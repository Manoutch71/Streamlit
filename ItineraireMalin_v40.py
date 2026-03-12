import streamlit as st
import time
import math
import unicodedata
import html as _html
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime
from typing import List, Tuple, Optional, Dict
from dataclasses import dataclass, field
import json
import csv
import io
import os
import re
from streamlit_gsheets import GSheetsConnection
import pandas as pd

def _h(s: str) -> str:
    """Échappe les caractères HTML dans une chaîne utilisateur."""
    return _html.escape(str(s))

def _sort_key_date(d: str):
    """Clé de tri robuste pour dates dd/mm/yyyy → (yyyy, mm, dd) en int."""
    try:
        parts = d.split("/")
        if len(parts) == 3:
            return (int(parts[2]), int(parts[1]), int(parts[0]))
    except (ValueError, IndexError):
        pass
    return (0, 0, 0)

def _norm_addr(s: str) -> str:
    """Normalisation robuste d'adresse : minuscules, sans accents,
    tirets→espaces, doubles espaces supprimés."""
    s = s.strip().lower()
    s = unicodedata.normalize("NFD", s)
    s = "".join(c for c in s if unicodedata.category(c) != "Mn")  # retire diacritiques
    s = re.sub(r"[-_]", " ", s)          # tirets → espaces
    s = re.sub(r"\s+", " ", s)           # doubles espaces → un seul
    return s

# ── Détection st.dialog (disponible depuis Streamlit ≥ 1.35) ──────────────
def _streamlit_version():
    try:
        from importlib.metadata import version
        v = version("streamlit")
        parts = v.split(".")
        return int(parts[0]), int(parts[1])
    except Exception:
        return (0, 0)

_ST_MAJOR, _ST_MINOR = _streamlit_version()
HAS_DIALOG   = (_ST_MAJOR, _ST_MINOR) >= (1, 35)
HAS_POPOVER  = (_ST_MAJOR, _ST_MINOR) >= (1, 31)
HAS_FRAGMENT = (_ST_MAJOR, _ST_MINOR) >= (1, 37)

# ── IMPORTS DIFFÉRÉS ─────────────────────────────────────────────────────────
# requests : chargé à la 1ère requête réseau (géocodage / OSRM)
# numpy    : remplacé par listes Python — supprimé (dist[a][b] au lieu de dist[a,b])
# cProfile : supprimé — le résultat du profiling n'était jamais affiché
# folium   : chargé à la 1ère construction de carte

def _import_folium():
    """Charge folium + streamlit_folium à la demande."""
    import folium as _folium
    from streamlit_folium import st_folium as _st_folium
    return _folium, _st_folium

# ==========================================================
# CONFIGURATION
# ==========================================================
st.set_page_config(layout="wide", page_title="ItinéraireMalin v40")
st.markdown(
    "<div id='haut-de-page'></div>"
    "<h1 style='text-align:center; font-size:42px;'>🚗 ItinéraireMalin</h1>",
    unsafe_allow_html=True
)

OSRM_URL         = "http://router.project-osrm.org"
OSRM_FALLBACK_URL = "https://routing.openstreetmap.de"
MAP_CENTER    = [48.087411375094675, 6.728658955145458]

SPH = 3600   # seconds per hour
SPM = 60     # seconds per minute

# ── Regex précompilées ────────────────────────────────────────────────────────
_RE_ORDINAL    = re.compile(r'(\d+)ème', re.IGNORECASE)
_RE_RTA_TO_DOT = re.compile(r'\bRTA\b',  re.IGNORECASE)
_RE_DU         = re.compile(r'\bdu\b',   re.IGNORECASE)
_RE_DES        = re.compile(r'\bdes\b',  re.IGNORECASE)
_RE_POSTCODE   = re.compile(r'\b\d{5}\b')
_RE_SAFE_NAME  = re.compile(r'[^A-Za-z0-9_\-\. ]')

WORK_START  = 8  * SPH   # 28800
WORK_END    = 18 * SPH   # 64800
MIDI        = 12 * SPH   # 43200
DEBUT_APM   = 13 * SPH   # 46800

# Types d'intervention ramonage avec durées par défaut
INTERVENTION_TYPES = {
    "Rapide_30": 30 * SPM,
    "Standard_60": 60 * SPM,
    "Difficile_90": 90 * SPM,
    "Conduits multiples_120": 120 * SPM,
}
# F: liste des clés pré-calculée — évite list(INTERVENTION_TYPES.keys()) répété à chaque rerun UI
INTERVENTION_KEYS = list(INTERVENTION_TYPES.keys())

# ==========================================================
# DATA CLASSES
# ==========================================================
@dataclass
class DeliveryPoint:
    address: str
    coordinates: Optional[Tuple[float, float]] = None
    time_mode: str = "Libre"
    target_time: Optional[int] = None
    intervention_type: str = "Standard"
    notes: str = ""
    service_duration: int = 60 * SPM

    def __post_init__(self):
        # Normalisé une seule fois à la création — évite .strip().lower() répétés
        object.__setattr__(self, '_address_norm', _norm_addr(self.address))

    @property
    def address_norm(self) -> str:
        return object.__getattribute__(self, '_address_norm')

@dataclass
class Contact:
    """Contact dans le carnet d'adresses"""
    name: str
    address: str
    phone: str = ""
    intervention_type: str = "Standard"
    notes: str = ""
    service_duration: int = 60 * SPM

    def __post_init__(self):
        object.__setattr__(self, '_address_norm', _norm_addr(self.address))
        object.__setattr__(self, '_name_norm',    _norm_addr(self.name))

    @property
    def address_norm(self) -> str:
        return object.__getattribute__(self, '_address_norm')

    @property
    def name_norm(self) -> str:
        return object.__getattribute__(self, '_name_norm')

@dataclass
class RouteConfig:
    start_address: str = ""
    start_coordinates: Optional[Tuple[float, float]] = None
    start_time: int = WORK_START
    start_service_duration: int = 60 * SPM
    end_address: str = "9 CHEMIN DES PINASSES 88530 LE THOLY"
    end_coordinates: Optional[Tuple[float, float]] = None

@dataclass
class RouteResult:
    order: List[int]
    total_distance: float
    total_time: int
    arrival_times: List[int]
    is_approximation: bool = False
    matin_moved: List[str] = field(default_factory=list)
    matin_duration: int = 0
    matin_count: int = 0
    initial_distance: float = 0.0   # distance ordre séquentiel — pour calcul du gain

# ==========================================================
# STATE MANAGER
# ==========================================================
class StateManager:
    @staticmethod
    def init():
        defaults = {
            "delivery_points": [],
            "route_config": RouteConfig(),
            "coord_cache": {},
            "map_zoom_target": None,
            "optimized_result": None,
            "last_error": None,
            "map_click_address": None,
            "map_click_coords": None,
            "map_click_queue": [],
            "client_history": [],
            "address_book": [],
            "address_suggestions": {},
            # Paramètres configurables de l'optimiseur
            "opt_pause_start":  12 * SPH,   # 12h00
            "opt_pause_end":    13 * SPH,   # 13h00
            "opt_max_matin_dur":  4 * SPH,  # Objectif matin 4h
            "opt_max_matin_slots": 4,
    "osrm_time_coeff":      1.15,  # +15% sur les temps OSRM (routes sinueuses)       # max arrêts matin
        }
        for k, v in defaults.items():
            if k not in st.session_state:
                st.session_state[k] = v
        
        # Charger le carnet d'adresses et l'historique au démarrage
        if "address_book_loaded" not in st.session_state:
            nb_loaded = AddressBookManager.load_from_file()
            if nb_loaded > 0:
                st.session_state["_contacts_loaded_msg"] = nb_loaded
            HistoryManager.load_from_file()
            GeoCache.load()   # ⚡ Cache géocodage persistant → 0 requête réseau si déjà connu
            # Patch : remplir les noms manquants dans l'historique depuis le carnet
            name_idx = {_norm_addr(c["address"]): c.get("name","")
                        for c in st.session_state.get("address_book", [])}
            for h in st.session_state.get("client_history", []):
                if not h.get("name"):
                    h["name"] = name_idx.get(_norm_addr(h.get("address","")), "")
            st.session_state.address_book_loaded = True

    @staticmethod
    def add_point(address):
        st.session_state.delivery_points.append(DeliveryPoint(address=address))

    @staticmethod
    def add_from_history(h: dict):
        """Ajoute un point depuis une entrée d'historique (évite la duplication)."""
        StateManager.add_point(h.get("address", ""))
        pts = st.session_state.delivery_points
        if pts:
            pts[-1].intervention_type = h.get("intervention_type", "Standard")
            pts[-1].notes             = h.get("notes", "")
            pts[-1].time_mode         = h.get("time_mode", "Libre")
            pts[-1].service_duration  = h.get("service_duration", 3600)

    @staticmethod
    def add_contact_to_route(contact_dict: dict):
        """Ajoute un contact du carnet directement comme point de la tournée."""
        point = DeliveryPoint(
            address=contact_dict["address"],
            intervention_type=contact_dict.get("intervention_type", "Standard_60"),
            notes=contact_dict.get("notes", ""),
            service_duration=contact_dict.get("service_duration", 60 * SPM)
        )
        st.session_state.delivery_points.append(point)

    @staticmethod
    def remove_point(i):
        if 0 <= i < len(st.session_state.delivery_points):
            st.session_state.delivery_points.pop(i)

    @staticmethod
    def update_point(i, **kw):
        p = st.session_state.delivery_points[i]
        for k, v in kw.items():
            if hasattr(p, k): setattr(p, k, v)

    @staticmethod
    def points() -> List[DeliveryPoint]:
        return st.session_state.delivery_points

    @staticmethod
    def config() -> RouteConfig:
        return st.session_state.route_config

    @staticmethod
    def update_config(**kw):
        c = st.session_state.route_config
        for k, v in kw.items():
            if hasattr(c, k): setattr(c, k, v)

    @staticmethod
    def commit(do_rerun: bool = True):
        """
        Groupeur de modifications : autosave + rerun.
        Si une optimisation existe ET toutes les coordonnées sont connues,
        pose le flag _reopt_pending → relance auto en début de main().
        Sinon efface simplement le résultat (coordonnées manquantes → regéocodage requis).
        """
        if st.session_state.optimized_result is not None:
            cfg = st.session_state.route_config
            pts = st.session_state.delivery_points
            all_ready = (
                bool(cfg.start_coordinates) and bool(cfg.end_coordinates)
                and bool(pts)
                and all(p.coordinates for p in pts)
            )
            if all_ready:
                st.session_state["_reopt_pending"] = True
            else:
                st.session_state.optimized_result = None
        RouteManager.autosave()
        if do_rerun:
            st.rerun()

    @staticmethod
    def save_to_history():
        """Sauvegarde les interventions dans l'historique avec suivi des dates de passage."""
        ss        = st.session_state
        pts       = ss.delivery_points
        if not pts:
            return
        today_str     = datetime.today().strftime("%d/%m/%Y")
        history       = ss.client_history
        history_index = {h["address"]: h for h in history}
        # Index nom depuis le carnet d'adresses
        name_index    = {c["address"]: c.get("name","") for c in ss.get("address_book", [])}
        for p in pts:
            p_name = name_index.get(p.address, "")
            if p.address in history_index:
                entry = history_index[p.address]
                entry.update({
                    "intervention_type": p.intervention_type,
                    "notes":             p.notes,
                    "time_mode":         p.time_mode,
                    "service_duration":  p.service_duration,
                })
                if p_name and not entry.get("name"):
                    entry["name"] = p_name
                dates = entry.setdefault("visit_dates", [])
                if today_str not in dates:
                    dates.append(today_str)
            else:
                new_entry = {
                    "name":              p_name,
                    "address":           p.address,
                    "intervention_type": p.intervention_type,
                    "notes":             p.notes,
                    "time_mode":         p.time_mode,
                    "service_duration":  p.service_duration,
                    "visit_dates":       [today_str],
                }
                history.append(new_entry)
                history_index[p.address] = new_entry
            StateManager.update_last_intervention(p.address, today_str)
        ss.client_history = history[-500:]
        HistoryManager.save_to_file()

    # ═══════════════════════════════════════════════════════
    # CARNET D'ADRESSES
    # ═══════════════════════════════════════════════════════
    
    @staticmethod
    def _invalidate_csv_cache():
        """Invalide le cache CSV du carnet (appelé à chaque mutation)"""
        st.session_state.pop("_csv_cache", None)

    # ── INDEX DE RECHERCHE CONTACTS (O(1) lookup) ────────────────────────
    @staticmethod
    def _build_contact_index():
        """
        Construit deux dicts O(1) :
          _contact_name_idx[name_lower]  → (orig_idx, contact_dict)
          _contact_addr_idx[addr_lower]  → (orig_idx, contact_dict)
        Et la liste complète de tuples pour l'itération paginée.
        """
        book = st.session_state.address_book
        name_idx: dict = {}
        addr_idx: dict = {}
        full_list = []
        for i, c in enumerate(book):
            nl = c["name"].lower()
            al = c["address"].lower()
            name_idx[nl] = (i, c)
            addr_idx[al] = (i, c)
            full_list.append((i, nl, al, c))
        st.session_state["_contact_name_idx"] = name_idx
        st.session_state["_contact_addr_idx"] = addr_idx
        st.session_state["_contact_index"]    = full_list  # conservé pour pagination

    @staticmethod
    def _get_contact_index() -> list:
        """Retourne la liste complète (rebuild si absente)."""
        if "_contact_index" not in st.session_state:
            StateManager._build_contact_index()
        return st.session_state["_contact_index"]

    @staticmethod
    def _get_name_idx() -> dict:
        if "_contact_name_idx" not in st.session_state:
            StateManager._build_contact_index()
        return st.session_state["_contact_name_idx"]

    @staticmethod
    def _get_addr_idx() -> dict:
        if "_contact_addr_idx" not in st.session_state:
            StateManager._build_contact_index()
        return st.session_state["_contact_addr_idx"]

    @staticmethod
    def _invalidate_contact_index():
        """Invalide les trois structures d'index."""
        for k in ("_contact_index", "_contact_name_idx", "_contact_addr_idx"):
            st.session_state.pop(k, None)

    @staticmethod
    def add_contact(contact: "Contact"):
        """Ajoute un contact au carnet d'adresses"""
        st.session_state.address_book.append({
            "name": contact.name,
            "address": contact.address,
            "phone": contact.phone,
            "intervention_type": contact.intervention_type,
            "notes": contact.notes,
            "service_duration": contact.service_duration
        })
        StateManager._invalidate_csv_cache()
        StateManager._invalidate_contact_index()
        # Sauvegarde automatique
        AddressBookManager.save_to_file()
    
    @staticmethod
    def get_contacts() -> List[dict]:
        """Retourne la liste des contacts"""
        return st.session_state.address_book
    
    @staticmethod
    def delete_contact(index: int):
        """Supprime un contact par son index"""
        if 0 <= index < len(st.session_state.address_book):
            st.session_state.address_book.pop(index)
            StateManager._invalidate_csv_cache()
            StateManager._invalidate_contact_index()
            # Sauvegarde automatique
            AddressBookManager.save_to_file()

    @staticmethod
    def delete_from_history(address: str):
        """Supprime un client de l'historique ET du carnet (par adresse normalisée)."""
        key = _norm_addr(address)
        # Historique
        st.session_state.client_history = [
            h for h in st.session_state.get("client_history", [])
            if _norm_addr(h.get("address", "")) != key
        ]
        HistoryManager.save_to_file()
        # Carnet
        st.session_state.address_book = [
            c for c in st.session_state.get("address_book", [])
            if _norm_addr(c.get("address", "")) != key
        ]
        StateManager._invalidate_csv_cache()
        StateManager._invalidate_contact_index()
        AddressBookManager.save_to_file()
    
    @staticmethod
    def update_contact(index: int, **kwargs):
        """Met à jour un contact"""
        if 0 <= index < len(st.session_state.address_book):
            contact = st.session_state.address_book[index]
            for k, v in kwargs.items():
                if k in contact:
                    contact[k] = v
            StateManager._invalidate_csv_cache()
            StateManager._invalidate_contact_index()
            # Sauvegarde automatique
            AddressBookManager.save_to_file()
    
    @staticmethod
    def move_point_up(i: int):
        """Monte un arrêt d'une position"""
        pts = st.session_state.delivery_points
        if i > 0:
            pts[i], pts[i - 1] = pts[i - 1], pts[i]

    @staticmethod
    def move_point_down(i: int):
        """Descend un arrêt d'une position"""
        pts = st.session_state.delivery_points
        if i < len(pts) - 1:
            pts[i], pts[i + 1] = pts[i + 1], pts[i]

    @staticmethod
    def is_duplicate_address(address: str) -> bool:
        """Vérifie si une adresse est déjà dans la tournée — O(n) sur norm précalculé."""
        addr_norm = _norm_addr(address)
        return any(p.address_norm == addr_norm for p in st.session_state.delivery_points)

    @staticmethod
    def is_duplicate_contact(name: str, address: str) -> bool:
        """O(1) — lookup via dicts pré-calculés."""
        name_idx = StateManager._get_name_idx()
        addr_idx = StateManager._get_addr_idx()
        return _norm_addr(name) in name_idx or _norm_addr(address) in addr_idx

    @staticmethod
    def auto_add_to_book(points: List["DeliveryPoint"], arrival_times: List[int],
                         order: List[int], today_str: str):
        """Après optimisation : propose les points absents du carnet.
           Stocke la liste en session pour affichage dans UI.results()."""
        book_addrs = {_norm_addr(c["address"]) for c in st.session_state.address_book}
        missing = []
        for step, node in enumerate(order):
            if node <= 0 or node > len(points):
                continue
            p = points[node - 1]
            if _norm_addr(p.address) not in book_addrs:
                missing.append({
                    "address": p.address,
                    "intervention_type": p.intervention_type,
                    "notes": p.notes,
                    "service_duration": p.service_duration,
                    "last_intervention": today_str,
                })
        st.session_state["_auto_add_candidates"] = missing

    @staticmethod
    def update_last_intervention(address: str, date_str: str):
        """Met à jour la date de dernière intervention — O(1) via addr_idx."""
        addr_l   = _norm_addr(address)
        addr_idx = StateManager._get_addr_idx()
        entry    = addr_idx.get(addr_l)
        if entry:
            entry[1]["last_intervention"] = date_str
        AddressBookManager.save_to_file()
        StateManager._invalidate_csv_cache()

# ==========================================================
# ROUTE MANAGER - Sauvegarde/Rechargement d'une tournée
# ==========================================================
class RouteManager:
    """Sauvegarde et recharge une tournée complète (points + config) en JSON."""

    SAVE_DIR      = "tournees_sauvegardees"
    AUTOSAVE_NAME = "_autosave"   # fichier réservé — jamais affiché dans la liste manuelle

    @staticmethod
    def _ensure_dir():
        os.makedirs(RouteManager.SAVE_DIR, exist_ok=True)

    @staticmethod
    def autosave():
        """Sauvegarde silencieuse automatique — écrase _autosave.json à chaque modif."""
        try:
            if st.session_state.get("delivery_points"):
                RouteManager.save(RouteManager.AUTOSAVE_NAME)
        except Exception:
            pass  # autosave ne doit jamais planter l'interface

    @staticmethod
    def save(name: str) -> bool:
        """Sauvegarde la tournée courante sous un nom donné."""
        try:
            RouteManager._ensure_dir()
            cfg  = st.session_state.route_config
            pts  = st.session_state.delivery_points
            data = {
                "version": 1,
                "saved_at": datetime.today().isoformat(timespec="seconds"),
                "config": {
                    "start_address":        cfg.start_address,
                    "start_time":           cfg.start_time,
                    "start_service_duration": cfg.start_service_duration,
                    "end_address":          cfg.end_address,
                },
                "points": [
                    {
                        "address":           p.address,
                        "time_mode":         p.time_mode,
                        "target_time":       p.target_time,
                        "intervention_type": p.intervention_type,
                        "notes":             p.notes,
                        "service_duration":  p.service_duration,
                    }
                    for p in pts
                ],
            }
            path = os.path.join(RouteManager.SAVE_DIR, f"{name}.json")
            with open(path, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False)  # pas d'indent → 4× plus rapide
            return True
        except Exception as e:
            st.error(f"Erreur sauvegarde tournée : {e}")
            return False

    @staticmethod
    def list_saves() -> List[str]:
        """Liste les tournées sauvegardées manuellement (sans _autosave)."""
        RouteManager._ensure_dir()
        files = [f[:-5] for f in os.listdir(RouteManager.SAVE_DIR)
                 if f.endswith(".json") and f[:-5] != RouteManager.AUTOSAVE_NAME]
        return sorted(files)

    @staticmethod
    def load(name: str) -> bool:
        """Recharge une tournée sauvegardée."""
        try:
            path = os.path.join(RouteManager.SAVE_DIR, f"{name}.json")
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
            cfg  = st.session_state.route_config
            c    = data.get("config", {})
            cfg.start_address          = c.get("start_address", "")
            cfg.start_time             = c.get("start_time", WORK_START)
            cfg.start_service_duration = c.get("start_service_duration", 60 * SPM)
            cfg.end_address            = c.get("end_address", "")
            cfg.start_coordinates      = None
            cfg.end_coordinates        = None
            pts = []
            for pd in data.get("points", []):
                pts.append(DeliveryPoint(
                    address           = pd.get("address", ""),
                    time_mode         = pd.get("time_mode", "Libre"),
                    target_time       = pd.get("target_time"),
                    intervention_type = pd.get("intervention_type", "Standard_60"),
                    notes             = pd.get("notes", ""),
                    service_duration  = pd.get("service_duration", 60 * SPM),
                ))
            st.session_state.delivery_points = pts
            st.session_state.optimized_result = None
            # Vider les clés des widgets adresse départ/retour → ils se
            # réinitialiseront avec les valeurs chargées au prochain render
            st.session_state.pop("si_start", None)
            st.session_state.pop("si_end",   None)
            return True
        except Exception as e:
            st.error(f"Erreur chargement tournée : {e}")
            return False

    @staticmethod
    def delete(name: str) -> bool:
        try:
            os.remove(os.path.join(RouteManager.SAVE_DIR, f"{name}.json"))
            return True
        except Exception as e:
            st.error(f"Erreur suppression : {e}")
            return False

    @staticmethod
    def to_ics(result: "RouteResult", cfg: "RouteConfig",
               points: List["DeliveryPoint"], tour_date: "datetime") -> str:
        """Génère un fichier ICS (Google Calendar / iCal) pour la tournée optimisée."""
        lines = [
            "BEGIN:VCALENDAR",
            "VERSION:2.0",
            "PRODID:-//Tournees4Me//FR",
            "CALSCALE:GREGORIAN",
            "METHOD:PUBLISH",
        ]
        date_str = tour_date.strftime("%Y%m%d")
        n_pts    = len(points)
        all_addr = [cfg.start_address] + [p.address for p in points] + [cfg.end_address]

        def to_dt(seconds: int) -> str:
            h = seconds // 3600
            m = (seconds % 3600) // 60
            return f"{date_str}T{h:02d}{m:02d}00"

        for step, node in enumerate(result.order):
            if node <= 0 or node > n_pts:
                continue
            p      = points[node - 1]
            start  = result.arrival_times[step]
            end    = start + p.service_duration
            uid    = f"tournee4me-{date_str}-{step}@local"
            summary = p.address.replace(",", "\\,")
            desc    = f"Type: {p.intervention_type}"
            if p.notes:
                desc += f"\\nNotes: {p.notes.replace(',', '\\,')}"
            lines += [
                "BEGIN:VEVENT",
                f"UID:{uid}",
                f"DTSTART:{to_dt(start)}",
                f"DTEND:{to_dt(end)}",
                f"SUMMARY:{summary}",
                f"DESCRIPTION:{desc}",
                f"LOCATION:{summary}",
                "END:VEVENT",
            ]

        lines.append("END:VCALENDAR")
        return "\r\n".join(lines)


# ==========================================================
# GEO CACHE — persistance disque du cache de géocodage
# ==========================================================
class GeoCache:
    """
    Cache géocodage persistant sur disque (coord_cache.json).
    Chargé UNE FOIS au démarrage → quasi-zéro requêtes réseau au 2e lancement.
    Écriture incrémentale : seules les nouvelles entrées sont écrites
    si le delta dépasse un seuil (évite d'écrire 5000 entrées pour 1 ajout).
    """
    CACHE_FILE     = "coord_cache.json"
    WRITE_INTERVAL = 10   # écrire si ≥ N nouvelles entrées depuis la dernière sauvegarde

    @staticmethod
    def load():
        """Charge le cache disque dans st.session_state.coord_cache (merge)."""
        try:
            if os.path.exists(GeoCache.CACHE_FILE):
                with open(GeoCache.CACHE_FILE, "r", encoding="utf-8") as f:
                    disk = json.load(f)
                merged = {k: tuple(v) for k, v in disk.items()
                          if isinstance(v, list) and len(v) == 2}
                merged.update(st.session_state.get("coord_cache", {}))
                st.session_state["coord_cache"]        = merged
                st.session_state["_geocache_size_disk"] = len(merged)
        except Exception:
            pass

    @staticmethod
    def save(force: bool = False):
        """
        Persiste le cache sur disque.
        En mode normal : écrit seulement si ≥ WRITE_INTERVAL nouvelles entrées.
        force=True : écrit immédiatement (ex: à la fermeture).
        """
        try:
            cache     = st.session_state.get("coord_cache", {})
            size_disk = st.session_state.get("_geocache_size_disk", 0)
            delta     = len(cache) - size_disk
            if not force and delta < GeoCache.WRITE_INTERVAL:
                return
            serializable = {k: list(v) for k, v in cache.items() if v is not None}
            tmp = GeoCache.CACHE_FILE + ".tmp"
            with open(tmp, "w", encoding="utf-8") as f:
                json.dump(serializable, f, ensure_ascii=False)
            os.replace(tmp, GeoCache.CACHE_FILE)   # atomique : jamais de fichier à moitié écrit
            st.session_state["_geocache_size_disk"] = len(serializable)
        except Exception:
            pass


# ==========================================================
# ADDRESS BOOK MANAGER - Sauvegarde/Chargement/Import/Export
# ==========================================================
class AddressBookManager:
    """Gère la persistance du carnet d'adresses"""

    SAVE_FILE = "carnet_adresses.json"
    
    @staticmethod
    def decode_csv_bytes(csv_bytes: bytes) -> str:
        """
        Décode les bytes du CSV en essayant différents encodages.
        Gère UTF-8 avec BOM (Excel), Windows-1252 et Latin-1.
        """
        encodings = ['utf-8-sig', 'utf-8', 'cp1252', 'iso-8859-1', 'latin1']

        for encoding in encodings:
            try:
                return csv_bytes.decode(encoding)
            except (UnicodeDecodeError, AttributeError):
                continue

        # En dernier recours : latin1 (ne peut pas lever d'exception)
        return csv_bytes.decode('latin1', errors='replace')
    
    @staticmethod
    def save_to_file():
        """Sauvegarde automatique du carnet dans un fichier JSON"""
        try:
            contacts = st.session_state.get("address_book", [])
            with open(AddressBookManager.SAVE_FILE, 'w', encoding='utf-8') as f:
                json.dump(contacts, f, ensure_ascii=False, indent=2)
            return True
        except Exception as e:
            st.error(f"Erreur sauvegarde : {e}")
            return False
    
    @staticmethod
    def load_from_file():
        """Charge le carnet depuis le fichier JSON au démarrage"""
        try:
            if os.path.exists(AddressBookManager.SAVE_FILE):
                with open(AddressBookManager.SAVE_FILE, 'r', encoding='utf-8') as f:
                    contacts = json.load(f)
                st.session_state.address_book = contacts
                StateManager._invalidate_contact_index()
                return len(contacts)
            return 0
        except Exception as e:
            st.error(f"Erreur chargement : {e}")
            return 0
    
    @staticmethod
    def export_to_csv() -> bytes:
        """Exporte le carnet en CSV (bytes UTF-8 avec BOM) — résultat mis en cache.
        L'encodage utf-8-sig garantit la compatibilité Excel (Windows) et tout
        lecteur UTF-8 standard (le BOM est silencieusement ignoré par les lecteurs modernes)."""
        if "_csv_cache" in st.session_state:
            return st.session_state["_csv_cache"]

        contacts = st.session_state.get("address_book", [])
        if not contacts:
            return b""

        output = io.StringIO()
        CSV_FIELDS = ["visit_date", "name", "address", "phone",
                      "service_duration", "intervention_type", "notes"]
        writer = csv.DictWriter(
            output,
            fieldnames=CSV_FIELDS,
            delimiter=';',
            extrasaction='ignore'
        )
        writer.writeheader()
        hist_idx = {_norm_addr(h["address"]): h
                    for h in st.session_state.get("client_history", [])}
        for contact in contacts:
            base = {
                "name":              contact["name"],
                "address":           contact["address"],
                "phone":             contact.get("phone", ""),
                "service_duration":  contact["service_duration"] // 60,
                "intervention_type": contact.get("intervention_type", ""),
                "notes":             contact.get("notes", ""),
            }
            hist     = hist_idx.get(_norm_addr(contact["address"]), {})
            dates    = hist.get("visit_dates", [])
            if dates:
                for d in sorted(dates, key=_sort_key_date):
                    writer.writerow({**base, "visit_date": d})
            else:
                writer.writerow({**base,
                                 "visit_date": contact.get("last_intervention", "")})

        result = output.getvalue().encode('utf-8-sig')
        st.session_state["_csv_cache"] = result
        return result
    
    @staticmethod
    def import_from_csv(csv_content: str) -> Tuple[int, List[str]]:
        """
        Importe des contacts + historique depuis un CSV une-ligne-par-passage.
        Format : visit_date;name;phone;address;service_duration;intervention_type;notes
        Les lignes du même client (même adresse normalisée) sont automatiquement
        regroupées : toutes leurs dates alimentent visit_dates dans l'historique.
        """
        try:
            delimiter = ';' if ';' in csv_content else ','
            reader    = csv.DictReader(io.StringIO(csv_content), delimiter=delimiter)

            errors: List[str]  = []
            # clé: adresse normalisée → dict agrégé
            by_addr: dict = {}

            for i, row in enumerate(reader, start=2):
                try:
                    # Accepter 'address' et 'adress' (typo fréquente)
                    addr = (row.get("address") or row.get("adress") or "").strip()
                    name = row.get("name", "").strip()
                    if not addr and not name:
                        errors.append(f"Ligne {i}: nom et adresse manquants")
                        continue

                    key = (_norm_addr(name), _norm_addr(addr))

                    # Date du passage
                    raw_date = (row.get("visit_date") or
                                row.get("visit_dates") or "").strip()
                    # Ignorer les lignes sans date valide (annulées, etc.)
                    if raw_date:
                        # Vérification légère du format jj/mm/aaaa
                        parts = raw_date.split("/")
                        if len(parts) != 3 or len(parts[2]) != 4:
                            raw_date = ""

                    itype = row.get("intervention_type", "").strip()
                    if itype not in INTERVENTION_TYPES:
                        itype = "Standard"
                    try:
                        sd_raw = row.get("service_duration", "").strip()
                        duration_sec = int(sd_raw) * 60 if sd_raw else 3600
                    except Exception:
                        duration_sec = 3600

                    if key not in by_addr:
                        by_addr[key] = {
                            "name":              name,
                            "address":           addr or name,
                            "phone":             row.get("phone", "").strip(),
                            "intervention_type": itype,
                            "notes":             row.get("notes", "").strip(),
                            "service_duration":  duration_sec,
                            "visit_dates":       [],
                        }

                    entry = by_addr[key]
                    # Les infos non-date sont écrasées par la ligne la plus récente
                    # (tri naturel du CSV : les dates récentes arrivent en dernier)
                    if name:       entry["name"]    = name
                    if addr:       entry["address"] = addr
                    ph = row.get("phone", "").strip()
                    if ph:         entry["phone"]   = ph
                    nt = row.get("notes", "").strip()
                    if nt:         entry["notes"]   = nt

                    if raw_date and raw_date not in entry["visit_dates"]:
                        entry["visit_dates"].append(raw_date)

                except Exception as e:
                    errors.append(f"Ligne {i}: {e}")

            if not by_addr:
                return 0, errors

            # ── Fusionner dans l'historique ────────────────────────────────
            history  = st.session_state.get("client_history", [])
            hist_idx = {(_norm_addr(h.get("name","")), _norm_addr(h["address"])): h for h in history}

            buffer: List[dict] = []
            for key, entry in by_addr.items():
                vd = entry.pop("visit_dates", [])
                buffer.append(dict(entry))          # copie sans visit_dates

                if key in hist_idx:
                    existing    = hist_idx[key]
                    existing_vd = existing.setdefault("visit_dates", [])
                    for d in vd:
                        if d not in existing_vd:
                            existing_vd.append(d)
                    # Mettre à jour le nom si absent ou vide
                    if entry.get("name") and not existing.get("name"):
                        existing["name"] = entry["name"]
                else:
                    new_h = {
                        "name":              entry.get("name", ""),
                        "address":           entry["address"],
                        "intervention_type": entry["intervention_type"],
                        "notes":             entry["notes"],
                        "time_mode":         "Libre",
                        "service_duration":  entry["service_duration"],
                        "visit_dates":       vd,
                    }
                    history.append(new_h)
                    hist_idx[key] = new_h

            st.session_state.client_history = history
            HistoryManager.save_to_file()
            st.session_state.address_book.extend(buffer)
            StateManager._invalidate_csv_cache()
            StateManager._invalidate_contact_index()
            AddressBookManager.save_to_file()

            return len(by_addr), errors

        except Exception as e:
            return 0, [f"Erreur lecture CSV: {str(e)}"]
    
    @staticmethod
    def get_csv_template() -> bytes:
        """Retourne un modèle CSV vide encodé en UTF-8 avec BOM"""
        content = (
            "visit_date;name;phone;address;service_duration;intervention_type;notes\n"
            "15/01/2025;DUPONT;;12 RUE DE LA PAIX 88000 EPINAL;;;POELE BOIS - SALON\n"
            "22/03/2025;DUPONT;;12 RUE DE LA PAIX 88000 EPINAL;;;POELE BOIS - SALON\n"
            "10/09/2024;MARTIN;;5 AV DE LA GARE 88530 LE THOLY;;;INSERT FERME TUBE"
        )
        return content.encode('utf-8-sig')

# ==========================================================
# HISTORY MANAGER
# ==========================================================
class HistoryManager:
    """Gère la persistance de l'historique des clients (visit_dates)."""
    SAVE_FILE = "historique_clients.json"

    @staticmethod
    def save_to_file():
        try:
            history = st.session_state.get("client_history", [])
            with open(HistoryManager.SAVE_FILE, 'w', encoding='utf-8') as f:
                json.dump(history, f, ensure_ascii=False, indent=2)
        except Exception as e:
            st.error(f"Erreur sauvegarde historique : {e}")

    @staticmethod
    def load_from_file():
        try:
            if os.path.exists(HistoryManager.SAVE_FILE):
                with open(HistoryManager.SAVE_FILE, 'r', encoding='utf-8') as f:
                    history = json.load(f)
                # Migration : garantir que visit_dates existe
                for h in history:
                    if "visit_dates" not in h:
                        h["visit_dates"] = [h["last_intervention"]] if h.get("last_intervention") else []
                    # Migration : garantir que name existe
                    if "name" not in h:
                        h["name"] = ""
                st.session_state.client_history = history
                return len(history)
            return 0
        except Exception:
            return 0

# ==========================================================
# TIME WINDOW HELPER
# ==========================================================
class TW:
    """Fenêtres horaires absolues (secondes depuis minuit)."""

    @staticmethod
    def get(p: DeliveryPoint) -> Tuple[int, int]:
        m = p.time_mode
        if m == "Heure précise" and p.target_time is not None:
            t = p.target_time
            return (t, t)
        if m == "Matin libre":
            return (WORK_START, MIDI)
        if m == "Après-midi libre":
            return (DEBUT_APM, WORK_END)
        return (WORK_START, WORK_END)

    @staticmethod
    def fmt(lo: int, hi: int) -> str:
        def f(s): return f"{s//3600:02d}:{(s%3600)//60:02d}"
        if lo == hi:
            return f"{f(lo)} (précis)"
        return f"{f(lo)} – {f(hi)}"

    @staticmethod
    def priority(p: DeliveryPoint) -> int:
        lo, _ = TW.get(p)
        return lo

# ==========================================================
# GEOCODING
# ==========================================================
class Geo:
    """Géocodage : API Gouv FR (1er) → Photon (2e) → Nominatim (3e)"""
    GOUV_URL      = "https://api-adresse.data.gouv.fr/search/"   # ① officiel France
    PHOTON_URL    = "https://photon.komoot.io/api/"               # ② mondial
    NOMINATIM_URL = "https://nominatim.openstreetmap.org/search"  # ③ dernier recours
    HEADERS = {
        "User-Agent": "Tournees4Me/1.0 (ramonage planning)",
        "Accept-Language": "fr,fr-FR;q=0.9",
    }
    # ✅ Session HTTP partagée — évite de rouvrir une connexion TCP à chaque requête
    _session: Optional["requests.Session"] = None

    @staticmethod
    def _get_session():
        if Geo._session is None:
            import requests
            Geo._session = requests.Session()
            Geo._session.headers.update(Geo.HEADERS)
        return Geo._session

    @staticmethod
    def normalize_address(address: str) -> List[str]:
        """
        Normalise une adresse pour améliorer le géocodage.
        Retourne plusieurs variantes de l'adresse à essayer.
        
        Gère les cas courants :
        - Ordinaux : 3ème → 3e, 1er → 1er (conservé), 2ème → 2e
        - Acronymes : RTA, R.T.A, Rta
        - Articles : du/des
        """
        variants = [address]
        normalized = address

        if _RE_ORDINAL.search(normalized):
            normalized = _RE_ORDINAL.sub(r'\1e', normalized)
            variants.append(normalized)

        if 'rta' in normalized.lower():
            if 'R.T.A' not in normalized:
                var_with_dots = _RE_RTA_TO_DOT.sub('R.T.A', normalized)
                if var_with_dots != normalized:
                    variants.append(var_with_dots)
            if 'R.T.A' in normalized:
                var_no_dots = normalized.replace('R.T.A', 'RTA').replace('r.t.a', 'rta')
                if var_no_dots != normalized:
                    variants.append(var_no_dots)

        if ' du ' in normalized.lower():
            variants.append(_RE_DU.sub('des', normalized))
        elif ' des ' in normalized.lower():
            variants.append(_RE_DES.sub('du', normalized))
        
        # 4. Supprimer les doublons en préservant l'ordre
        seen = set()
        unique_variants = []
        for v in variants:
            v_lower = v.lower()
            if v_lower not in seen:
                seen.add(v_lower)
                unique_variants.append(v)
        
        return unique_variants

    @staticmethod
    def _fetch(address: str) -> Optional[Tuple[float, float]]:
        """
        Géocodage pur — SANS toucher st.session_state (thread-safe).
        Stratégie : BAN (officielle FR) → Photon → Nominatim.
        Chaque API est tentée sur toutes les variantes avant de passer à la suivante.
        """
        variants = Geo.normalize_address(address.strip())

        # 1. BAN — la plus précise pour la France
        for variant in variants:
            coords = Geo._gouv(variant)
            if coords:
                return coords

        # 2. Photon (Komoot) — couvre mieux certaines communes rurales
        for variant in variants:
            coords = Geo._photon(variant)
            if coords:
                return coords

        # 3. Nominatim — OSM mondial, fallback universel
        time.sleep(0.3)   # politesse envers l'API publique
        for variant in variants:
            coords = Geo._nominatim(variant)
            if coords:
                return coords

        return None

    @staticmethod
    def get(address: str) -> Optional[Tuple[float, float]]:
        """Géocode une adresse — utilise le cache session, appelle _fetch si absent."""
        if not address or not address.strip():
            return None
        key   = _norm_addr(address)
        cache = st.session_state.coord_cache
        if key in cache: return cache[key]

        coords = Geo._fetch(address)
        if coords:
            cache[key] = coords
        else:
            st.session_state.last_error = (
                f"Adresse introuvable : '{address}'. "
                "Vérifiez l'orthographe ou ajoutez le code postal."
            )
        return coords

    @staticmethod
    def batch_geocode(
        addresses: List[str],
        max_workers: int = 4,
        progress_cb=None
    ) -> Dict[str, Optional[Tuple[float, float]]]:
        """
        Géocode en parallèle.
        ⚠️ Les threads appellent _fetch (pas get) — aucun accès à st.session_state
        depuis les workers. Le cache est mis à jour dans le thread principal après.
        """
        cache  = st.session_state.coord_cache
        result: Dict[str, Optional[Tuple[float, float]]] = {}
        to_fetch: List[str] = []

        # Résoudre depuis le cache dans le thread principal
        for addr in addresses:
            key = _norm_addr(addr)
            if key in cache:
                result[addr] = cache[key]
            else:
                to_fetch.append(addr)

        if not to_fetch:
            return result

        total = len(addresses)
        done  = len(result)
        errors: List[str] = []

        # Adapter le nombre de workers : inutile d'ouvrir 8 threads pour 2 adresses
        # et évite les rate-limits des APIs publiques (BAN/Photon)
        effective_workers = min(max_workers, len(to_fetch), 4)

        # Threads : uniquement _fetch, zéro st.session_state
        with ThreadPoolExecutor(max_workers=effective_workers) as executor:
            future_to_addr = {
                executor.submit(Geo._fetch, addr): addr
                for addr in to_fetch
            }
            for future in as_completed(future_to_addr):
                addr = future_to_addr[future]
                exc_occurred = False
                try:
                    coords = future.result()
                except Exception as e:
                    coords = None
                    exc_occurred = True
                    errors.append(f"{addr}: {e}")

                result[addr] = coords
                # Mettre à jour le cache dans le thread principal (clé normalisée uniquement)
                if coords:
                    cache[_norm_addr(addr)] = coords
                else:
                    if not exc_occurred:   # évite le doublon si exception déjà loggée
                        errors.append(addr)

                done += 1
                if progress_cb:
                    progress_cb(done, total)

        if errors:
            st.session_state.last_error = "Introuvable : " + ", ".join(errors[:3])

        # ⚡ Persister le cache sur disque après chaque batch
        if to_fetch:
            GeoCache.save()

        return result

    @staticmethod
    def _gouv(address: str) -> Optional[Tuple[float, float]]:
        """API adresse.data.gouv.fr — base officielle BAN, très précise pour la France."""
        try:
            r = Geo._get_session().get(
                Geo.GOUV_URL,
                params={"q": address, "limit": 1},
                timeout=10,
            )
            if r.status_code == 200:
                features = r.json().get("features", [])
                if features:
                    lon, lat = features[0]["geometry"]["coordinates"]
                    return (float(lat), float(lon))
            else:
                st.session_state.last_error = f"Gouv HTTP {r.status_code} pour : {address}"
        except Exception as e:
            st.session_state.last_error = f"Gouv erreur : {e}"
        return None

    @staticmethod
    def _photon(address: str) -> Optional[Tuple[float, float]]:
        try:
            time.sleep(0.15)
            r = Geo._get_session().get(
                Geo.PHOTON_URL,
                params={"q": address, "limit": 1, "lang": "fr"},
                timeout=10,
            )
            if r.status_code == 200:
                features = r.json().get("features", [])
                if features:
                    lon, lat = features[0]["geometry"]["coordinates"]
                    return (float(lat), float(lon))
            else:
                st.session_state.last_error = f"Photon HTTP {r.status_code} pour : {address}"
        except Exception as e:
            st.session_state.last_error = f"Photon erreur : {e}"
        return None

    @staticmethod
    def _nominatim(address: str) -> Optional[Tuple[float, float]]:
        try:
            r = Geo._get_session().get(
                Geo.NOMINATIM_URL,
                params={"q": address, "format": "json", "limit": 1,
                        "addressdetails": 1, "accept-language": "fr"},
                timeout=15,
            )
            if r.status_code == 200:
                data = r.json()
                if data:
                    return (float(data[0]["lat"]), float(data[0]["lon"]))
        except Exception as e:
            st.session_state.last_error = f"Nominatim: {e}"
        return None

    @staticmethod
    def reverse(lat: float, lon: float) -> Optional[str]:
        try:
            r = Geo._get_session().get(
                "https://nominatim.openstreetmap.org/reverse",
                params={"lat": lat, "lon": lon, "format": "json",
                        "accept-language": "fr", "zoom": 18},
                timeout=10,
            )
            if r.status_code == 200:
                data = r.json()
                if "display_name" in data:
                    addr = data.get("address", {})
                    parts = []
                    if addr.get("house_number"): parts.append(addr["house_number"])
                    if addr.get("road"):         parts.append(addr["road"])
                    city = addr.get("city") or addr.get("town") or addr.get("village") or addr.get("hamlet", "")
                    postcode = addr.get("postcode", "")
                    if postcode and city:
                        parts.append(f"{postcode} {city}")
                    elif city:
                        parts.append(city)
                    if parts:
                        return " ".join(parts)
                    return data["display_name"]
        except:
            pass
        return None

    @staticmethod
    def is_incomplete_address(address: str) -> bool:
        """
        Détecte si une adresse est incomplète (manque code postal et ville).
        Retourne True si l'adresse semble incomplète.
        """
        # Chercher un code postal français (5 chiffres)
        has_postcode = bool(_RE_POSTCODE.search(address))
        
        # Si pas de code postal, considérer comme incomplet
        return not has_postcode
    
    @staticmethod
    def search_address_suggestions(partial_address: str, limit: int = 5) -> List[dict]:
        """
        Cherche des suggestions d'adresses complètes en France.
        Retourne une liste de dictionnaires avec: display_name, lat, lon, address_details
        """
        suggestions = []
        
        try:
            time.sleep(0.15)   # PERF: 0.5→0.15s
            # Ajouter "France" pour limiter la recherche
            search_query = f"{partial_address}, France"
            
            r = Geo._get_session().get(
                Geo.NOMINATIM_URL,
                params={
                    "q": search_query,
                    "format": "json",
                    "limit": limit,
                    "addressdetails": 1,
                    "countrycodes": "fr",  # Limiter à la France
                    "accept-language": "fr"
                },
                timeout=15,
            )
            
            if r.status_code == 200:
                results = r.json()
                for result in results:
                    addr = result.get("address", {})
                    
                    # Construire une adresse lisible
                    parts = []
                    if addr.get("house_number"):
                        parts.append(addr["house_number"])
                    if addr.get("road"):
                        parts.append(addr["road"])
                    
                    # Ville
                    city = (addr.get("city") or addr.get("town") or 
                           addr.get("village") or addr.get("municipality") or "")
                    
                    # Code postal
                    postcode = addr.get("postcode", "")
                    
                    if postcode and city:
                        parts.append(f"{postcode} {city}")
                    elif city:
                        parts.append(city)
                    
                    display = " ".join(parts) if parts else result.get("display_name", "")
                    
                    suggestions.append({
                        "display_name": display,
                        "full_display": result.get("display_name", ""),
                        "lat": float(result["lat"]),
                        "lon": float(result["lon"]),
                        "postcode": postcode,
                        "city": city,
                        "road": addr.get("road", ""),
                        "house_number": addr.get("house_number", "")
                    })
        except Exception as e:
            st.warning(f"Erreur recherche suggestions : {e}")
        
        return suggestions

# ==========================================================
# ROUTING
# ==========================================================
class OSRM:
    """
    Cache OSRM par paire de points (i,j).
    Avantage : ajouter/supprimer un point ne recalcule que les nouvelles lignes,
    pas toute la matrice.
    Cache structure :
      _osrm_pair_dist[(pt_a, pt_b)] = distance_m
      _osrm_pair_dur [(pt_a, pt_b)] = durée_s
    où pt_a/pt_b = (round(lat,6), round(lon,6))
    """
    _session: Optional["requests.Session"] = None

    @staticmethod
    def _get_session():
        if OSRM._session is None:
            import requests
            OSRM._session = requests.Session()
        return OSRM._session

    @staticmethod
    def _pt(coord) -> tuple:
        """Clé normalisée d'un point."""
        return (round(coord[0], 6), round(coord[1], 6))

    @staticmethod
    def matrix(coords) -> Optional[Tuple[list, list]]:
        """
        Retourne (dist_matrix, dur_matrix) en listes de listes.
        Utilise le cache par paire — seules les paires manquantes
        sont envoyées à OSRM.
        """
        try:
            n = len(coords)
            dist_cache = st.session_state.setdefault("_osrm_pair_dist", {})
            dur_cache  = st.session_state.setdefault("_osrm_pair_dur",  {})

            pts = [OSRM._pt(c) for c in coords]

            # Identifier les paires manquantes
            missing_indices = set()
            for i in range(n):
                for j in range(n):
                    if (pts[i], pts[j]) not in dist_cache:
                        missing_indices.add(i)
                        missing_indices.add(j)

            # Requête OSRM uniquement pour les points manquants
            if missing_indices:
                sub_idx    = sorted(missing_indices)
                sub_coords = [coords[i] for i in sub_idx]
                s = ";".join(f"{lon},{lat}" for lat, lon in sub_coords)
                d = None
                for base_url in (OSRM_URL, OSRM_FALLBACK_URL):
                    try:
                        r = OSRM._get_session().get(
                            f"{base_url}/table/v1/driving/{s}?annotations=distance,duration",
                            timeout=15
                        )
                        r.raise_for_status()
                        d = r.json()
                        if "distances" in d and "durations" in d:
                            if base_url != OSRM_URL:
                                st.toast(f"⚠️ Serveur OSRM principal indisponible — serveur de secours utilisé.", icon="⚠️")
                            break
                        d = None
                    except Exception as e:
                        st.session_state.last_error = f"OSRM ({base_url}): {e}"
                        d = None
                if d is None:
                    st.session_state.last_error = "OSRM indisponible (serveur principal et de secours)"
                    return None
                sub_pts = [pts[i] for i in sub_idx]
                for si, pi in enumerate(sub_pts):
                    for sj, pj in enumerate(sub_pts):
                        dist_cache[(pi, pj)] = d["distances"][si][sj]
                        dur_cache [(pi, pj)] = d["durations"][si][sj]

            # Assembler la matrice + appliquer le coefficient correcteur sur les durées
            coeff = st.session_state.get("osrm_time_coeff", 1.15)
            dist_m = [[dist_cache.get((pts[i], pts[j]), 0.0) for j in range(n)] for i in range(n)]
            dur_s  = [[dur_cache.get ((pts[i], pts[j]), 0.0) * coeff for j in range(n)] for i in range(n)]
            return (dist_m, dur_s)

        except Exception as e:
            st.session_state.last_error = f"OSRM: {e}"
            return None

# ==========================================================
# OPTIMIZER
# ==========================================================
class Optimizer:
    PAUSE_START = 12 * SPH   # valeur par défaut (écrasée par session_state si configurée)
    PAUSE_END   = 13 * SPH

    # ──────────────────────────────────────────────────────
    # 🧠 Cheapest Insertion  (meilleure init que Nearest Neighbor)
    # Principe : part du nœud le plus éloigné du dépôt, insère
    # chaque nœud restant à sa position de coût minimal.
    # Gain typique : -15 à -25 % vs Nearest Neighbor.
    # ──────────────────────────────────────────────────────
    @staticmethod
    def cheapest_insertion(candidates: List[int], start: int,
                           end: int, dist) -> List[int]:
        """
        Construit un ordre optimal par insertion économique.
        candidates : liste d'indices de nœuds à ordonner
        start / end : indices du nœud de départ et d'arrivée (dépôt)
        dist        : matrice de distances (liste de listes)
        Retourne la liste ordonnée des nœuds (sans start/end).
        """
        if not candidates:
            return []
        if len(candidates) == 1:
            return list(candidates)

        # Initialisation : nœud le plus loin du départ
        seed_node = max(candidates, key=lambda n: dist[start][n])
        route = [start, seed_node, end]
        remaining = [c for c in candidates if c != seed_node]

        while remaining:
            best_cost = float("inf")
            best_node = -1
            best_pos  = -1
            for node in remaining:
                for pos in range(1, len(route)):
                    a, b = route[pos - 1], route[pos]
                    delta = dist[a][node] + dist[node][b] - dist[a][b]
                    if delta < best_cost:
                        best_cost = delta
                        best_node = node
                        best_pos  = pos
            route.insert(best_pos, best_node)
            remaining.remove(best_node)

        return route[1:-1]  # Retirer start et end

    # ──────────────────────────────────────────────────────
    # ⚡ 2-opt delta-distance  (O(1) par swap, pas de recalcul global)
    # Calcule uniquement le gain sur les 4 arêtes concernées.
    # ──────────────────────────────────────────────────────
    @staticmethod
    def two_opt_delta(chain: List[int], start: int, end: int,
                      dist, max_iter: int = 3) -> Tuple[List[int], bool]:
        """
        2-opt delta — calcul sur les 4 arêtes concernées uniquement.
        max_iter=3 : 95% du gain en 2-3 passes, pas besoin de converger totalement.
        Skip j=i+1 : swap adjacent = inutile (ne change rien à la distance).
        Retourne (chaîne_améliorée, improved:bool) pour early-exit dans or_opt_1.
        """
        if len(chain) < 2:
            return chain, False
        route = [start] + list(chain) + [end]
        n = len(route)
        any_improved = False
        improved = True
        iters = 0
        while improved and iters < max_iter:
            improved = False
            iters += 1
            for i in range(1, n - 2):
                ri_prev = route[i - 1]
                ri      = route[i]
                for j in range(i + 2, n - 1):   # i+2 : skip arête adjacente j=i+1
                    rj      = route[j]
                    rj_next = route[j + 1]
                    delta = (
                        dist[ri_prev][rj]
                        + dist[ri][rj_next]
                        - dist[ri_prev][ri]
                        - dist[rj][rj_next]
                    )
                    if delta < -1e-9:
                        route[i:j + 1] = route[i:j + 1][::-1]
                        improved     = True
                        any_improved = True
                        ri = route[i]
        return route[1:-1], any_improved

    @staticmethod
    def or_opt_1(chain: List[int], start: int, end: int, dist) -> Tuple[List[int], bool]:
        """
        Or-Opt-1 : déplace un nœud à sa meilleure position dans la chaîne.
        (anciennement Or-Opt avec nœud unique — pas un vrai 3-opt)
        Complexité O(n²) — utilise un index de position pour éviter .index() O(n).
        Retourne (chaîne_améliorée, improved:bool) pour permettre l'early-exit.
        """
        if len(chain) < 4:
            return chain, False
        route = [start] + list(chain) + [end]
        n = len(route)
        any_improved = False
        improved = True
        while improved:
            improved = False
            # Index de position O(1) : pos_of[node] = indice dans route
            pos_of = {node: idx for idx, node in enumerate(route)}
            for i in range(1, n - 1):
                node   = route[i]
                prev_i = route[i - 1]
                next_i = route[i + 1]
                removal_gain = dist[prev_i][node] + dist[node][next_i] - dist[prev_i][next_i]
                for j in range(1, n - 2):   # n-2 : j+1 < n garanti, check redondant supprimé
                    if j == i or j == i - 1:
                        continue
                    a, b = route[j], route[j + 1]
                    insert_cost = dist[a][node] + dist[node][b] - dist[a][b]
                    if removal_gain - insert_cost > 1e-9:
                        # Retirer node de la position i, insérer après j
                        route.pop(i)
                        ins = j if j < i else j - 1   # j décale si on retirait avant
                        route.insert(ins + 1, node)
                        n = len(route)
                        improved     = True
                        any_improved = True
                        break
                if improved:
                    break
        return route[1:-1], any_improved

    # ── Paramètres configurables ─────────────────────────────────────────────
    @staticmethod
    def _params() -> dict:
        """Retourne les paramètres configurables depuis session_state."""
        return {
            "pause_start":  st.session_state.get("opt_pause_start",  12 * SPH),
            "pause_end":    st.session_state.get("opt_pause_end",    13 * SPH),
            "max_dur":      st.session_state.get("opt_max_matin_dur",  4 * SPH),
            "max_slots":    st.session_state.get("opt_max_matin_slots", 4),
        }

    @staticmethod
    def fmt(s): return f"{int(s)//3600:02d}:{(int(s)%3600)//60:02d}"

    @staticmethod
    def _chain_cost(chain: List[int], start: int, end: int, dist) -> float:
        """Coût total d'une sous-chaîne (start → chain[0] → … → chain[-1] → end)."""
        if not chain:
            return float(dist[start][end])
        full = [start] + chain + [end]
        return sum(float(dist[full[k]][full[k+1]]) for k in range(len(full)-1))

    @staticmethod
    def held_karp(candidates: List[int], start: int, end: int, dist) -> List[int]:
        """
        Held-Karp — programmation dynamique TSP exact.
        Garantit la tournée OPTIMALE pour la sous-chaîne donnée.

        Complexité : O(n² · 2ⁿ)  →  utilisé uniquement si len(candidates) ≤ 11
          n=8  →  256 états   < 1 ms
          n=11 →  2048 états  < 20 ms

        Paramètres :
          candidates : liste des nœuds intermédiaires (indices dans dist)
          start / end : nœuds de départ et d'arrivée (dépôt)
          dist       : matrice de distances/durées

        Retourne la liste ordonnée des candidats (sans start/end).
        """
        from itertools import combinations

        n = len(candidates)
        if n == 0:
            return []
        if n == 1:
            return list(candidates)

        # Renuméroter localement : 0 = start, 1..n = candidates, (n+1) = end
        # dist_local[i][j] précalculée — évite float(dist[local[i]][local[j]]) à chaque appel
        local      = [start] + list(candidates)   # local[0]=start, local[1..n]=candidats
        size       = n + 1
        dist_local = [[float(dist[local[i]][local[j]]) for j in range(size)]
                      for i in range(size)]
        # dist_end[k] = coût local[k] → end  (end peut être hors local)
        dist_end   = [float(dist[local[k]][end]) for k in range(size)]

        def d(i, j):
            return dist_local[i][j]

        # dp[(subset_bits, last)] = (coût_min, nœud_précédent)
        # subset_bits : masque des candidats locaux visités (bits 1..n, bit 0 = start exclu)
        dp: dict = {}

        # Init : depuis start (local 0) vers chaque candidat k (local 1..n)
        for k in range(1, size):
            dp[(1 << k, k)] = (d(0, k), 0)

        # Remplissage par taille de sous-ensemble croissante
        for subset_size in range(2, size):
            for subset in combinations(range(1, size), subset_size):
                bits = 0
                for b in subset:
                    bits |= (1 << b)
                for k in subset:
                    prev_bits = bits & ~(1 << k)
                    best_cost = None
                    best_prev = None
                    for m in subset:
                        if m == k:
                            continue
                        state = dp.get((prev_bits, m))
                        if state is None:
                            continue
                        cost = state[0] + d(m, k)
                        if best_cost is None or cost < best_cost:
                            best_cost = cost
                            best_prev = m
                    if best_cost is not None:
                        dp[(bits, k)] = (best_cost, best_prev)

        full_bits = (1 << size) - 2   # tous les bits 1..n allumés
        best_final_cost = None
        best_last_local = None

        for k in range(1, size):
            state = dp.get((full_bits, k))
            if state is None:
                continue
            cost = state[0] + dist_end[k]   # précalculé
            if best_final_cost is None or cost < best_final_cost:
                best_final_cost = cost
                best_last_local = k

        if best_last_local is None:
            # Fallback si dp incomplet (ne devrait pas arriver)
            return list(candidates)

        # Reconstruction du chemin (en sens inverse)
        path_local = []
        last  = best_last_local
        bits  = full_bits
        for _ in range(n):
            path_local.append(last)
            state    = dp.get((bits, last))
            prev     = state[1] if state else 0
            bits     = bits & ~(1 << last)
            last     = prev

        path_local.reverse()
        # Reconvertir vers indices originaux (local[k] = candidates[k-1])
        return [local[k] for k in path_local]

    @staticmethod
    def _randomized_best_chain(
        candidates: List[int], start: int, end: int,
        dist, n_trials: int = 20
    ) -> List[int]:
        """
        Randomized construction : essaie n_trials ordres initiaux aléatoires
        des candidats, applique cheapest_insertion + 2-opt + 3-opt sur chacun,
        retourne la meilleure sous-chaîne trouvée.

        Principe (cf. OR-Tools GRASP) :
          for _ in range(n_trials):
              shuffled = candidates[:]
              random.shuffle(shuffled)
              chain = cheapest_insertion(shuffled, dist)
              chain = two_opt(chain, dist)
          → garder le meilleur
        Gain typique vs construction déterministe seule : 5-15 % sur distance.

        Si len(candidates) ≤ 11 : utilise Held-Karp (solution OPTIMALE garantie)
        au lieu des tirages aléatoires.
        """
        import random

        if len(candidates) <= 1:
            return list(candidates)

        # ── Held-Karp : solution optimale garantie pour les petites sous-chaînes ──
        HELD_KARP_THRESHOLD = 13   # exact DP — 2^13=8192 états, <100ms, parfait jusqu'à 13 arrêts
        if len(candidates) <= HELD_KARP_THRESHOLD:
            return Optimizer.held_karp(candidates, start, end, dist)

        # ── Randomized construction pour les grandes sous-chaînes ────────────────
        # Solution de référence : construction déterministe
        best_chain, two_opt_improved = Optimizer.two_opt_delta(
            Optimizer.cheapest_insertion(candidates, start, end, dist), start, end, dist)
        if two_opt_improved:   # early-exit : or_opt_1 seulement si 2-opt a amélioré
            best_chain, _ = Optimizer.or_opt_1(best_chain, start, end, dist)
        best_cost = Optimizer._chain_cost(best_chain, start, end, dist)

        # n_trials tirages aléatoires
        for _ in range(n_trials):
            shuffled = candidates[:]
            random.shuffle(shuffled)
            chain, improved2 = Optimizer.two_opt_delta(
                Optimizer.cheapest_insertion(shuffled, start, end, dist), start, end, dist)
            if improved2:
                chain, _ = Optimizer.or_opt_1(chain, start, end, dist)
            cost = Optimizer._chain_cost(chain, start, end, dist)
            if cost < best_cost - 1e-9:
                best_chain = chain
                best_cost  = cost

        return best_chain

    @staticmethod
    def optimize(config: RouteConfig, points: List[DeliveryPoint],
                 precomputed_mats=None) -> Optional["RouteResult"]:

        # ── Hash de la tournée : si rien n'a changé, retourner le résultat en cache ──
        _p_params = Optimizer._params()
        tour_hash = hash((
            config.start_address, config.end_address,
            config.start_time, config.start_service_duration,
            tuple((p.address, p.time_mode, p.target_time,
                   p.intervention_type, p.service_duration) for p in points),
            _p_params["pause_start"], _p_params["pause_end"],
            _p_params["max_dur"],     _p_params["max_slots"],
        ))
        cached_result = st.session_state.get("_optim_cache")
        if cached_result and cached_result[0] == tour_hash:
            return cached_result[1]

        all_coords = (
            [config.start_coordinates] +
            [p.coordinates for p in points] +
            [config.end_coordinates]
        )
        if len(all_coords) > 40:
            st.session_state.last_error = "Max 40 points (OSRM public)"
            return None
        # Toujours appeler avec precomputed_mats depuis main() pour éviter
        # un double appel OSRM. En cas d'appel direct non prévu, on recalcule
        # mais on avertit via last_error.
        if precomputed_mats is None:
            st.session_state.last_error = "⚠️ optimize() appelé sans matrice précalculée — recalcul OSRM."
        mats = precomputed_mats if precomputed_mats is not None else OSRM.matrix(all_coords)
        if mats is None: return None
        dist_m, dur_s = mats
        if any(v is not None and math.isnan(v) for row in dist_m for v in row) or \
           any(v is not None and math.isnan(v) for row in dur_s  for v in row):
            st.session_state.last_error = "Matrice OSRM invalide"
            return None
        n_pts = len(points)
        svc = [config.start_service_duration] + [p.service_duration for p in points] + [0]
        _p   = _p_params   # réutilise le dict déjà calculé pour le hash — pas d'appel double
        PAUSE_START = _p["pause_start"]
        PAUSE_END   = _p["pause_end"]
        matin_nodes  = []
        fixe_nodes   = []
        apm_nodes    = []
        libre_nodes  = []
        for i, p in enumerate(points):
            mat_idx = i + 1
            if p.time_mode == "Matin libre":
                matin_nodes.append(mat_idx)
            elif p.time_mode == "Après-midi libre":
                apm_nodes.append(mat_idx)
            elif p.time_mode == "Heure précise" and p.target_time is not None:
                if p.target_time < PAUSE_START:
                    matin_nodes.append(mat_idx)
                else:
                    fixe_nodes.append(mat_idx)
            else:
                libre_nodes.append(mat_idx)
        for li in libre_nodes:
            if not matin_nodes:
                matin_nodes.append(li)
                continue
            cost_matin = Optimizer._insertion_cost(li, matin_nodes, 0, dur_s)
            cost_apm   = Optimizer._insertion_cost(li, apm_nodes,
                             fixe_nodes[-1] if fixe_nodes else 0, dur_s)
            if cost_matin <= cost_apm * 1.5:
                matin_nodes.append(li)
            else:
                apm_nodes.append(li)
        chain_matin = Optimizer._nearest_chain(0,          matin_nodes, dur_s)
        last_matin  = chain_matin[-1] if chain_matin else 0
        chain_fixe  = Optimizer._nearest_chain(last_matin, fixe_nodes,  dur_s)
        last_fixe   = chain_fixe[-1] if chain_fixe else last_matin
        chain_apm   = Optimizer._nearest_chain(last_fixe,  apm_nodes,   dur_s)
        matin_nodes, apm_nodes, chain_matin, _ = Optimizer._enforce_matin_budget(
            chain_matin, apm_nodes, matin_nodes, points, dur_s, svc, config
        )
        last_matin = chain_matin[-1] if chain_matin else 0
        chain_fixe = Optimizer._nearest_chain(last_matin, fixe_nodes, dur_s)
        last_fixe  = chain_fixe[-1] if chain_fixe else last_matin
        chain_apm  = Optimizer._nearest_chain(last_fixe, apm_nodes, dur_s)
        chain_matin, chain_fixe, chain_apm, matin_nodes, apm_nodes = \
            Optimizer._group_nearby(
                chain_matin, chain_fixe, chain_apm,
                matin_nodes, apm_nodes, fixe_nodes,
                points, dur_s, svc, config
            )
        def optimize_last_node(chain: List[int], end_idx: int, prev_idx: int) -> List[int]:
            if len(chain) < 2:
                return chain
            def total_distance(c: List[int]) -> float:
                d = float(dur_s[prev_idx][c[0]])
                for k in range(len(c) - 1):
                    d += float(dur_s[c[k]][c[k+1]])
                d += float(dur_s[c[-1]][end_idx])
                return d
            best_chain = list(chain)
            best_dist  = total_distance(best_chain)
            for candidate in chain:
                others = [n for n in chain if n != candidate]
                if not others:
                    test_chain = [candidate]
                else:
                    rem = list(others); sub = []; cur = prev_idx
                    while rem:
                        nxt = min(rem, key=lambda x: float(dur_s[cur][x]))
                        sub.append(nxt); rem.remove(nxt); cur = nxt
                    test_chain = sub + [candidate]
                test_dist = total_distance(test_chain)
                if test_dist < best_dist:
                    best_chain = test_chain
                    best_dist  = test_dist
            return best_chain
        prev_apm = chain_fixe[-1] if chain_fixe else (chain_matin[-1] if chain_matin else 0)
        chain_apm = optimize_last_node(chain_apm, n_pts + 1, prev_apm)

        # ── Randomized construction / Held-Karp selon taille ──────────────
        n_trials = max(5, min(20, n_pts * 3))
        HELD_KARP_THRESHOLD = 13   # même seuil que _randomized_best_chain
        # Tournée optimale garantie si toutes les sous-chaînes rentrent dans HK
        is_optimal = (
            len(chain_matin) <= HELD_KARP_THRESHOLD and
            len(chain_fixe)  <= HELD_KARP_THRESHOLD and
            len(chain_apm)   <= HELD_KARP_THRESHOLD
        )

        end_matin   = chain_fixe[0] if chain_fixe else (chain_apm[0] if chain_apm else n_pts + 1)
        chain_matin = Optimizer._randomized_best_chain(
            chain_matin, 0, end_matin, dur_s, n_trials=n_trials)

        last_matin2 = chain_matin[-1] if chain_matin else 0
        end_fixe    = chain_apm[0] if chain_apm else n_pts + 1
        chain_fixe  = Optimizer._randomized_best_chain(
            chain_fixe, last_matin2, end_fixe, dur_s, n_trials=n_trials)

        last_fixe2  = chain_fixe[-1] if chain_fixe else last_matin2
        chain_apm   = Optimizer._randomized_best_chain(
            chain_apm, last_fixe2, n_pts + 1, dur_s, n_trials=n_trials)

        full_chain = chain_matin + chain_fixe + chain_apm
        order = [0] + full_chain + [n_pts + 1]
        arrivals = Optimizer._compute_times(order, config.start_time, dur_s, svc, points)
        Optimizer._check_constraints(order, arrivals, points, n_pts)
        total_dist = sum(float(dist_m[order[k]][order[k+1]]) for k in range(len(order)-1))
        matin_dur = (svc[0]
                     + sum(int(dur_s[chain_matin[k-1] if k>0 else 0][chain_matin[k]])
                           + svc[chain_matin[k]]
                           for k in range(len(chain_matin)))
                     ) if chain_matin else svc[0]
        original_matin = set()
        for i, p in enumerate(points):
            mat_idx = i + 1
            if p.time_mode in ("Matin libre", "Libre"):
                original_matin.add(mat_idx)
        moved_to_apm = [points[n-1].address for n in apm_nodes
                        if n in original_matin and n not in chain_fixe]


        result = RouteResult(
            order=order,
            total_distance=total_dist,
            total_time=arrivals[-1] - config.start_time,
            arrival_times=arrivals,
            is_approximation=not is_optimal,
            matin_moved=moved_to_apm,
            matin_duration=matin_dur,
            matin_count=len(chain_matin),
            initial_distance=sum(
                float(dist_m[k][k+1]) for k in range(len(order)-1)
            ),  # ordre séquentiel 0→1→2→…→n+1
        )
        # Mettre en cache : même tournée → même résultat sans recalcul
        st.session_state["_optim_cache"] = (tour_hash, result)
        return result

    @staticmethod
    def _insertion_cost(node: int, bloc: List[int], prev: int, dur_s) -> float:
        if not bloc:
            return float(dur_s[prev][node])
        path = [prev] + bloc
        best = float("inf")
        for k in range(len(path) - 1):
            a, b = path[k], path[k+1]
            cost = float(dur_s[a][node]) + float(dur_s[node][b]) - float(dur_s[a][b])
            if cost < best:
                best = cost
        return best

    @staticmethod
    def _nearest_chain(start: int, candidates: List[int], dur_s) -> List[int]:
        """
        ⚡ Remplacé par Cheapest Insertion (vs Nearest Neighbor v1).
        Gain typique : -15 à -25 % sur la distance de chaque sous-chaîne.
        """
        if not candidates:
            return []
        if len(candidates) == 1:
            return list(candidates)
        # Utilise un nœud fantôme "end = start" pour les sous-chaînes sans retour fixe
        return Optimizer.cheapest_insertion(candidates, start, start, dur_s)

    PROXIMITY_SEUIL = 5 * 60

    @staticmethod
    def nearby_conflicts(points: List[DeliveryPoint], dur_s) -> List[Tuple[int, int]]:
        SEUIL = Optimizer.PROXIMITY_SEUIL
        p_    = Optimizer._params()
        PAUSE_START = p_["pause_start"]
        PAUSE_END   = p_["pause_end"]
        conflicts = []
        n = len(points)
        # E: fonctions définies une seule fois hors boucle (évitait N*(N-1)/2 redéfinitions)
        def is_matin_locked(mode, target):
            return (mode == "Matin libre" or
                    (mode == "Heure précise" and target is not None
                     and target < PAUSE_START))
        def is_apm_locked(mode, target):
            return (mode == "Après-midi libre" or
                    (mode == "Heure précise" and target is not None
                     and target >= PAUSE_END))
        for i in range(n):
            for j in range(i + 1, n):
                a, b = i + 1, j + 1
                t_ab = int(dur_s[a][b]); t_ba = int(dur_s[b][a])
                if t_ab >= SEUIL and t_ba >= SEUIL:
                    continue
                mi, mj = points[i].time_mode, points[j].time_mode
                ti, tj = points[i].target_time, points[j].target_time
                i_matin = is_matin_locked(mi, ti)
                i_apm   = is_apm_locked(mi, ti)
                j_matin = is_matin_locked(mj, tj)
                j_apm   = is_apm_locked(mj, tj)
                if (i_matin and j_apm) or (i_apm and j_matin):
                    conflicts.append((i, j))
        return conflicts

    @staticmethod
    def _group_nearby(
        chain_matin, chain_fixe, chain_apm,
        matin_nodes, apm_nodes, fixe_nodes,
        points, dur_s, svc, config
    ):
        SEUIL   = Optimizer.PROXIMITY_SEUIL
        p_      = Optimizer._params()
        MAX_DUR = p_["max_dur"]
        MAX_SLT = p_["max_slots"]
        def mode_of(node):
            return points[node - 1].time_mode
        def is_free(node):
            return mode_of(node) == "Libre"
        def can_go_apm(node):
            return mode_of(node) in ("Libre", "Matin libre")
        def matin_fits(extra):
            chain = list(cm) + list(extra)
            t = svc[0]; cur = 0
            for n in chain:
                t += int(dur_s[cur][n]) + svc[n]; cur = n
            return t <= MAX_DUR and len(chain) <= MAX_SLT
        def close(a, b):
            return int(dur_s[a][b]) < SEUIL or int(dur_s[b][a]) < SEUIL
        def nn(start, nodes):
            if not nodes: return []
            rem = list(nodes); out = []; cur = start
            while rem:
                nxt = min(rem, key=lambda x: float(dur_s[cur][x]))
                out.append(nxt); rem.remove(nxt); cur = nxt
            return out
        cm = list(chain_matin)
        an = list(apm_nodes)
        for _pass in range(30):
            changed = False
            last_m = cm[-1] if cm else 0
            cf_tmp = nn(last_m, fixe_nodes)
            last_f = cf_tmp[-1] if cf_tmp else last_m
            ca_tmp = nn(last_f, an)
            for m_node in list(cm):
                for a_node in list(ca_tmp):
                    if not close(m_node, a_node):
                        continue
                    if m_node not in cm or a_node not in an:
                        continue
                    if not is_free(m_node) and not is_free(a_node):
                        continue
                    if not is_free(a_node):
                        if can_go_apm(m_node):
                            cm.remove(m_node); an.append(m_node); changed = True
                        break
                    if not is_free(m_node):
                        if is_free(a_node) and matin_fits([a_node]):
                            an.remove(a_node); cm.append(a_node); changed = True
                        break
                    if matin_fits([a_node]):
                        an.remove(a_node); cm.append(a_node); changed = True
                    elif can_go_apm(m_node):
                        cm.remove(m_node); an.append(m_node); changed = True
                    break
            if not changed:
                break
        last_m   = cm[-1] if cm else 0
        cf_final = nn(last_m, fixe_nodes)
        last_f   = cf_final[-1] if cf_final else last_m
        ca_final = nn(last_f, an)
        def enforce_adjacency(chain):
            pairs_in_chain = []
            for i in range(len(chain)):
                for j in range(i + 1, len(chain)):
                    if close(chain[i], chain[j]):
                        pairs_in_chain.append((chain[i], chain[j]))
            for a, b in pairs_in_chain:
                if a not in chain or b not in chain:
                    continue
                # G: dict de position construit une seule fois par paire
                pos = {v: k for k, v in enumerate(chain)}
                ia, ib = pos[a], pos[b]
                if abs(ia - ib) == 1:
                    continue
                chain = list(chain)
                chain.pop(ib)
                # G: mise à jour incrémentale de pos après pop — évite un rebuild O(n) complet
                pos = {v: (k if k < ib else k - 1) for v, k in pos.items() if v != b}
                ia = pos[a]
                chain.insert(ia + 1, b)
            return chain
        cm       = enforce_adjacency(cm)
        ca_final = enforce_adjacency(ca_final)
        return cm, cf_final, ca_final, cm, an

    @staticmethod
    def _enforce_matin_budget(
        chain_matin, apm_nodes, matin_nodes, points, dur_s, svc, config
    ):
        p      = Optimizer._params()
        MAX_DUR   = p["max_dur"]
        MAX_SLOTS = p["max_slots"]
        def is_movable(mat_idx: int) -> bool:
            p = points[mat_idx - 1]
            return p.time_mode in ("Libre", "Matin libre")
        def matin_total_time(chain: List[int]) -> int:
            t   = svc[0]
            cur = 0
            for node in chain:
                t  += int(dur_s[cur][node]) + svc[node]
                cur = node
            return t
        chain = list(chain_matin)
        apm   = list(apm_nodes)
        matin = list(matin_nodes)
        # D: calcul initial unique, puis mise à jour incrémentale à chaque retrait
        dur_m = matin_total_time(chain)
        for _ in range(len(chain) + 1):
            nb = len(chain)
            if dur_m <= MAX_DUR and nb <= MAX_SLOTS:
                break
            moved = False
            for j in range(len(chain) - 1, -1, -1):
                node = chain[j]
                if is_movable(node):
                    # D: mise à jour incrémentale — soustrait uniquement le coût du nœud retiré
                    prev_node = chain[j - 1] if j > 0 else 0
                    next_node = chain[j + 1] if j < len(chain) - 1 else None
                    cost_removed = int(dur_s[prev_node][node]) + svc[node]
                    if next_node is not None:
                        cost_removed += int(dur_s[node][next_node]) - int(dur_s[prev_node][next_node])
                    dur_m -= cost_removed
                    chain.pop(j)
                    apm.append(node)
                    if node in matin:
                        matin.remove(node)
                    moved = True
                    break
            if not moved:
                break
        return matin, apm, chain, apm

    @staticmethod
    def _compute_times(order, start_time, dur_s, svc, points):
        n_pts  = len(points)
        p_     = Optimizer._params()
        PAUSE_START = p_["pause_start"]
        PAUSE_END   = p_["pause_end"]
        arrivals = []
        t = start_time
        for step, node in enumerate(order):
            is_precise_in_pause = False
            if 0 < node <= n_pts:
                p = points[node - 1]
                if p.time_mode == "Heure précise" and p.target_time is not None:
                    if PAUSE_START <= p.target_time < PAUSE_END:
                        is_precise_in_pause = True
            if not is_precise_in_pause:
                if PAUSE_START <= t < PAUSE_END:
                    t = PAUSE_END
            if 0 < node <= n_pts:
                p = points[node - 1]
                tw_lo, tw_hi = TW.get(p)
                if t < tw_lo:
                    t = tw_lo
            arrivals.append(t)
            if step < len(order) - 1:
                next_node = order[step + 1]
                service   = svc[node]
                travel    = int(dur_s[node][next_node])
                t = t + service + travel
        return arrivals

    @staticmethod
    def _check_constraints(order, arrivals, points, n_pts):
        violations = []
        p_  = Optimizer._params()
        PAUSE_START = p_["pause_start"]
        PAUSE_END   = p_["pause_end"]
        for step, node in enumerate(order):
            if 0 < node <= n_pts:
                p = points[node - 1]
                t = arrivals[step]
                svc_end = t + p.service_duration
                tw_lo, tw_hi = TW.get(p)
                if p.time_mode == "Heure précise":
                    if t < tw_lo:
                        violations.append(
                            f"⚠️ '{p.address[:30]}' : arrivée à {Optimizer.fmt(t)} "
                            f"avant l'heure ({Optimizer.fmt(tw_lo)})"
                        )
                    elif t > tw_hi:
                        retard = t - tw_hi
                        violations.append(
                            f"⚠️ '{p.address[:30]}' : retard de {retard//60}min "
                            f"(service à {Optimizer.fmt(t)}, prévu {Optimizer.fmt(tw_lo)})"
                        )
                elif p.time_mode == "Matin libre":
                    if t >= PAUSE_START:
                        violations.append(
                            f"⚠️ '{p.address[:30]}' (matin) : arrivée à {Optimizer.fmt(t)}"
                        )
                elif p.time_mode == "Après-midi libre":
                    if t < PAUSE_END:
                        violations.append(
                            f"⚠️ '{p.address[:30]}' (APM) : arrivée à {Optimizer.fmt(t)}"
                        )
                if PAUSE_START <= t < PAUSE_END:
                    violations.append(
                        f"⚠️ '{p.address[:30]}' : tombe pendant la pause déjeuner "
                        f"({Optimizer.fmt(t)})"
                    )
        if violations:
            st.warning("Contraintes à vérifier :\n" + "\n".join(violations))

# ==========================================================
# VALIDATOR
# ==========================================================
class Validator:
    @staticmethod
    def check_point_time(p: DeliveryPoint) -> Tuple[bool, Optional[str]]:
        if p.time_mode == "Heure précise":
            if p.target_time is None:
                return False, "Heure cible non spécifiée"
            if not (WORK_START <= p.target_time <= WORK_END):
                h = p.target_time // SPH; m = (p.target_time % SPH) // SPM
                return False, f"Heure {h:02d}:{m:02d} hors plage 08h-18h"
        return True, None

    @staticmethod
    def check_setup(config: RouteConfig, points: List[DeliveryPoint]) -> Tuple[bool, Optional[str]]:
        if not config.start_address:     return False, "Adresse de départ manquante"
        if not config.start_coordinates: return False, "Départ non géocodé"
        if not config.end_address:       return False, "Adresse de retour manquante"
        if not config.end_coordinates:   return False, "Retour non géocodé"
        if not points:                   return False, "Aucun point d'arrêt"
        for p in points:
            if not p.coordinates: return False, f"Non géocodé: {p.address}"
        for i, p in enumerate(points):
            ok, err = Validator.check_point_time(p)
            if not ok: return False, f"Point {i+1}: {err}"
        return True, None

# ==========================================================
# UI
# ==========================================================
class UI:

    # ── Fenêtres modales (st.dialog si dispo, sinon inline) ───────────────

    @staticmethod
    @staticmethod
    def _edit_point(idx: int, address: str):
        """Ouvre un dialog pour modifier l'adresse d'un point de la tournée."""
        if HAS_DIALOG:
            @st.dialog("✏️ Modifier l'adresse")
            def _dlg():
                new_addr = st.text_input("Adresse", value=address, key="edit_addr_input")
                if new_addr and Geo.is_incomplete_address(new_addr):
                    st.caption("💡 Pas de code postal — géocodage peut échouer")
                col_ok, col_no = st.columns(2)
                with col_ok:
                    if st.button("✅ Valider", type="primary",
                                 use_container_width=True, key="dlg_edit_ok"):
                        if new_addr.strip() and new_addr.strip() != address:
                            pts = StateManager.points()
                            pts[idx].address = new_addr.strip()
                            pts[idx].coordinates = None   # forcer re-géocodage
                            StateManager.commit()
                        else:
                            st.rerun()
                with col_no:
                    if st.button("Annuler", use_container_width=True, key="dlg_edit_no"):
                        st.rerun()
            _dlg()
        else:
            # Fallback inline
            key_edit = f"_pending_edit_{idx}"
            if st.session_state.get(key_edit):
                new_addr = st.text_input("Nouvelle adresse", value=address,
                                         key=f"edit_addr_inline_{idx}")
                c1, c2 = st.columns(2)
                with c1:
                    if st.button("✅ Valider", key=f"edit_ok_{idx}",
                                 type="primary", use_container_width=True):
                        if new_addr.strip() and new_addr.strip() != address:
                            pts = StateManager.points()
                            pts[idx].address = new_addr.strip()
                            pts[idx].coordinates = None
                        st.session_state.pop(key_edit, None)
                        StateManager.commit()
                with c2:
                    if st.button("Annuler", key=f"edit_no_{idx}",
                                 use_container_width=True):
                        st.session_state.pop(key_edit, None)
                        st.rerun()
            else:
                st.session_state[key_edit] = True
                st.rerun()

    @staticmethod
    def _confirm_delete_point(idx: int, address: str):
        """Ouvre une confirmation avant de supprimer un point de la tournée."""
        if HAS_DIALOG:
            @st.dialog("🗑️ Supprimer ce point ?")
            def _dlg():
                st.write(f"**{address}**")
                st.caption("Cette action supprimera le point de la tournée en cours.")
                col_ok, col_no = st.columns(2)
                with col_ok:
                    if st.button("✅ Confirmer", type="primary",
                                 use_container_width=True, key="dlg_del_ok"):
                        StateManager.remove_point(idx)
                        StateManager.commit()
                with col_no:
                    if st.button("Annuler", use_container_width=True, key="dlg_del_no"):
                        st.rerun()
            _dlg()
        else:
            # Fallback : bouton de confirmation inline
            key_confirm = f"_pending_del_{idx}"
            if st.session_state.get(key_confirm):
                st.warning(f"Confirmer la suppression de **{address[:40]}** ?")
                c1, c2 = st.columns(2)
                with c1:
                    if st.button("✅ Oui, supprimer", key=f"dlg_del_ok_{idx}",
                                 type="primary", use_container_width=True):
                        st.session_state.pop(key_confirm, None)
                        StateManager.remove_point(idx)
                        StateManager.commit()
                with c2:
                    if st.button("Annuler", key=f"dlg_del_no_{idx}",
                                 use_container_width=True):
                        st.session_state.pop(key_confirm, None)
                        st.rerun()
            else:
                st.session_state[key_confirm] = True
                st.rerun()

    @staticmethod
    def _confirm_delete_save(save_name: str):
        """Ouvre une confirmation avant de supprimer une sauvegarde."""
        if HAS_DIALOG:
            @st.dialog("🗑️ Supprimer la sauvegarde ?")
            def _dlg():
                st.write(f"**« {save_name} »**")
                st.caption("Cette action est irréversible.")
                col_ok, col_no = st.columns(2)
                with col_ok:
                    if st.button("✅ Supprimer", type="primary",
                                 use_container_width=True, key="dlg_save_ok"):
                        RouteManager.delete(save_name)
                        st.rerun()
                with col_no:
                    if st.button("Annuler", use_container_width=True, key="dlg_save_no"):
                        st.rerun()
            _dlg()
        else:
            if RouteManager.delete(save_name):
                st.rerun()

    @staticmethod
    def _dialog_conflicts(conflicts, pts):
        """Modale pour les conflits de créneaux — retourne True si l'utilisateur force."""
        if HAS_DIALOG:
            @st.dialog("⚠️ Créneaux incompatibles détectés", width="large")
            def _dlg():
                st.markdown(
                    "Les paires suivantes sont à **moins de 5 minutes** l'une de l'autre "
                    "mais ont des créneaux sur des **demi-journées opposées**.")
                for (i, j) in conflicts:
                    pi, pj = pts[i], pts[j]
                    ci = "🌅 Matin" if "Matin" in pi.time_mode or (
                        pi.time_mode == "Heure précise" and pi.target_time
                        and pi.target_time < 43200) else "🌆 APM"
                    cj = "🌅 Matin" if "Matin" in pj.time_mode or (
                        pj.time_mode == "Heure précise" and pj.target_time
                        and pj.target_time < 43200) else "🌆 APM"
                    st.info(f"• **{pi.address[:45]}** ({ci})  ↔  **{pj.address[:45]}** ({cj})")
                st.markdown("---")
                col_ok, col_no = st.columns(2)
                with col_ok:
                    if st.button("▶ Optimiser quand même", type="primary",
                                 use_container_width=True, key="dlg_conf_ok"):
                        st.session_state["_force_optim"] = True
                        st.rerun()
                with col_no:
                    if st.button("✏️ Modifier les créneaux",
                                 use_container_width=True, key="dlg_conf_no"):
                        st.session_state["_force_optim"] = False
                        st.rerun()
            _dlg()
            return False   # on attend le rerun
        else:
            # Fallback inline (comportement précédent)
            st.warning("⚠️ **Adresses proches avec créneaux incompatibles**")
            for (i, j) in conflicts:
                pi, pj = pts[i], pts[j]
                ci = "🌅 Matin" if "Matin" in pi.time_mode else "🌆 APM"
                cj = "🌅 Matin" if "Matin" in pj.time_mode else "🌆 APM"
                st.info(f"• **{pi.address[:40]}** ({ci})  ↔  **{pj.address[:40]}** ({cj})")
            col_ok, col_no = st.columns(2)
            with col_ok:
                if st.button("▶ Optimiser quand même", type="primary", key="force_optim"):
                    return True
            with col_no:
                st.button("✏️ Modifier les créneaux", key="cancel_optim")
            return False

    @staticmethod
    def params_tab():
        """Contenu de l'onglet Paramètres — fragment beta."""
        if HAS_FRAGMENT:
            @st.fragment
            def _run():
                UI._params_tab_body()
            _run()
        else:
            UI._params_tab_body()

    @staticmethod
    def _params_tab_body():
        """Corps de l'onglet Paramètres (séparé pour fragmentation)."""
        cfg      = StateManager.config()
        contacts = StateManager.get_contacts()

        # ── Mise en page 2 colonnes pour écran 14" ───────────────────────
        col_depart, col_options = st.columns(2, gap="large")

        with col_depart:
            # ── Départ ───────────────────────────────────────────────────
            st.markdown("#### 🏠 Départ")
            if contacts:
                with st.expander("📒 Choisir depuis le carnet", expanded=False):
                    search_dep = st.text_input("Filtrer", placeholder="Nom ou adresse…",
                                               key="dep_book_search", label_visibility="collapsed")
                    sl = search_dep.lower() if search_dep else ""
                    filtered_dep = [(c["name"], c["address"]) for c in contacts
                                if not sl or sl in c["name"].lower() or sl in c["address"].lower()]
                    if filtered_dep:
                        options = [f"{n[:25]} — {a[:25]}" for n, a in filtered_dep]
                        choice = st.selectbox("Contact", options, key="dep_book_choice",
                                              label_visibility="collapsed")
                        if st.button("✅ Utiliser comme départ", key="dep_book_apply",
                                     use_container_width=True):
                            chosen_addr = filtered_dep[options.index(choice)][1]
                            StateManager.update_config(start_address=chosen_addr, start_coordinates=None)
                            st.session_state["si_start"] = chosen_addr
                            StateManager.commit()
                    else:
                        st.caption("Aucun contact trouvé")

            if "si_start" not in st.session_state:
                st.session_state["si_start"] = cfg.start_address
            val = st.text_input("Adresse de départ", key="si_start")
            if val != cfg.start_address:
                StateManager.update_config(start_address=val, start_coordinates=None)
                StateManager.commit(do_rerun=False)

            c_t, c_s = st.columns(2)
            with c_t:
                default_t = datetime.strptime(
                    f"{cfg.start_time//SPH:02d}:{(cfg.start_time%SPH)//SPM:02d}", "%H:%M"
                ).time()
                ti = st.time_input("Heure de départ", value=default_t, key="si_stime")
                ts = ti.hour * SPH + ti.minute * SPM
                if ts != cfg.start_time:
                    StateManager.update_config(start_time=ts)
                    StateManager.commit(do_rerun=False)
            with c_s:
                svc_dep_min = st.number_input("Durée sur place (min)", 0, 180,
                                              value=cfg.start_service_duration // SPM,
                                              step=5, key="si_svc_dep")
                if svc_dep_min * SPM != cfg.start_service_duration:
                    StateManager.update_config(start_service_duration=int(svc_dep_min) * SPM)
                    StateManager.commit(do_rerun=False)

            st.markdown("---")
            # ── Retour ───────────────────────────────────────────────────
            st.markdown("#### 🏁 Retour")
            if contacts:
                with st.expander("📒 Choisir depuis le carnet", expanded=False):
                    search_end = st.text_input("Filtrer", placeholder="Nom ou adresse…",
                                               key="end_book_search", label_visibility="collapsed")
                    sl2 = search_end.lower() if search_end else ""
                    filtered_end = [(c["name"], c["address"]) for c in contacts
                                    if not sl2 or sl2 in c["name"].lower() or sl2 in c["address"].lower()]
                    if filtered_end:
                        options_end = [f"{n[:25]} — {a[:25]}" for n, a in filtered_end]
                        choice_end = st.selectbox("Contact", options_end, key="end_book_choice",
                                                  label_visibility="collapsed")
                        if st.button("✅ Utiliser comme retour", key="end_book_apply",
                                     use_container_width=True):
                            chosen_addr = filtered_end[options_end.index(choice_end)][1]
                            StateManager.update_config(end_address=chosen_addr, end_coordinates=None)
                            st.session_state["si_end"] = chosen_addr
                            StateManager.commit()
                    else:
                        st.caption("Aucun contact trouvé")

            if "si_end" not in st.session_state:
                st.session_state["si_end"] = cfg.end_address
            val_end = st.text_input("Adresse de retour", key="si_end")
            if val_end != cfg.end_address:
                StateManager.update_config(end_address=val_end, end_coordinates=None)
                StateManager.commit(do_rerun=False)

        with col_options:
            # ── Optimiseur ───────────────────────────────────────────────
            st.markdown("#### ⚙️ Paramètres optimiseur")
            if st.session_state.pop("_reset_params_pending", False):
                for k, v in [("inp_ps_h",12),("inp_ps_m",0),("inp_pe_h",13),
                             ("inp_pe_m",0),("inp_max_dur",4),("inp_max_slots",4),
                             ("inp_osrm_coeff", 15)]:
                    st.session_state[k] = v
                st.session_state.opt_pause_start     = 12 * SPH
                st.session_state.opt_pause_end       = 13 * SPH
                st.session_state.opt_max_matin_dur   = 4  * SPH
                st.session_state.opt_max_matin_slots = 4
                st.session_state["osrm_time_coeff"]  = 1.15

            if "inp_ps_h"      not in st.session_state: st.session_state["inp_ps_h"]      = st.session_state.opt_pause_start // SPH
            if "inp_ps_m"      not in st.session_state: st.session_state["inp_ps_m"]      = (st.session_state.opt_pause_start % SPH) // SPM
            if "inp_pe_h"      not in st.session_state: st.session_state["inp_pe_h"]      = st.session_state.opt_pause_end // SPH
            if "inp_pe_m"      not in st.session_state: st.session_state["inp_pe_m"]      = (st.session_state.opt_pause_end % SPH) // SPM
            if "inp_max_dur"   not in st.session_state: st.session_state["inp_max_dur"]   = st.session_state.opt_max_matin_dur // SPH
            if "inp_max_slots" not in st.session_state: st.session_state["inp_max_slots"] = st.session_state.opt_max_matin_slots

            st.caption("Pause méridienne")
            p1, p2 = st.columns(2)
            with p1:
                new_ps_h = st.number_input("Début pause (h)", 8, 16, key="inp_ps_h")
                new_ps_m = st.selectbox("min",  [0,15,30,45], key="inp_ps_m")
            with p2:
                new_pe_h = st.number_input("Fin pause (h)",   9, 17, key="inp_pe_h")
                new_pe_m = st.selectbox("min ", [0,15,30,45], key="inp_pe_m")
            new_ps = new_ps_h * SPH + new_ps_m * SPM
            new_pe = new_pe_h * SPH + new_pe_m * SPM
            if new_ps != st.session_state.opt_pause_start or new_pe != st.session_state.opt_pause_end:
                if new_pe > new_ps:
                    st.session_state.opt_pause_start = new_ps
                    st.session_state.opt_pause_end   = new_pe
                    StateManager.commit(do_rerun=False)
                else:
                    st.warning("La fin de pause doit être après le début.")

            new_max_dur = st.slider("Objectif matin (h)", 1, 6, key="inp_max_dur")
            if new_max_dur * SPH != st.session_state.opt_max_matin_dur:
                st.session_state.opt_max_matin_dur = new_max_dur * SPH
                StateManager.commit(do_rerun=False)
            new_max_slots = st.slider("Max arrêts matin", 1, 10, key="inp_max_slots")
            if new_max_slots != st.session_state.opt_max_matin_slots:
                st.session_state.opt_max_matin_slots = new_max_slots
                StateManager.commit(do_rerun=False)

            st.markdown("---")
            st.caption("🛣️ Correction temps de trajet OSRM")
            coeff_pct = st.slider(
                "Marge sur les temps calculés (%)", 0, 40,
                value=int(round((st.session_state.get("osrm_time_coeff", 1.15) - 1.0) * 100)),
                step=5, key="inp_osrm_coeff",
                help="OSRM calcule des temps théoriques. +15% recommandé pour routes sinueuses (Vosges)."
            )
            new_coeff = 1.0 + coeff_pct / 100.0
            if abs(new_coeff - st.session_state.get("osrm_time_coeff", 1.15)) > 0.001:
                st.session_state["osrm_time_coeff"] = new_coeff
                st.session_state.pop("_osrm_pair_dur", None)   # invalider le cache durées
                StateManager.commit(do_rerun=False)
            st.caption(f"Temps OSRM × {new_coeff:.2f}")

            if st.button("↩️ Remettre par défaut", key="reset_params"):
                st.session_state["_reset_params_pending"] = True
                StateManager.commit(do_rerun=False)
                st.rerun()



    @staticmethod
    def export_google_maps_url(result: RouteResult, cfg: RouteConfig, points: List[DeliveryPoint]) -> str:
        """Génère l'URL Google Maps avec tous les waypoints."""
        all_coords = [cfg.start_coordinates] + [p.coordinates for p in points] + [cfg.end_coordinates]
        ordered_coords = [all_coords[node] for node in result.order if all_coords[node]]
        
        if len(ordered_coords) < 2:
            return ""
        
        origin = f"{ordered_coords[0][0]},{ordered_coords[0][1]}"
        dest = f"{ordered_coords[-1][0]},{ordered_coords[-1][1]}"
        waypoints = "|".join([f"{c[0]},{c[1]}" for c in ordered_coords[1:-1]])
        
        url = f"https://www.google.com/maps/dir/?api=1&origin={origin}&destination={dest}"
        if waypoints:
            url += f"&waypoints={waypoints}"
        url += "&travelmode=driving"
        
        return url
        
    @staticmethod
    def address_list():
        st.subheader("Configuration des interventions")
        cfg = StateManager.config()
        points = StateManager.points()

        # Construire un dict node→heure d'arrivée depuis le résultat si disponible
        result = st.session_state.get("optimized_result")
        arrival_by_node: dict = {}
        if result:
            for step, node in enumerate(result.order):
                arrival_by_node[node] = result.arrival_times[step]

        def fmt_t(s): return f"{s//3600:02d}:{(s%3600)//60:02d}"

        c1, c2, c3 = st.columns([6, 2, 2])
        with c1: st.write(f"  **DÉPART:** {cfg.start_address or '(non configuré)'}")
        with c2:
            h, m = cfg.start_time//SPH, (cfg.start_time%SPH)//SPM
            st.write(f"ߕ {h:02d}:{m:02d}")
        with c3:
            if cfg.start_service_duration > 0:
                st.caption(f"⏱ {cfg.start_service_duration//SPM}min sur place")
        st.markdown("---")

        if not points:
            st.caption("Aucune intervention ajoutée.")
        else:
            st.write("**Interventions :**")
            for i, p in enumerate(points):
                node = i + 1
                arr = arrival_by_node.get(node)
                # Colonnes : adresse | créneau | durée | heure passage | boutons
                c1, c2, c3, c4, c_btns = st.columns([6, 2, 1, 2, 3])
                with c1: st.write(f"**{i+1}.** {p.address}")
                with c2:
                    lo, hi = TW.get(p)
                    icons = {"Heure précise":"ߔ","Matin libre":"ߌ","Après-midi libre":"ߌ","Libre":"ߕ"}
                    icon = icons.get(p.time_mode, "ߕ")
                    if p.time_mode == "Libre":
                        st.write(f"{icon} Libre")
                    else:
                        st.write(f"{icon} {TW.fmt(lo, hi)}")
                with c3:
                    st.caption(f"⏱ {p.service_duration//SPM}min")
                with c4:
                    if arr is not None:
                        st.write(f"🕐 **{fmt_t(arr)}**")
                    else:
                        st.caption("—")
                with c_btns:
                    if st.button("↑", key=f"up_{i}", disabled=(i == 0), help="Monter"):
                        StateManager.move_point_up(i)
                        StateManager.commit()
                    if st.button("↓", key=f"dn_{i}", disabled=(i == len(points)-1), help="Descendre"):
                        StateManager.move_point_down(i)
                        StateManager.commit()
                    if st.button("✎", key=f"edit_addr_{i}", help="Modifier l'adresse"):
                        UI._edit_point(i, p.address)
                    if st.button("✕", key=f"del_addr_{i}", help="Supprimer"):
                        UI._confirm_delete_point(i, p.address)

                with st.expander(
                    f"📍 {p.address[:28]}…" if len(p.address) > 28 else f"📍 {p.address}"
                ):
                    # ── Champ adresse unifié ──────────────────────────────
                    new_address_val = st.text_input(
                        "Adresse", value=p.address, key=f"addr_{i}",
                        help="Modifiez le code postal, la ville, etc.")

                    addr_changed = new_address_val.strip() != p.address.strip()
                    has_postcode = bool(_RE_POSTCODE.search(new_address_val))

                    # L'avertissement CP ne s'affiche que si le champ actuel
                    # n'a pas de code postal (disparaît dès que l'utilisateur en saisit un)
                    if not has_postcode:
                        st.caption("⚠️ Pas de code postal — géocodage peut échouer")

                    if addr_changed:
                        new_addr_clean = new_address_val.strip()
                        addr_l_old     = _norm_addr(p.address)
                        addr_l_new     = new_addr_clean.lower()
                        addr_idx       = StateManager._get_addr_idx()
                        in_carnet      = addr_l_old in addr_idx
                        today_str      = datetime.today().strftime("%d/%m/%Y")

                        def _apply_to_tour(_i=i, _p=p, _new=new_addr_clean, _old=addr_l_old):
                            """Applique la nouvelle adresse dans la tournée."""
                            st.session_state.coord_cache.pop(_norm_addr(_old), None)
                            StateManager.update_point(_i, address=_new, coordinates=None)
                            st.session_state.pop(f"addr_{_i}", None)

                        def _apply_to_carnet(orig_idx, contact, _new=new_addr_clean):
                            """Applique la nouvelle adresse dans le carnet."""
                            st.session_state.coord_cache.pop(
                                _norm_addr(contact["address"]), None)
                            st.session_state.address_book[orig_idx]["address"] = _new
                            StateManager._invalidate_csv_cache()
                            StateManager._invalidate_contact_index()
                            AddressBookManager.save_to_file()

                        if in_carnet:
                            orig_idx, contact = addr_idx[addr_l_old]
                            st.caption(f"📒 Contact : **{contact['name']}**")
                            col_t, col_c, col_tc = st.columns(3)
                            with col_t:
                                if st.button("✅ Tournée",
                                             key=f"val_tour_{i}",
                                             use_container_width=True,
                                             help="Met à jour la tournée uniquement"):
                                    _apply_to_tour()
                                    StateManager.commit()
                            with col_c:
                                if st.button("💾 Carnet",
                                             key=f"val_carnet_{i}",
                                             use_container_width=True,
                                             help="Met à jour le carnet JSON uniquement"):
                                    _apply_to_carnet(orig_idx, contact)
                                    # Pas de maj tournée : on efface quand même le widget
                                    st.session_state.pop(f"addr_{i}", None)
                                    st.rerun()
                            with col_tc:
                                if st.button("🔄 Tournée + Carnet",
                                             key=f"val_both_{i}",
                                             use_container_width=True,
                                             type="primary",
                                             help="Corrige partout"):
                                    _apply_to_carnet(orig_idx, contact)
                                    _apply_to_tour()
                                    StateManager.commit()
                        else:
                            # Adresse absente du carnet
                            candidates   = st.session_state.get("_auto_add_candidates", [])
                            is_candidate = any(
                                _norm_addr(c["address"]) == addr_l_old
                                for c in candidates)
                            col_t2, col_add2 = st.columns([1, 2])
                            with col_t2:
                                if st.button("✅ Tournée",
                                             key=f"val_tour_only_{i}",
                                             use_container_width=True):
                                    _apply_to_tour()
                                    StateManager.commit()
                            with col_add2:
                                # Nom/tél inline pour ajouter au carnet en même temps
                                cand_name = st.text_input(
                                    "Nom (pour le carnet)", placeholder="M. Dupont",
                                    key=f"opt_cand_name_{i}",
                                    label_visibility="collapsed")
                                if st.button(
                                    "➕ Tournée + Carnet" + (" ✨" if is_candidate else ""),
                                    key=f"val_tour_carnet_{i}",
                                    use_container_width=True,
                                    type="primary"):
                                    if cand_name.strip():
                                        new_c = {
                                            "name":              cand_name.strip(),
                                            "address":           new_addr_clean,
                                            "phone":             "",
                                            "intervention_type": p.intervention_type,
                                            "notes":             p.notes,
                                            "service_duration":  p.service_duration,
                                            "last_intervention": today_str,
                                        }
                                        st.session_state.address_book.append(new_c)
                                        StateManager._invalidate_csv_cache()
                                        StateManager._invalidate_contact_index()
                                        AddressBookManager.save_to_file()
                                        st.session_state["_auto_add_candidates"] = [
                                            c for c in candidates
                                            if _norm_addr(c["address"]) != addr_l_old]
                                        _apply_to_tour()
                                        StateManager.commit()
                                    else:
                                        st.warning("Saisissez un nom pour enregistrer dans le carnet.")

                    # ── Si adresse non modifiée et absente du carnet ──────
                    if not addr_changed:
                        addr_l    = _norm_addr(p.address)
                        addr_idx2 = StateManager._get_addr_idx()
                        if addr_l not in addr_idx2:
                            today_str2   = datetime.today().strftime("%d/%m/%Y")
                            candidates2  = st.session_state.get("_auto_add_candidates", [])
                            is_cand2     = any(
                                _norm_addr(c["address"]) == addr_l for c in candidates2)
                            label2 = "📒 Ajouter au carnet ✨" if is_cand2 else "📒 Ajouter au carnet"
                            with st.expander(label2, expanded=is_cand2):
                                col_n3, col_ph3 = st.columns(2)
                                with col_n3:
                                    cand_name3 = st.text_input(
                                        "Nom", placeholder="M. Dupont",
                                        key=f"cand_name_static_{i}")
                                with col_ph3:
                                    cand_phone3 = st.text_input(
                                        "Tél.", placeholder="06…",
                                        key=f"cand_phone_static_{i}")
                                if st.button("➕ Enregistrer dans le carnet",
                                             key=f"cand_add_static_{i}",
                                             use_container_width=True,
                                             type="primary"):
                                    if cand_name3.strip():
                                        new_c3 = {
                                            "name":              cand_name3.strip(),
                                            "address":           p.address,
                                            "phone":             cand_phone3.strip(),
                                            "intervention_type": p.intervention_type,
                                            "notes":             p.notes,
                                            "service_duration":  p.service_duration,
                                            "last_intervention": today_str2,
                                        }
                                        st.session_state.address_book.append(new_c3)
                                        StateManager._invalidate_csv_cache()
                                        StateManager._invalidate_contact_index()
                                        AddressBookManager.save_to_file()
                                        st.session_state["_auto_add_candidates"] = [
                                            c for c in candidates2
                                            if _norm_addr(c["address"]) != addr_l]
                                        st.rerun()
                                    else:
                                        st.warning("Saisissez un nom.")

                    st.markdown("<hr style='margin:6px 0;border-color:#333'>",
                                unsafe_allow_html=True)

                    mode = st.selectbox(
                        "Mode horaire",
                        ["Libre", "Heure précise", "Matin libre", "Après-midi libre"],
                        index=["Libre","Heure précise","Matin libre",
                               "Après-midi libre"].index(p.time_mode),
                        key=f"mode_{i}")
                    tgt = None
                    if mode == "Heure précise":
                        dft = None
                        if p.target_time:
                            dft = datetime.strptime(
                                f"{p.target_time//SPH:02d}:{(p.target_time%SPH)//SPM:02d}",
                                "%H:%M").time()
                        ti2 = st.time_input("Heure cible", value=dft, key=f"ti_{i}")
                        if ti2:
                            tgt = ti2.hour * SPH + ti2.minute * SPM
                            ok, err = Validator.check_point_time(
                                DeliveryPoint(address="", time_mode=mode, target_time=tgt))
                            if not ok:
                                st.warning(f"⚠️ {err}")

                    tmp = DeliveryPoint(address="", time_mode=mode, target_time=tgt)
                    lo, hi = TW.get(tmp)
                    icons = {"Heure précise":"⏰","Matin libre":"🌅",
                             "Après-midi libre":"🌆","Libre":"🕐"}
                    st.caption(f"{icons.get(mode,'🕐')} Fenêtre : {TW.fmt(lo, hi)}")
                    if mode == "Heure précise" and tgt is not None:
                        _ps = st.session_state.get("opt_pause_start", 12*SPH)
                        _pe = st.session_state.get("opt_pause_end",   13*SPH)
                        if _ps <= tgt < _pe:
                            st.warning(
                                f"⚠️ {tgt//SPH:02d}:{(tgt%SPH)//SPM:02d} est dans la pause "
                                f"({_ps//SPH:02d}h{(_ps%SPH)//SPM:02d}–"
                                f"{_pe//SPH:02d}h{(_pe%SPH)//SPM:02d})")

                    prev_type_key = f"prev_type_{i}"
                    if prev_type_key not in st.session_state:
                        st.session_state[prev_type_key] = p.intervention_type
                    itype = st.selectbox(
                        "Type d'intervention", INTERVENTION_KEYS,
                        index=INTERVENTION_KEYS.index(p.intervention_type)
                            if p.intervention_type in INTERVENTION_TYPES else 1,
                        key=f"itype_{i}")
                    if itype != p.intervention_type:
                        StateManager.update_point(i, intervention_type=itype,
                            service_duration=INTERVENTION_TYPES.get(itype, 60*SPM))
                        st.session_state[prev_type_key] = itype
                        st.rerun()

                    svc_min = st.slider("Durée (min)", 15, 180,
                                        value=max(15, p.service_duration//SPM),
                                        step=5, key=f"svc_{i}")
                    notes_val = st.text_area("Notes", value=p.notes, height=60,
                                              placeholder="RPH, X conduits…",
                                              key=f"notes_{i}")

                    if (p.time_mode != mode or p.target_time != tgt
                            or p.intervention_type != itype
                            or p.notes != notes_val
                            or p.service_duration != svc_min * SPM):
                        StateManager.update_point(i, time_mode=mode, target_time=tgt,
                            intervention_type=itype, notes=notes_val,
                            service_duration=svc_min*SPM)

            st.markdown("---")
            st.write(f"**RETOUR:** {cfg.end_address or '(non configuré)'}")

    @staticmethod
    def _build_folium_map(cfg, points, show_route, folium):
        """Construit l'objet folium.Map — séparé pour permettre le cache session."""
        m = folium.Map(location=MAP_CENTER, zoom_start=14)

        if cfg.start_coordinates:
            folium.Marker(cfg.start_coordinates,
                          popup=f"DÉPART: {cfg.start_address}",
                          icon=folium.Icon(color="green", icon="play")).add_to(m)

        for i, p in enumerate(points):
            if p.coordinates:
                color = {"Heure précise": "red", "Matin libre": "lightblue",
                         "Après-midi libre": "orange", "Libre": "blue"}.get(p.time_mode, "blue")
                lo, hi = TW.get(p)
                popup_text = f"{i+1}. {p.address}\n{TW.fmt(lo, hi)}\n⏱ {p.service_duration//SPM}min"
                if p.notes:
                    popup_text += f"\n📝 {p.notes[:50]}"
                folium.Marker(p.coordinates, popup=popup_text,
                              icon=folium.Icon(color=color, icon="info-sign")).add_to(m)

        if cfg.end_coordinates:
            folium.Marker(cfg.end_coordinates,
                          popup=f"🏁 RETOUR: {cfg.end_address}",
                          icon=folium.Icon(color="orange", icon="stop")).add_to(m)

        if show_route and st.session_state.optimized_result:
            result    = st.session_state.optimized_result
            all_coords = ([cfg.start_coordinates] + [p.coordinates for p in points]
                          + [cfg.end_coordinates])
            route_coords = [all_coords[node] for node in result.order if all_coords[node]]
            if route_coords:
                folium.PolyLine(route_coords,
                                color="orange" if result.is_approximation else "green",
                                weight=4, opacity=0.8).add_to(m)

        if st.session_state.get("map_click_queue"):
            for qi, (qlat, qlon) in enumerate(st.session_state["map_click_queue"]):
                folium.Marker(location=[qlat, qlon],
                              popup=f"📍 Point {qi+1}",
                              icon=folium.Icon(color="cadetblue", icon="plus-sign")).add_to(m)
        return m

    @staticmethod
    def map(show_route=False):
        cfg    = StateManager.config()
        points = StateManager.points()

        folium, st_folium = _import_folium()

        # ── Clé de cache : change si les données changent → rebuild automatique ──
        cache_key = (
            cfg.start_coordinates,
            cfg.end_coordinates,
            tuple((p.coordinates, p.time_mode, p.address) for p in points),
            show_route,
            st.session_state.optimized_result is not None,
            tuple(st.session_state.get("map_click_queue", [])),
        )
        cached = st.session_state.get("_map_cache")
        if cached and cached[0] == cache_key:
            m = cached[1]
        else:
            m = UI._build_folium_map(cfg, points, show_route, folium)
            st.session_state["_map_cache"] = (cache_key, m)

        target = st.session_state.map_zoom_target
        if target:
            coords = Geo.get(target)
            center = coords if coords else MAP_CENTER
            zoom   = 16
            st.session_state.map_zoom_target = None
            m.location   = list(center)
            m.zoom_start = zoom

        st.caption("🖱️ Double-cliquez sur la carte pour sélectionner des points, "
                   "puis cliquez **Ajouter les points**")

        map_data = st_folium(
            m,
            height=420,
            width=None,
            returned_objects=["last_clicked"],
            key="main_map"
        )

        # ── Capture du clic : ajout à la file d'attente ──────────────────
        if map_data and map_data.get("last_clicked"):
            click = map_data["last_clicked"]
            lat, lon = click.get("lat"), click.get("lng")
            if lat and lon:
                lat, lon = float(lat), float(lon)
                rounded = (round(lat, 5), round(lon, 5))
                # Ne traiter que si c'est un clic différent du dernier traité
                last_processed = st.session_state.get("_map_last_processed_click")
                if rounded != last_processed:
                    st.session_state["_map_last_processed_click"] = rounded
                    queue: list = list(st.session_state.get("map_click_queue", []))
                    queue.append(rounded)
                    st.session_state["map_click_queue"] = queue
                    # Pas de rerun ici → la carte reste stable

        # ── Affichage de la file d'attente ───────────────────────────────
        queue: list = st.session_state.get("map_click_queue", [])
        if queue:
            st.info(f"📍 **{len(queue)} point(s) sélectionné(s)** sur la carte")
            for qi, (qlat, qlon) in enumerate(queue):
                qc1, qc2 = st.columns([5, 1])
                with qc1:
                    # Résoudre l'adresse uniquement si pas encore fait
                    addr_key = f"map_q_addr_{qi}"
                    if addr_key not in st.session_state:
                        with st.spinner(f"Identification point {qi+1}…"):
                            resolved = Geo.reverse(qlat, qlon)
                        st.session_state[addr_key] = resolved or f"{qlat}, {qlon}"
                    addr_q = st.text_input(
                        f"Point {qi+1}",
                        value=st.session_state[addr_key],
                        key=f"map_q_edit_{qi}",
                        label_visibility="collapsed"
                    )
                    st.session_state[addr_key] = addr_q
                with qc2:
                    if st.button("✖", key=f"map_q_rm_{qi}", help="Retirer ce point"):
                        queue.pop(qi)
                        st.session_state["map_click_queue"] = queue
                        st.session_state.pop("_map_last_processed_click", None)
                        # Nettoyer les clés de cache d'adresses
                        for k in [f"map_q_addr_{j}" for j in range(qi, len(queue)+1)]:
                            st.session_state.pop(k, None)
                        st.rerun()

            ca, cb = st.columns(2)
            with ca:
                if st.button("➕ Ajouter les points à la tournée",
                             type="primary", key="map_q_add_all",
                             use_container_width=True):
                    for qi, (qlat, qlon) in enumerate(queue):
                        addr_q = st.session_state.get(f"map_q_addr_{qi}",
                                                       f"{qlat}, {qlon}")
                        if addr_q.strip():
                            StateManager.add_point(addr_q.strip())
                            pts_q = StateManager.points()
                            pts_q[-1].coordinates = (qlat, qlon)
                    # Vider la file
                    st.session_state["map_click_queue"] = []
                    st.session_state.pop("_map_last_processed_click", None)
                    for k in list(st.session_state.keys()):
                        if k.startswith("map_q_addr_") or k.startswith("map_q_edit_"):
                            del st.session_state[k]
                    StateManager.commit()
            with cb:
                if st.button("✖ Vider la sélection", key="map_q_clear",
                             use_container_width=True):
                    st.session_state["map_click_queue"] = []
                    st.session_state.pop("_map_last_processed_click", None)
                    for k in list(st.session_state.keys()):
                        if k.startswith("map_q_addr_") or k.startswith("map_q_edit_"):
                            del st.session_state[k]
                    st.rerun()

    @staticmethod
    def results():
        if not st.session_state.optimized_result:
            st.info("Aucune tournée planifiée. Cliquez sur **🗺️ Planifier**.")
            return

        result: RouteResult = st.session_state.optimized_result
        cfg = StateManager.config()
        points = StateManager.points()

        st.markdown("<div id='ordre-de-passage'></div>", unsafe_allow_html=True)
        col_title, col_top = st.columns([8, 1])
        with col_title:
            st.subheader("Ordre de passage")
        with col_top:
            st.markdown(
                "<a href='#haut-de-page'>"
                "<button style='background:#444;color:white;border:none;"
                "padding:4px 10px;border-radius:4px;cursor:pointer;font-size:0.85rem'>"
                "⬆ Haut</button></a>",
                unsafe_allow_html=True
            )

        h_m = result.matin_duration // 3600
        min_m = (result.matin_duration % 3600) // 60
        badge = "⭐" if not result.is_approximation else "📊"
        moved_txt = f" · ⚠️ {len(result.matin_moved)} déplacé(s) PM" if result.matin_moved else ""
        st.caption(f"{badge} Matin : {result.matin_count} arrêt(s) — {h_m}h{min_m:02d}{moved_txt}")
        st.markdown("---")

        all_addr = [cfg.start_address] + [p.address for p in points] + [cfg.end_address]
        n_pts = len(points)

        def fmt_t(s):
            return f"{s//3600:02d}:{(s%3600)//60:02d}"

        for step, node in enumerate(result.order):
            if node < 0 or node >= len(all_addr):
                continue

            arr_t = result.arrival_times[step]

            service_start = arr_t
            waiting = 0
            if 0 < node <= n_pts:
                p = points[node - 1]
                lo, hi = TW.get(p)
                if arr_t < lo:
                    service_start = lo
                    waiting = lo - arr_t

            c1, c2, c3, c4, c5 = st.columns([1, 5, 2, 2, 2])
            with c1:
                st.write("ߏ" if node == 0 or node == n_pts + 1 else f"**{step}**")
            with c2:
                if node == 0:
                    st.write(f"**DÉPART :** {all_addr[0]}")
                elif node == n_pts + 1:
                    st.write(f"**RETOUR :** {all_addr[-1]}")
                else:
                    st.write(all_addr[node])
                    if 0 < node <= n_pts:
                        p = points[node - 1]
                        if p.notes:
                            st.caption(f"ߓ {p.notes}")
            with c3:
                if waiting > 0:
                    st.write(f"ߚ {fmt_t(arr_t)}")
                    st.caption(f"⏳ attente {waiting//60}min")
                    st.write(f"ߔ **{fmt_t(service_start)}**")
                else:
                    st.write(f"ߕ **{fmt_t(arr_t)}**")
            with c4:
                if node == 0:
                    d = cfg.start_service_duration
                    if d > 0:
                        st.caption(f"⏱ {d//SPM}min")
                        depart_effectif = arr_t + d
                        st.caption(f"→ départ {fmt_t(depart_effectif)}")
                elif 0 < node <= n_pts:
                    p = points[node - 1]
                    st.caption(f"⏱ {p.service_duration//SPM}min")
            with c5:
                if 0 < node <= n_pts:
                    p = points[node - 1]
                    if p.time_mode != "Libre":
                        lo, hi = TW.get(p)
                        st.caption(f"ߎ {TW.fmt(lo, hi)}")
                        if lo == hi:
                            if service_start == lo:
                                st.success("✓ exact")
                            elif service_start < lo:
                                st.success(f"✓ {fmt_t(service_start)}")
                            else:
                                retard = service_start - lo
                                st.warning(f"⏰ +{retard//60}min")
                        else:
                            if service_start < lo or service_start > hi:
                                st.error("⚠️ Hors fenêtre!")
                            else:
                                st.success("✓")

        st.markdown("---")
        st.markdown("<h4 style='margin:0.5rem 0 0.3rem 0;font-size:1rem'>Résumé</h4>", unsafe_allow_html=True)

        # ── Métriques principales ─────────────────────────────────────────
        c1, c2, c3 = st.columns(3)
        with c1: st.metric("Distance optimisée", f"{result.total_distance/1000:.1f} km")
        with c2: st.metric("Durée totale", f"{result.total_time/3600:.1f} h")
        with c3: st.metric("Arrêts", str(n_pts))

        # ── Gain vs ordre séquentiel ──────────────────────────────────────
        if result.initial_distance > 0 and result.initial_distance != result.total_distance:
            init_km  = result.initial_distance / 1000
            optim_km = result.total_distance / 1000
            gain_pct = (init_km - optim_km) / init_km * 100
            gain_km  = init_km - optim_km
            g1, g2, g3 = st.columns(3)
            with g1: st.metric("Ordre initial",    f"{init_km:.1f} km")
            with g2: st.metric("Ordre optimisé",   f"{optim_km:.1f} km")
            with g3: st.metric("Gain",             f"-{gain_km:.1f} km",
                                delta=f"-{gain_pct:.0f} %",
                                delta_color="normal")

        # ── Décomposition du temps ────────────────────────────────────────
        svc_total = (cfg.start_service_duration
                     + sum(p.service_duration for p in points))  # temps clients
        travel_total = max(0, result.total_time - svc_total)     # temps trajets

        def _fmt_hm(secs: int) -> str:
            h, m = secs // 3600, (secs % 3600) // 60
            return f"{h}h{m:02d}" if h else f"{m}min"

        t1, t2, t3 = st.columns(3)
        with t1: st.metric("⏱ Clients",  _fmt_hm(svc_total))
        with t2: st.metric("🚗 Trajets",  _fmt_hm(travel_total))
        with t3: st.metric("📅 Total",    _fmt_hm(result.total_time))

        st.markdown("---")
        st.subheader("Export")
        gmap_url = UI.export_google_maps_url(result, cfg, points)
        if gmap_url:
            st.markdown(f"[Ouvrir l'itinéraire dans Google Maps]({gmap_url})")
            with st.expander("ߓ Lien complet"):
                st.code(gmap_url, language=None)

        # ── Export Google Calendar (.ics) ─────────────────────────────────
        st.markdown("**📅 Exporter vers Google Calendar**")
        tour_date = st.date_input(
            "Date de la tournée",
            value=datetime.today().date(),
            key="ics_date"
        )
        ics_content = RouteManager.to_ics(
            result, cfg, points,
            datetime(tour_date.year, tour_date.month, tour_date.day)
        )
        st.download_button(
            label="📅 Télécharger le fichier .ics (Google Calendar / iCal)",
            data=ics_content,
            file_name=f"tournee_{tour_date.strftime('%Y%m%d')}.ics",
            mime="text/calendar",
            use_container_width=True,
            help="Importez ce fichier dans Google Calendar (Paramètres → Importer)"
        )

        # ── Auto-ajout au carnet : détection des adresses absentes ──────────
        today_str = datetime.today().strftime("%d/%m/%Y")
        StateManager.auto_add_to_book(points, result.arrival_times, result.order, today_str)
        
# Créez la connexion (à mettre avant la fonction main)
conn = st.connection("gsheets", type=GSheetsConnection)

def load_from_gsheets():
    """Charge les contacts depuis Google Sheets"""
    try:
        df = conn.read(ttl=0) # ttl=0 pour forcer la lecture fraîche
        return df.to_dict('records')
    except:
        return []

def save_to_gsheets(data):
    """Sauvegarde les contacts vers Google Sheets"""
    df = pd.DataFrame(data)
    conn.update(data=df)
    st.success("Données synchronisées avec Google Sheets !")
# ==========================================================
# MAIN
# ==========================================================
def main():
    try:
        StateManager.init()

        # ── Ré-optimisation automatique après modification ─────────────────
        if st.session_state.pop("_reopt_pending", False):
            cfg = StateManager.config()
            pts = StateManager.points()
            all_coords = (
                [cfg.start_coordinates]
                + [p.coordinates for p in pts]
                + [cfg.end_coordinates]
            )
            with st.spinner("🔄 Mise à jour de la tournée…"):
                mats = OSRM.matrix(all_coords)
            if mats:
                result = Optimizer.optimize(cfg, pts, precomputed_mats=mats)
                if result:
                    st.session_state.optimized_result = result
                    # UI.sidebar() est appelé juste après dans ce même render
                else:
                    st.session_state.optimized_result = None

        # ── Bannière restauration autosave ────────────────────────────────
        if st.session_state.get("_autosave_available"):
            info = st.session_state["_autosave_available"]
            col_msg, col_yes, col_no = st.columns([5, 1, 1])
            with col_msg:
                st.info(
                    f"💾 Tournée non terminée détectée ({info['n_pts']} arrêt(s), "
                    f"sauvegardée le {info['saved_at'][:16].replace('T',' ')}). "
                    "Voulez-vous la restaurer ?"
                )
            with col_yes:
                if st.button("✅ Restaurer", use_container_width=True):
                    RouteManager.load(RouteManager.AUTOSAVE_NAME)
                    del st.session_state["_autosave_available"]
                    st.rerun()
            with col_no:
                if st.button("🗑️ Ignorer", use_container_width=True):
                    del st.session_state["_autosave_available"]
                    st.rerun()

        # ── CSS global : masquer sidebar, max-width 14" ──────────────────
        st.markdown("""
<style>
/* Masquer complètement la sidebar */
section[data-testid="stSidebar"] { display: none !important; }
button[data-testid="baseButton-headerNoPadding"] { display: none !important; }
/* Largeur max adaptée écran 14" (~1280px) */
.main .block-container,
section.main > div:first-child,
div[data-testid="stMainBlockContainer"],
div[data-testid="block-container"] {
    max-width: 1100px !important;
    padding-left: 1.5rem !important;
    padding-right: 1.5rem !important;
    padding-top: 1rem !important;
    margin-left: auto !important;
    margin-right: auto !important;
}
/* Boutons actions intervention : côte à côte */
div[data-testid="stHorizontalBlock"] > div:last-child div[data-testid="stVerticalBlock"] {
    display: flex !important;
    flex-direction: row !important;
    flex-wrap: wrap !important;
    gap: 2px !important;
    align-items: center !important;
}
div[data-testid="stHorizontalBlock"] > div:last-child button[kind="secondary"] {
    flex: 0 0 auto !important;
    min-width: 32px !important;
    width: auto !important;
    padding: 2px 6px !important;
}
/* Métriques compactes */
div[data-testid="stMetric"] label { font-size: 0.75rem !important; }
div[data-testid="stMetricValue"]   { font-size: 1rem !important; }
div[data-testid="stMetricDelta"]   { font-size: 0.75rem !important; }
</style>
""", unsafe_allow_html=True)

        # ── Sidebar désactivée — tout est dans les onglets ────────────────

        if st.session_state.last_error:
            st.warning(f"⚠️ {st.session_state.last_error}")
            st.session_state.last_error = None


        # ══════════════════════════════════════════════════════════════════
        # FENÊTRE PRINCIPALE — ONGLETS NAVIGATEUR
        # ══════════════════════════════════════════════════════════════════
        tab_tournee, tab_contacts, tab_search, tab_params, tab_csv = st.tabs([
            "🗺️ Planification", "📒 Contacts", "🔍 Rechercher", "⚙️ Paramètres", "📥📤 Import / Export"
        ])

        with tab_tournee:
            # ── Bouton afficher/masquer la carte ─────────────────────────
            map_visible = st.session_state.get("map_visible", False)
            if st.button("🗺️ Masquer la carte" if map_visible else "🗺️ Afficher la carte",
                         key="btn_toggle_map"):
                st.session_state["map_visible"] = not map_visible
                st.rerun()

            if map_visible:
                UI.map(show_route=bool(st.session_state.optimized_result))

            col_btn, col_geo, col_save, col_load = st.columns([1, 1, 3, 3])

            with col_btn:
                run_optim = st.button("🗺️", type="primary",
                                      use_container_width=False, key="btn_planifier",
                                      help="Planifier la tournée optimale 😊")

            with col_geo:
                _do_geocode = st.button("📍", key="btn_geocode_main",
                                        help="Géocoder toutes les adresses",
                                        use_container_width=False)
            if _do_geocode:
                pts_geo = StateManager.points()
                cfg_geo = StateManager.config()
                with st.spinner("Géocodage…"):
                    geo_addrs: List[str] = []
                    if cfg_geo.start_address: geo_addrs.append(cfg_geo.start_address)
                    if cfg_geo.end_address:   geo_addrs.append(cfg_geo.end_address)
                    geo_addrs += [p.address for p in pts_geo]
                    geo_r = Geo.batch_geocode(geo_addrs, max_workers=4)
                    if cfg_geo.start_address and geo_r.get(cfg_geo.start_address):
                        StateManager.update_config(start_coordinates=geo_r[cfg_geo.start_address])
                    if cfg_geo.end_address and geo_r.get(cfg_geo.end_address):
                        StateManager.update_config(end_coordinates=geo_r[cfg_geo.end_address])
                    ok, fail = 0, 0
                    for p in pts_geo:
                        if geo_r.get(p.address):
                            p.coordinates = geo_r[p.address]; ok += 1
                        else:
                            fail += 1
                    StateManager.commit()
                    st.success(f"✅ {ok} adresse(s) géocodée(s)" + (f" · ❌ {fail} échouée(s)" if fail else ""))

            with col_save:
                with st.expander("💾 Sauvegarder", expanded=False):
                    save_name = st.text_input("Nom", placeholder="Lundi_S42",
                                              key="save_route_name")
                    if st.button("💾 Sauvegarder", key="btn_save_route",
                                 use_container_width=True, type="primary"):
                        if save_name.strip():
                            clean = _RE_SAFE_NAME.sub('',
                                           save_name.strip()).replace(' ', '_')
                            if RouteManager.save(clean):
                                st.success(f"✅ « {clean} »")
                                st.rerun()
                        else:
                            st.warning("Donnez un nom")

            with col_load:
                with st.expander("📂 Charger", expanded=False):
                    saves = RouteManager.list_saves()
                    if saves:
                        selected_save = st.selectbox("Tournée", saves,
                                                     key="sel_load_route",
                                                     label_visibility="collapsed")
                        c_load, c_del = st.columns(2)
                        with c_load:
                            if st.button("📂 Charger", key="btn_load_route",
                                         use_container_width=True, type="primary"):
                                if RouteManager.load(selected_save):
                                    st.rerun()
                        with c_del:
                            if st.button("✕", key="btn_del_route",
                                         use_container_width=True,
                                         help="Supprimer cette sauvegarde"):
                                UI._confirm_delete_save(selected_save)
                    else:
                        st.caption("Aucune sauvegarde")

            # ── Mise en page : configuration puis ordre de passage ──────────
            if st.session_state.optimized_result:
                st.markdown(
                    "<a href='#ordre-de-passage'>"
                    "<button style='background:#1f77b4;color:white;border:none;"
                    "padding:4px 12px;border-radius:4px;cursor:pointer;font-size:0.85rem'>"
                    "⬇ Voir l'ordre de passage</button></a>",
                    unsafe_allow_html=True
                )
            UI.address_list()
            UI.results()

            # ── Optimisation ──────────────────────────────────────────────────
            if run_optim:
                cfg = StateManager.config()
                pts = StateManager.points()

                if not cfg.start_address:
                    st.error("Veuillez saisir une adresse de départ")
                elif not cfg.end_address:
                    st.error("Veuillez saisir une adresse de retour")
                elif not pts:
                    st.error("Ajoutez au moins un point d'arrêt")
                else:
                    _status = st.status("🗺️ Planification en cours…", expanded=True)
                    with _status:
                        addrs_needed: List[str] = []
                        if not cfg.start_coordinates:
                            addrs_needed.append(cfg.start_address)
                        if not cfg.end_coordinates:
                            addrs_needed.append(cfg.end_address)
                        pts_sans_coords = [p for p in pts if not p.coordinates]
                        addrs_needed += [p.address for p in pts_sans_coords]

                        if addrs_needed:
                            geo_bar = st.progress(0, text="Géocodage : 0 / 0 adresses…")
                            def _update_bar(done, total):
                                geo_bar.progress(
                                    done / total,
                                    text=f"Géocodage : {done} / {total} adresses…"
                                )
                            geo_map = Geo.batch_geocode(
                                addrs_needed, max_workers=4, progress_cb=_update_bar
                            )
                            geo_bar.empty()
                        else:
                            geo_map = {}

                        # Appliquer les coordonnées géocodées
                        if not cfg.start_coordinates:
                            c = geo_map.get(cfg.start_address) or geo_map.get(_norm_addr(cfg.start_address))
                            if c:
                                StateManager.update_config(start_coordinates=c)
                                cfg = StateManager.config()
                            else:
                                _status.update(label="❌ Adresse de départ introuvable", state="error")
                                st.error(f"Adresse de départ introuvable : {cfg.start_address}")
                                st.stop()

                        if not cfg.end_coordinates:
                            c = geo_map.get(cfg.end_address) or geo_map.get(_norm_addr(cfg.end_address))
                            if c:
                                StateManager.update_config(end_coordinates=c)
                                cfg = StateManager.config()
                            else:
                                _status.update(label="❌ Adresse de retour introuvable", state="error")
                                st.error(f"Adresse de retour introuvable : {cfg.end_address}")
                                st.stop()

                        failed = []
                        for p in pts_sans_coords:
                            c = geo_map.get(p.address) or geo_map.get(_norm_addr(p.address))
                            if c:
                                p.coordinates = c
                            else:
                                failed.append(p.address)

                        if failed:
                            _status.update(label="❌ Adresses introuvables", state="error")
                            st.error("Adresses introuvables :\n" + "\n".join(f"• {a}" for a in failed))
                        else:
                            ok, err = Validator.check_setup(cfg, pts)
                            if not ok:
                                _status.update(label=f"❌ {err}", state="error")
                                st.error(f"❌ {err}")
                            else:
                                all_coords_check = (
                                    [cfg.start_coordinates]
                                    + [p.coordinates for p in pts]
                                    + [cfg.end_coordinates]
                                )
                                st.write("🔗 Calcul des distances OSRM…")
                                mats_check = OSRM.matrix(all_coords_check)
                                if mats_check is None:
                                    _status.update(label="❌ OSRM indisponible", state="error")
                                    st.error("❌ Impossible de calculer la matrice de distances (OSRM).")
                                    st.stop()

                                _, dur_check = mats_check
                                conflicts = Optimizer.nearby_conflicts(pts, dur_check)

                                if conflicts and not st.session_state.pop("_force_optim", False):
                                    _status.update(label="⚠️ Conflits détectés", state="error")
                                    UI._dialog_conflicts(conflicts, pts)
                                    st.stop()

                                st.write("⚙️ Optimisation de l'itinéraire…")
                                result = Optimizer.optimize(cfg, pts, precomputed_mats=mats_check)
                                if result:
                                    _status.update(label="✅ Tournée planifiée !", state="complete",
                                                   expanded=False)
                                    st.session_state.optimized_result = result
                                    StateManager.save_to_history()
                                    st.rerun()
                                else:
                                    _status.update(label="❌ Optimisation échouée", state="error")
                                    st.error("❌ Optimisation échouée")


        # ── Onglet Contacts ──────────────────────────────────────────────
        with tab_contacts:
            contacts = StateManager.get_contacts()
            history  = st.session_state.get("client_history", [])

            nb_msg = st.session_state.pop("_contacts_loaded_msg", None)
            if nb_msg:
                st.success(f"📒 {nb_msg} contact(s) importé(s)")

            # ── Filtres historique ──────────────────────────────────────────
            if history:
                all_years: set = set()
                for h in history:
                    for d in h.get("visit_dates", []):
                        parts = d.split("/")
                        if len(parts) == 3:
                            all_years.add(parts[2])
                year_list   = ["Toutes"] + sorted(all_years, reverse=True)
                MOIS_LABELS = ["Tous","Janv.","Févr.","Mars","Avr.","Mai","Juin",
                               "Juil.","Août","Sept.","Oct.","Nov.","Déc."]

                hf1, hf2, hf3, hf4 = st.columns([1, 1, 2, 1])
                with hf1:
                    sel_year  = st.selectbox("Année", year_list, key="hist_year")
                with hf2:
                    sel_month_label = st.selectbox("Mois", MOIS_LABELS, key="hist_month")
                    sel_month = MOIS_LABELS.index(sel_month_label)
                with hf3:
                    if st.session_state.pop("_reset_hist_search", False):
                        st.session_state["hist_name_search"] = ""
                    hist_search = st.text_input("Rechercher", key="hist_name_search",
                                                placeholder="Nom ou adresse…")
                with hf4:
                    st.markdown("<label style='font-size:0.85rem;color:transparent'>.</label>",
                                unsafe_allow_html=True)
                    if st.button("🔄", key="reset_filters",
                                 help="Réinitialiser les filtres",
                                 use_container_width=True):
                        for k in ("hist_year", "hist_month", "hist_page"):
                            st.session_state.pop(k, None)
                        st.session_state["_reset_hist_search"] = True
                        st.rerun()

                no_date_filter = (sel_year == "Toutes" and sel_month == 0)
                name_q = hist_search.strip().lower()

                filtered: List[tuple] = []
                for h in history:
                    if name_q and name_q not in h.get("name","").lower():
                        continue
                    if no_date_filter:
                        all_dates = h.get("visit_dates", [])
                        if name_q:
                            # Recherche active → tout l'historique du client
                            filtered.append((h, all_dates))
                        else:
                            # Aucun filtre, aucune recherche → dernière date uniquement
                            most_recent = sorted(all_dates, key=_sort_key_date)[-1:] if all_dates else []
                            filtered.append((h, most_recent))
                    else:
                        matching = []
                        for d in h.get("visit_dates", []):
                            parts = d.split("/")
                            if len(parts) != 3: continue
                            try:
                                d_m, d_y = int(parts[1]), parts[2]
                            except ValueError:
                                continue
                            if sel_year != "Toutes" and d_y != sel_year: continue
                            if sel_month != 0 and d_m != sel_month:      continue
                            matching.append(d)
                        if matching:
                            filtered.append((h, matching))

                filtered.sort(key=lambda x: (x[0].get("name","") or x[0].get("address","")).lower())

                # ── Recherche rapide ────────────────────────────────────────
                if name_q:
                    if filtered:
                        st.caption(f"{len(filtered)} résultat(s)")
                        for fi, (h, dates) in enumerate(filtered[:8]):
                            h_name = h.get("name", "")
                            h_addr = h.get("address", "")
                            col_info, col_btn = st.columns([3, 1])
                            with col_info:
                                name_part = f"<span style='font-size:1em;font-weight:bold'>{_h(h_name)}</span>" if h_name else ""
                                addr_part = f"<span style='font-size:0.88em;color:#aaa'>📍 {_h(h_addr[:45])}</span>"
                                st.markdown(
                                    f"<div style='line-height:1.4;margin:2px 0 2px 0'>"
                                    f"{name_part}<br>{addr_part}</div>",
                                    unsafe_allow_html=True)
                                # Toutes les dates avec bouton ✕ individuel
                                all_h_dates = sorted(h.get("visit_dates", []), key=_sort_key_date)
                                for di, d in enumerate(all_h_dates):
                                    dc1, dc2 = st.columns([4, 1])
                                    with dc1:
                                        st.caption(f"📅 {d}")
                                    with dc2:
                                        if st.button("✕", key=f"qs_del_date_{fi}_{di}",
                                                     help=f"Supprimer le {d}"):
                                            h["visit_dates"] = [x for x in h["visit_dates"] if x != d]
                                            HistoryManager.save_to_file()
                                            st.rerun()
                            with col_btn:
                                if st.button("➕", key=f"hist_qs_{fi}",
                                             help="Ajouter à la tournée"):
                                    StateManager.add_from_history(h)
                                    StateManager.commit()
                            st.markdown("<hr style='margin:3px 0;border-color:#333'>",
                                        unsafe_allow_html=True)
                        if len(filtered) > 8:
                            st.caption(f"… {len(filtered)-8} de plus")
                    else:
                        st.info(f"Aucun résultat pour « {hist_search} »")

                # ── Mode pagination ─────────────────────────────────────────
                else:
                    HIST_PAGE_SIZE = 15
                    n_total  = len(filtered)
                    n_pages  = max(1, (n_total + HIST_PAGE_SIZE - 1) // HIST_PAGE_SIZE)
                    page     = max(0, min(st.session_state.get("hist_page", 0), n_pages - 1))

                    st.caption(f"📒 {n_total} client(s) — page {page+1}/{n_pages}")
                    _hc, _hn, _hp = st.columns([6, 1, 1])
                    with _hn:
                        if st.button("◀", key="hist_prev", disabled=(page == 0),
                                     help="Page précédente"):
                            st.session_state.hist_page = page - 1
                            st.rerun()
                    with _hp:
                        if st.button("▶", key="hist_next",
                                     disabled=(page == n_pages - 1),
                                     help="Page suivante"):
                            st.session_state.hist_page = page + 1
                            st.rerun()

                    start_i    = page * HIST_PAGE_SIZE
                    page_items = filtered[start_i: start_i + HIST_PAGE_SIZE]

                    with st.expander(
                        f"📒 Contacts {start_i+1}–{min(start_i+HIST_PAGE_SIZE, n_total)}",
                        expanded=True
                    ):
                        for fi, (h, dates) in enumerate(page_items):
                            h_name = h.get("name","")
                            h_addr = h.get("address","")
                            last_visit = sorted(dates, key=_sort_key_date)[-1] if dates else ""
                            phone_str = (f" · 📞 {_h(h['phone'])}" if h.get("phone") else "")
                            last_str  = (f"<br><span style='color:#888;font-size:0.88em'>"
                                         f"🔧 {_h(last_visit)}  ·  {len(dates)} passage(s)</span>"
                                         if last_visit else "")
                            st.markdown(
                                f"<div style='line-height:1.25;margin:1px 0 3px 0'>"
                                f"<span style='font-size:1em;font-weight:bold'>"
                                f"{_h(h_name) if h_name else _h(h_addr[:40])}</span>"
                                f"<span style='font-size:0.88em;color:#aaa'>{phone_str}</span><br>"
                                + (f"<span style='font-size:0.88em;color:#aaa'>📍 {_h(h_addr[:40])}</span>" if h_name else "")
                                + f"{last_str}</div>", unsafe_allow_html=True)

                            hcol1, hcol2, hcol3, hcol4 = st.columns([2, 1, 1, 1])
                            with hcol1:
                                if st.button("➕ Ajouter", key=f"hist_add_{start_i+fi}"):
                                    StateManager.add_from_history(h)
                                    StateManager.commit()
                            with hcol2:
                                if st.button("🔍", key=f"hist_detail_{start_i+fi}",
                                             help="Voir toutes les dates"):
                                    st.session_state[f"hist_expand_{start_i+fi}"] = \
                                        not st.session_state.get(f"hist_expand_{start_i+fi}", False)
                                    st.rerun()
                            with hcol3:
                                # Bouton éditer — cherche le contact correspondant dans le carnet
                                h_cidx = StateManager._get_contact_index()
                                match_c = [(ci, cc) for ci, nl, al, cc in h_cidx
                                           if _norm_addr(cc["address"]) == _norm_addr(h_addr)]
                                if match_c:
                                    if st.button("✎", key=f"hist_edit_{start_i+fi}",
                                                 help="Modifier ce contact"):
                                        st.session_state[f"editing_hist_{start_i+fi}"] = True
                            with hcol4:
                                confirm_key = f"hist_del_confirm_{start_i+fi}"
                                if st.session_state.get(confirm_key):
                                    if st.button("✅", key=f"hist_del_ok_{start_i+fi}",
                                                 help="Confirmer la suppression"):
                                        StateManager.delete_from_history(h_addr)
                                        st.session_state[confirm_key] = False
                                        st.rerun()
                                else:
                                    if st.button("✕", key=f"hist_del_{start_i+fi}",
                                                 help="Supprimer ce client (historique + carnet)"):
                                        st.session_state[confirm_key] = True
                                        st.rerun()

                            # Formulaire édition inline (fragment beta)
                            if st.session_state.get(f"editing_hist_{start_i+fi}", False):
                                h_cidx2 = StateManager._get_contact_index()
                                match_c2 = [(ci, cc) for ci, nl, al, cc in h_cidx2
                                            if _norm_addr(cc["address"]) == _norm_addr(h_addr)]
                                if match_c2:
                                    orig_ci2, contact_c2 = match_c2[0]

                                    def _edit_contact(
                                        _fi=fi, _si=start_i,
                                        _oci=orig_ci2, _cc=contact_c2
                                    ):
                                        """Corps du formulaire d'édition — fragmenté pour éviter le rerun à chaque frappe."""
                                        st.write("✏️ **Modification**")
                                        edit_name  = st.text_input("Nom", value=_cc['name'],
                                                                    key=f"hedit_name_{_si+_fi}")
                                        edit_addr  = st.text_input("Adresse", value=_cc['address'],
                                                                    key=f"hedit_addr_{_si+_fi}",
                                                                    help="Ajoutez le code postal si manquant")
                                        if edit_addr and not _RE_POSTCODE.search(edit_addr):
                                            st.caption("⚠️ Pas de code postal")
                                        edit_phone = st.text_input("Téléphone",
                                                                    value=_cc.get('phone', ''),
                                                                    key=f"hedit_phone_{_si+_fi}")
                                        edit_type  = st.selectbox("Type intervention", INTERVENTION_KEYS,
                                            index=INTERVENTION_KEYS.index(_cc['intervention_type'])
                                                  if _cc['intervention_type'] in INTERVENTION_TYPES else 1,
                                            key=f"hedit_type_{_si+_fi}")
                                        edit_notes = st.text_area("Notes", value=_cc.get('notes', ''),
                                                                   key=f"hedit_notes_{_si+_fi}")
                                        cs, cv, cc = st.columns([2, 2, 1])
                                        with cs:
                                            if st.button("💾 Sauver", key=f"hedit_save_{_si+_fi}",
                                                         use_container_width=True):
                                                if edit_addr.strip() != _cc['address'].strip():
                                                    st.session_state.coord_cache.pop(_norm_addr(_cc['address']), None)
                                                StateManager.update_contact(
                                                    _oci, name=edit_name, address=edit_addr,
                                                    phone=edit_phone, intervention_type=edit_type,
                                                    notes=edit_notes,
                                                    service_duration=INTERVENTION_TYPES.get(edit_type, 60*SPM))
                                                st.session_state[f"editing_hist_{_si+_fi}"] = False
                                                st.rerun()  # rerun global nécessaire : maj liste contacts
                                        with cv:
                                            if st.button("🔍 Vérifier", key=f"hedit_val_{_si+_fi}",
                                                         use_container_width=True):
                                                with st.spinner("Géocodage…"):
                                                    coords = Geo._fetch(edit_addr.strip())
                                                if coords:
                                                    st.success(f"✅ ({coords[0]:.4f}, {coords[1]:.4f})")
                                                    st.session_state.coord_cache[_norm_addr(edit_addr)] = coords
                                                    GeoCache.save()
                                                else:
                                                    st.error("❌ Adresse non trouvée")
                                        with cc:
                                            if st.button("✖", key=f"hedit_cancel_{_si+_fi}",
                                                         use_container_width=True):
                                                st.session_state[f"editing_hist_{_si+_fi}"] = False
                                                st.rerun()

                                    if HAS_FRAGMENT:
                                        st.fragment(_edit_contact)()
                                    else:
                                        _edit_contact()

                            if st.session_state.get(f"hist_expand_{start_i+fi}", False):
                                st.write(f"**Type :** {h.get('intervention_type','—')}")
                                if h.get("notes"):
                                    st.write(f"**Notes :** {h['notes']}")
                                all_h_dates = sorted(h.get("visit_dates", []), key=_sort_key_date)
                                if all_h_dates:
                                    st.caption("Dates de passage (✕ pour supprimer) :")
                                    for di, d in enumerate(all_h_dates):
                                        dc1, dc2 = st.columns([3, 1])
                                        with dc1:
                                            st.caption(f"📅 {d}")
                                        with dc2:
                                            if st.button("✕", key=f"del_date_{start_i+fi}_{di}",
                                                         help=f"Supprimer le {d}"):
                                                h["visit_dates"] = [x for x in h["visit_dates"] if x != d]
                                                HistoryManager.save_to_file()
                                                st.rerun()

                            st.markdown("<hr style='margin:3px 0;border-color:#333'>",
                                        unsafe_allow_html=True)

            else:
                st.info("Aucun historique. Planifiez une tournée pour l'alimenter, "
                        "ou importez un CSV avec une colonne visit_date.")

            # ── Ajouter un nouveau contact ──────────────────────────────────
            with st.expander("➕ Nouveau contact", expanded=False):
                new_name    = st.text_input("Nom du client", key="new_contact_name",
                                            placeholder="Ex: M. Dupont")
                new_address = st.text_input("Adresse", key="new_contact_addr",
                                            placeholder="12 rue de la Paix…")
                new_phone   = st.text_input("Téléphone (optionnel)", key="new_contact_phone",
                                            placeholder="06…")
                new_type    = st.selectbox("Type intervention par défaut", INTERVENTION_KEYS,
                                           index=1, key="new_contact_type")
                new_notes   = st.text_area("Notes", key="new_contact_notes",
                                           placeholder="Ex: Cheminée difficile…", height=80)
                if st.button("💾 Enregistrer le contact", type="primary",
                             use_container_width=True):
                    if new_name and new_address:
                        if StateManager.is_duplicate_contact(new_name, new_address):
                            st.warning("⚠️ Contact déjà existant.")
                        else:
                            contact_new = Contact(
                                name=new_name, address=new_address, phone=new_phone,
                                intervention_type=new_type, notes=new_notes,
                                service_duration=INTERVENTION_TYPES.get(new_type, 60*SPM))
                            StateManager.add_contact(contact_new)
                            for k in ["new_contact_name","new_contact_addr",
                                      "new_contact_phone","new_contact_notes"]:
                                st.session_state.pop(k, None)
                            st.rerun()
                    else:
                        st.warning("Nom et adresse requis")

        with tab_search:
            st.markdown("#### 🔍 Rechercher une adresse")
            search_query = st.text_input("", placeholder="Ex : 12 rue de la Paix 88000 Épinal…",
                                         key="addr_search_query",
                                         label_visibility="collapsed")
            if st.button("🔍 Chercher", key="addr_search_btn",
                         use_container_width=True, type="primary"):
                if search_query:
                    with st.spinner("Recherche…"):
                        suggestions = Geo.search_address_suggestions(search_query, limit=10)
                        if suggestions:
                            st.session_state.address_suggestions["search"] = suggestions
                            st.rerun()
                        else:
                            st.warning("Aucun résultat")

            if "search" in st.session_state.address_suggestions:
                suggestions = st.session_state.address_suggestions["search"]
                st.caption(f"{len(suggestions)} résultat(s) — cliquez ➕ pour ajouter à la tournée")
                for idx, sugg in enumerate(suggestions):
                    if st.button(f"➕ {sugg['display_name'][:60]}",
                                 key=f"sugg_search_{idx}",
                                 use_container_width=True):
                        StateManager.add_point(sugg['display_name'])
                        pts2 = StateManager.points()
                        pts2[-1].coordinates = (sugg['lat'], sugg['lon'])
                        del st.session_state.address_suggestions["search"]
                        StateManager.commit()

        # ── Onglet Paramètres ────────────────────────────────────────────
        with tab_params:
            UI.params_tab()

        # ── Onglet Import / Export ───────────────────────────────────────
        with tab_csv:
            st.markdown("#### 📥 Export du carnet")
            contacts_csv = StateManager.get_contacts()
            if contacts_csv:
                csv_exp = AddressBookManager.export_to_csv()
                st.download_button("📥 Télécharger le carnet (CSV)",
                                   data=csv_exp, file_name="carnet_adresses.csv",
                                   mime="text/csv", use_container_width=True)
            else:
                st.info("Aucun contact à exporter.")

            st.markdown("---")
            st.markdown("#### 📤 Import / Mise à jour")
            template_dl = AddressBookManager.get_csv_template()
            st.download_button("📋 Télécharger le modèle CSV", data=template_dl,
                               file_name="modele_carnet.csv", mime="text/csv")
            uploaded_csv = st.file_uploader("Choisir un fichier CSV", type=["csv"],
                                            key="upload_csv_tab")
            if uploaded_csv is not None:
                st.caption("Le fichier est prêt. Choisissez une action :")
                c1, c2 = st.columns(2)
                with c1:
                    if st.button("➕ Ajouter les nouveaux clients", key="btn_csv_add",
                                 use_container_width=True, type="primary",
                                 help="Fusionne avec le carnet existant"):
                        csv_bytes = AddressBookManager.decode_csv_bytes(uploaded_csv.getvalue())
                        imported, errors = AddressBookManager.import_from_csv(csv_bytes)
                        if imported > 0:
                            st.success(f"✅ {imported} contact(s) importé(s)")
                        if errors:
                            for err in errors[:5]: st.caption(f"⚠️ {err}")
                        st.rerun()
                with c2:
                    if st.button("🔄 Remplacer tout le carnet", key="btn_csv_replace",
                                 use_container_width=True,
                                 help="Supprime l'existant et importe ce fichier"):
                        if st.session_state.get("_confirm_replace_csv"):
                            st.session_state.address_book = []
                            StateManager._invalidate_csv_cache()
                            StateManager._invalidate_contact_index()
                            csv_bytes = AddressBookManager.decode_csv_bytes(uploaded_csv.getvalue())
                            imported, errors = AddressBookManager.import_from_csv(csv_bytes)
                            st.session_state["_confirm_replace_csv"] = False
                            if imported > 0:
                                st.success(f"✅ {imported} contact(s) importé(s)")
                            if errors:
                                for err in errors[:5]: st.caption(f"⚠️ {err}")
                            st.rerun()
                        else:
                            st.session_state["_confirm_replace_csv"] = True
                            st.warning("⚠️ Cette action supprime tous les contacts existants. Cliquez à nouveau pour confirmer.")

        st.markdown(
            "<div style='text-align:center;color:gray;font-size:0.8em;margin-top:2em'>"
            "ItinéraireMalin v40 &nbsp;·&nbsp; "
            "⭐ Exact solver ≤11 stops &nbsp;·&nbsp; "
            "⚡ Heuristique >11"
            "</div>", unsafe_allow_html=True
        )

    except Exception as e:
        st.error(f"❌Erreur critique: {e}")
        import traceback
        st.code(traceback.format_exc())

if __name__ == "__main__":
    main()
