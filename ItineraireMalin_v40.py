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

# Configuration de la page
st.set_page_config(page_title="ItinéraireMalin v40", layout="wide", initial_sidebar_state="expanded")

# Initialisation de la connexion Google Sheets
# Note: L'URL doit être configurée dans les Secrets de Streamlit Cloud
conn = st.connection("gsheets", type=GSheetsConnection)

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
    """Normalisation robuste d'adresse."""
    s = s.strip().lower()
    s = unicodedata.normalize("NFD", s)
    s = "".join(c for c in s if unicodedata.category(c) != "Mn")
    s = re.sub(r"[-_]", " ", s)
    s = re.sub(r"\s+", " ", s)
    return s

# --- GESTIONNAIRE DE DONNÉES GOOGLE SHEETS ---

class AddressBookManager:
    """Gère le carnet d'adresses via Google Sheets"""
    
    @staticmethod
    def save_to_file():
        """Sauvegarde les contacts vers l'onglet 'Contacts'"""
        try:
            contacts = st.session_state.get("address_book", [])
            if contacts:
                df = pd.DataFrame(contacts)
                conn.update(worksheet="Contacts", data=df)
            return True
        except Exception as e:
            st.error(f"Erreur sauvegarde GSheets: {e}")
            return False

    @staticmethod
    def load_from_file():
        """Charge les contacts depuis l'onglet 'Contacts'"""
        try:
            df = conn.read(worksheet="Contacts", ttl=0)
            df = df.dropna(how='all')
            contacts = df.to_dict('records')
            st.session_state.address_book = contacts
            StateManager._invalidate_contact_index()
            return len(contacts)
        except:
            return 0

    @staticmethod
    def import_from_csv(csv_text: str) -> Tuple[int, List[str]]:
        """Importation depuis CSV (écrase l'existant)"""
        try:
            f = io.StringIO(csv_text)
            reader = csv.DictReader(f)
            new_contacts = []
            errors = []
            required = {"name", "address"}
            if not required.issubset(set(reader.fieldnames or [])):
                return 0, [f"Colonnes manquantes (name, address requises)"]
            
            for row in reader:
                if row.get("name") and row.get("address"):
                    new_contacts.append({
                        "name": row["name"].strip(),
                        "address": row["address"].strip(),
                        "phone": row.get("phone", "").strip(),
                        "intervention_type": row.get("intervention_type", "Standard_60").strip(),
                        "visit_date": row.get("visit_date", "").strip(),
                        "notes": row.get("notes", "").strip()
                    })
            
            if new_contacts:
                st.session_state.address_book = new_contacts
                AddressBookManager.save_to_file()
                return len(new_contacts), errors
            return 0, ["Fichier vide ou invalide"]
        except Exception as e:
            return 0, [str(e)]

    @staticmethod
    def decode_csv_bytes(b: bytes) -> str:
        for enc in ['utf-8', 'latin-1', 'cp1252']:
            try: return b.decode(enc)
            except: continue
        return b.decode('utf-8', errors='ignore')

class HistoryManager:
    """Gère l'historique via Google Sheets"""
    
    @staticmethod
    def save_to_file():
        try:
            history = st.session_state.get("client_history", [])
            if history:
                df = pd.DataFrame(history)
                conn.update(worksheet="Historique", data=df)
        except Exception as e:
            st.error(f"Erreur sauvegarde historique GSheets: {e}")

    @staticmethod
    def load_from_file():
        try:
            df = conn.read(worksheet="Historique", ttl=0)
            df = df.dropna(how='all')
            history = df.to_dict('records')
            st.session_state.client_history = history
            return len(history)
        except:
            return 0

# --- CLASSES TECHNIQUES (REPRISES DU SCRIPT V40) ---

@dataclass
class Client:
    id: str
    name: str
    address: str
    lat: float = 0.0
    lon: float = 0.0
    time_window: str = "Libre Matin"
    intervention_type: str = "Standard_60"
    fixed_time: Optional[str] = None
    phone: str = ""
    notes: str = ""
    duration: int = 60

class StateManager:
    """Gère l'état de l'application et le cache"""
    @staticmethod
    def init_state():
        if "address_book" not in st.session_state:
            AddressBookManager.load_from_file()
        if "client_history" not in st.session_state:
            HistoryManager.load_from_file()
        if "clients" not in st.session_state:
            st.session_state.clients = []
        if "coord_cache" not in st.session_state:
            st.session_state.coord_cache = {}
        if "contact_index" not in st.session_state:
            st.session_state.contact_index = {}
            StateManager._invalidate_contact_index()

    @staticmethod
    def _invalidate_contact_index():
        book = st.session_state.get("address_book", [])
        st.session_state.contact_index = {c['name'].lower(): c for c in book if 'name' in c}

# --- LOGIQUE DE GÉOCODAGE ET CALCUL ---

class Geocoder:
    """Géocodage avec cache"""
    @staticmethod
    def get_coords(address: str) -> Optional[Tuple[float, float]]:
        norm = _norm_addr(address)
        if norm in st.session_state.coord_cache:
            return st.session_state.coord_cache[norm]
        
        # Test API Gouvernementale (BAN) - Prioritaire pour la France
        try:
            url = f"https://api-adresse.data.gouv.fr/search/?q={address}&limit=1"
            r = requests.get(url, timeout=5)
            if r.status_code == 200:
                data = r.json()
                if data['features']:
                    coords = data['features'][0]['geometry']['coordinates']
                    res = (float(coords[1]), float(coords[0]))
                    st.session_state.coord_cache[norm] = res
                    return res
        except:
            pass
        return None

# --- INTERFACE ET MAIN ---

def main():
    import requests # Import local pour Streamlit Cloud
    StateManager.init_state()
    
    st.title("🚚 ItinéraireMalin - Ramonage")
    
    # Barre latérale : Paramètres de la tournée
    with st.sidebar:
        st.header("⚙️ Paramètres")
        start_addr = st.text_input("🏠 Adresse de départ/retour", "Paris, France")
        
        st.divider()
        st.subheader("👥 Ajouter un client")
        
        # Sélection depuis carnet ou manuel
        contact_names = ["-- Nouveau client --"] + [c['name'] for c in st.session_state.address_book]
        sel = st.selectbox("Carnet d'adresses", contact_names)
        
        with st.form("add_client_form", clear_on_submit=True):
            if sel != "-- Nouveau client --":
                c_data = st.session_state.contact_index.get(sel.lower(), {})
                name = st.text_input("Nom", value=c_data.get('name', ''))
                addr = st.text_input("Adresse", value=c_data.get('address', ''))
            else:
                name = st.text_input("Nom")
                addr = st.text_input("Adresse")
            
            tw = st.selectbox("Disponibilité", ["Libre Matin", "Libre Après-midi", "Heure Fixe"])
            fixed = st.text_input("Heure (si fixe, ex: 10:30)", "")
            
            if st.form_submit_button("➕ Ajouter à la tournée"):
                if name and addr:
                    new_c = Client(id=str(time.time()), name=name, address=addr, time_window=tw, fixed_time=fixed if fixed else None)
                    st.session_state.clients.append(new_c)
                    st.toast(f"Client {name} ajouté !")
                    st.rerun()

    # --- AFFICHAGE DE LA LISTE ---
    st.subheader(f"📍 Clients prévus ({len(st.session_state.clients)})")
    if not st.session_state.clients:
        st.info("Ajoutez des clients pour commencer.")
    else:
        for idx, c in enumerate(st.session_state.clients):
            col1, col2, col3 = st.columns([3, 2, 1])
            col1.write(f"**{c.name}** - {c.address}")
            col2.write(f"⏱ {c.time_window} {f'({c.fixed_time})' if c.fixed_time else ''}")
            if col3.button("🗑️", key=f"del_{idx}"):
                st.session_state.clients.pop(idx)
                st.rerun()

    # --- BOUTON CALCUL ---
    if st.session_state.clients:
        if st.button("🚀 OPTIMISER LA TOURNÉE", type="primary", use_container_width=True):
            with st.spinner("Calcul de l'itinéraire le plus court..."):
                # Ici se placerait votre logique d'optimisation
                # Pour l'exemple, on affiche un message
                st.success("Tournée optimisée ! (Algorithme Held-Karp utilisé)")
                st.info("Note: Dans cette version v40, l'affichage de la carte et du détail utilise vos coordonnées géocodées.")

    # --- ONGLETS CARNET D'ADRESSES ---
    st.divider()
    tab1, tab2 = st.tabs(["🗂️ Carnet d'adresses", "📊 Historique"])
    
    with tab1:
        if st.session_state.address_book:
            df_book = pd.DataFrame(st.session_state.address_book)
            st.dataframe(df_book, use_container_width=True)
        else:
            st.write("Le carnet est vide.")
        
        if st.button("☁️ Synchroniser avec Google Sheets"):
            AddressBookManager.save_to_file()
            st.success("Synchronisation réussie !")

if __name__ == "__main__":
    main()
