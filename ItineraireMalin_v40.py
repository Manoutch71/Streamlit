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
import requests
from streamlit_gsheets import GSheetsConnection
import pandas as pd

# --- CONFIGURATION DE LA PAGE ---
st.set_page_config(page_title="ItinéraireMalin v40", layout="wide", initial_sidebar_state="expanded")

# Initialisation de la connexion Google Sheets
try:
    conn = st.connection("gsheets", type=GSheetsConnection)
except Exception as e:
    st.error("Erreur de connexion Google Sheets. Vérifiez vos Secrets Streamlit.")

# --- UTILITAIRES DE NETTOYAGE ---
def _h(s: str) -> str:
    return _html.escape(str(s))

def _norm_addr(s: str) -> str:
    s = s.strip().lower()
    s = unicodedata.normalize("NFD", s)
    s = "".join(c for c in s if unicodedata.category(c) != "Mn")
    s = re.sub(r"[-_]", " ", s)
    s = re.sub(r"\s+", " ", s)
    return s

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

# --- GESTIONNAIRES DE PERSISTANCE (GOOGLE SHEETS) ---
class AddressBookManager:
    @staticmethod
    def save_to_file():
        try:
            contacts = st.session_state.get("address_book", [])
            if contacts:
                df = pd.DataFrame(contacts)
                conn.update(worksheet="Contacts", data=df)
                return True
        except Exception as e:
            st.error(f"Erreur sauvegarde Contacts: {e}")
        return False

    @staticmethod
    def load_from_file():
        try:
            df = conn.read(worksheet="Contacts", ttl=0)
            df = df.dropna(how='all')
            contacts = df.to_dict('records')
            st.session_state.address_book = contacts
            return len(contacts)
        except:
            st.session_state.address_book = []
            return 0

class HistoryManager:
    @staticmethod
    def save_to_file():
        try:
            history = st.session_state.get("client_history", [])
            if history:
                df = pd.DataFrame(history)
                conn.update(worksheet="Historique", data=df)
        except Exception as e:
            st.error(f"Erreur sauvegarde Historique: {e}")

    @staticmethod
    def load_from_file():
        try:
            df = conn.read(worksheet="Historique", ttl=0)
            df = df.dropna(how='all')
            history = df.to_dict('records')
            st.session_state.client_history = history
            return len(history)
        except:
            st.session_state.client_history = []
            return 0

class StateManager:
    @staticmethod
    def init_state():
        if "address_book" not in st.session_state:
            st.session_state.address_book = []
        if "client_history" not in st.session_state:
            st.session_state.client_history = []
        if "clients" not in st.session_state:
            st.session_state.clients = []
        if "coord_cache" not in st.session_state:
            st.session_state.coord_cache = {}
        if "contact_index" not in st.session_state:
            st.session_state.contact_index = {}
        
        if "data_loaded" not in st.session_state:
            AddressBookManager.load_from_file()
            HistoryManager.load_from_file()
            StateManager._invalidate_contact_index()
            st.session_state.data_loaded = True

    @staticmethod
    def _invalidate_contact_index():
        book = st.session_state.get("address_book", [])
        st.session_state.contact_index = {str(c.get('name', '')).lower(): c for c in book if 'name' in c}
        # --- INTERFACE ET LOGIQUE ---
def main():
    # Correctif CSS pour éviter le titre coupé sur mobile
    st.markdown("""
        <style>
            .block-container { padding-top: 2rem; padding-bottom: 1rem; }
            h1 { line-height: 1.4; padding-bottom: 10px; font-size: 1.8rem !important; }
            .stButton>button { width: 100%; border-radius: 6px; height: 3em; background-color: #007bff; color: white; }
            .stExpander { border: 1px solid #ddd; border-radius: 8px; margin-bottom: 5px; }
        </style>
        """, unsafe_allow_html=True)

    StateManager.init_state()
    
    st.title("🚚 ItinéraireMalin - Ramonage")

    # --- BARRE LATÉRALE ---
    with st.sidebar:
        st.header("⚙️ Paramètres")
        
        # Sélection sécurisée depuis le carnet
        contacts_list = st.session_state.get("address_book", [])
        contact_names = ["-- Nouveau client --"] + [str(c.get('name', 'Sans nom')) for c in contacts_list]
        
        sel = st.selectbox("Rechercher un client", contact_names)
        
        with st.form("add_client_form", clear_on_submit=True):
            if sel != "-- Nouveau client --":
                c_data = st.session_state.contact_index.get(sel.lower(), {})
                name = st.text_input("Nom", value=c_data.get('name', ''))
                addr = st.text_input("Adresse", value=c_data.get('address', ''))
            else:
                name = st.text_input("Nom")
                addr = st.text_input("Adresse")
            
            tw = st.selectbox("Disponibilité", ["Libre Matin", "Libre Après-midi", "Heure Fixe"])
            fixed = st.text_input("Heure (ex: 10:30)", "")
            
            if st.form_submit_button("➕ Ajouter à la tournée"):
                if name and addr:
                    new_c = Client(id=str(time.time()), name=name, address=addr, time_window=tw, fixed_time=fixed)
                    st.session_state.clients.append(new_c)
                    st.success(f"Ajouté : {name}")
                    st.rerun()

    # --- CORPS DE LA PAGE ---
    col_main, col_info = st.columns([2, 1])
    
    with col_main:
        st.subheader(f"📍 Liste du jour ({len(st.session_state.clients)})")
        if not st.session_state.clients:
            st.info("Utilisez la barre latérale pour ajouter des clients.")
        else:
            for idx, c in enumerate(st.session_state.clients):
                with st.expander(f"👤 {c.name} - {c.time_window}"):
                    st.write(f"🏠 **Adresse :** {c.address}")
                    if c.fixed_time:
                        st.write(f"⏰ **Heure fixe :** {c.fixed_time}")
                    if st.button(f"🗑️ Retirer {c.name}", key=f"del_{idx}"):
                        st.session_state.clients.pop(idx)
                        st.rerun()

        if st.session_state.clients:
            st.divider()
            if st.button("🚀 CALCULER L'ITINÉRAIRE", type="primary"):
                st.info("Calcul en cours via OSRM... (Pensez à bien renseigner les adresses complètes)")

    with col_info:
        st.subheader("💾 Données")
        if st.button("☁️ Synchroniser vers GSheets"):
            if AddressBookManager.save_to_file():
                st.success("✅ Contacts sauvegardés !")
        
        if st.button("🔄 Actualiser la liste"):
            AddressBookManager.load_from_file()
            StateManager._invalidate_contact_index()
            st.rerun()
            
        st.caption("Assurez-vous que votre Google Sheet possède les onglets 'Contacts' et 'Historique'.")

if __name__ == "__main__":
    main()
