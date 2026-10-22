import tkinter as tk
from tkinter import ttk, messagebox, filedialog, simpledialog
import pandas as pd
import json
import os
import sys
import site
import subprocess
from datetime import datetime, timedelta
import threading
import time

# Ensure JSON files and local virtual environments are found relative to the script or working directory
BASE_DIR = os.path.dirname(os.path.abspath(__file__)) if '__file__' in globals() else os.getcwd()

def _inject_local_venv_paths():
    """Adds local .venv or venv site-packages to sys.path in case Code Runner uses global Python."""
    search_roots = list({
        BASE_DIR,
        os.getcwd(),
        os.path.dirname(BASE_DIR),
        os.path.dirname(os.getcwd())
    })
    for root_dir in search_roots:
        for venv_name in (".venv", "venv", "env"):
            win_sp = os.path.join(root_dir, venv_name, "Lib", "site-packages")
            if os.path.isdir(win_sp) and win_sp not in sys.path:
                sys.path.append(win_sp)
    try:
        user_sp = site.getusersitepackages()
        if isinstance(user_sp, str) and os.path.isdir(user_sp) and user_sp not in sys.path:
            sys.path.append(user_sp)
    except Exception:
        pass

_inject_local_venv_paths()

# --- DEFERRED EXTERNAL LIBRARIES ---
# Loaded dynamically via lazy-loading to ensure the app launches instantly
plt = None
FigureCanvasTkAgg = None
LinearRegression = None
np = None
GoogleAuth = None
GoogleDrive = None
DateEntry = None

CLOUD_LIBRARY_INSTALLED = False
TKCALENDAR_INSTALLED = False
ANALYTICS_INSTALLED = False


class FallbackLinearRegression:
    """Built-in Ordinary Least Squares Linear Regression so AI Insights works even without scikit-learn."""
    def __init__(self):
        self.coef_ = [0.0]
        self.intercept_ = 0.0

    def fit(self, X, y):
        x_vals = [float(row[0]) if hasattr(row, '__iter__') else float(row) for row in X]
        y_vals = [float(val) for val in y]
        n = len(x_vals)
        if n > 1:
            mean_x = sum(x_vals) / n
            mean_y = sum(y_vals) / n
            num = sum((x_vals[i] - mean_x) * (y_vals[i] - mean_y) for i in range(n))
            den = sum((x_vals[i] - mean_x) ** 2 for i in range(n))
            slope = (num / den) if den != 0 else 0.0
            self.coef_ = [slope]
            self.intercept_ = mean_y - slope * mean_x
        return self

    def predict(self, X):
        x_vals = [float(row[0]) if hasattr(row, '__iter__') else float(row) for row in X]
        preds = [self.coef_[0] * x + self.intercept_ for x in x_vals]
        return np.array(preds) if np is not None else preds


def load_heavy_libraries():
    """Lazy Loader: Imports heavy data science libraries independently after login."""
    global pd, plt, FigureCanvasTkAgg, LinearRegression, np
    global GoogleAuth, GoogleDrive, CLOUD_LIBRARY_INSTALLED
    global DateEntry, TKCALENDAR_INSTALLED, ANALYTICS_INSTALLED

    _inject_local_venv_paths()

    try:
        import pandas as pd_mod
        pd = pd_mod
    except ImportError:
        pass

    try:
        import numpy as np_mod
        np = np_mod
    except ImportError:
        pass

    try:
        from pydrive2.auth import GoogleAuth as GA
        from pydrive2.drive import GoogleDrive as GD
        GoogleAuth = GA
        GoogleDrive = GD
        CLOUD_LIBRARY_INSTALLED = True
    except ImportError:
        CLOUD_LIBRARY_INSTALLED = False

    try:
        from tkcalendar import DateEntry as DE
        DateEntry = DE
        TKCALENDAR_INSTALLED = True
    except ImportError:
        TKCALENDAR_INSTALLED = False

    # Load scikit-learn independently, using built-in FallbackLinearRegression if sklearn isn't installed
    try:
        from sklearn.linear_model import LinearRegression as LR
        LinearRegression = LR
    except ImportError:
        LinearRegression = FallbackLinearRegression

    # Load matplotlib independently so a missing sklearn never disables charts
    try:
        import matplotlib
        matplotlib.use("TkAgg")
        import matplotlib.pyplot as plt_mod
        from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg as FC
        plt = plt_mod
        FigureCanvasTkAgg = FC
        ANALYTICS_INSTALLED = True
    except ImportError:
        try:
            subprocess.check_call([sys.executable, "-m", "pip", "install", "matplotlib", "--quiet"])
            import matplotlib
            matplotlib.use("TkAgg")
            import matplotlib.pyplot as plt_mod
            from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg as FC
            plt = plt_mod
            FigureCanvasTkAgg = FC
            ANALYTICS_INSTALLED = True
        except Exception as e:
            print(f"Matplotlib load warning: {e}")
            ANALYTICS_INSTALLED = False


def resolve_data_path(filename):
    """Finds the file in the current working directory or script directory."""
    if os.path.exists(filename):
        return os.path.abspath(filename)
    return os.path.join(BASE_DIR, filename)

DB_FILE = resolve_data_path("students.json")
FACULTY_FILE = resolve_data_path("faculty.json")
COURSES_FILE = resolve_data_path("courses.json")
HISTORY_FILE = resolve_data_path("attendance_history.json")

# In-memory fallback cache so login works even if OneDrive locks a file temporarily
MEMORY_FACULTY_DB = {}

# --- GOOGLE DRIVE CREDENTIALS ---
GOOGLE_CLIENT_ID = "PASTE-YOUR-CLIENT_ID"
GOOGLE_CLIENT_SECRET = "PASTE-YOUR-CLIENT-SECRET"

# --- SMS CONFIGURATION ---
SMS_ENABLED = False  
TWILIO_SID = "your_twilio_sid_here"
TWILIO_AUTH = "your_twilio_auth_token_here"
TWILIO_PHONE = "+1234567890"


class FacultyAuth:
    """Handles Faculty Login, Registration, and Password Recovery"""
    def __init__(self, root, on_success):
        self.root = root
        self.on_success = on_success
        self.root.title("Faculty Access Portal")
        self.root.geometry("650x850")
        self.root.configure(bg="#f0f2f5")
        
        # Force window to front
        self.root.lift()
        self.root.focus_force()

        self.frame = None
        self.last_registered_user = ""
        self.last_registered_pwd = ""
        self.show_login()

    def _create_frame(self, width=450, height=500):
        if self.frame is not None:
            self.frame.destroy()
            
        self.frame = tk.Frame(self.root, bg="#ffffff", relief=tk.RIDGE, bd=1)
        self.frame.place(relx=0.5, rely=0.5, anchor="center", width=width, height=height)
        self.frame.pack_propagate(False) 
        
        self.inner = tk.Frame(self.frame, bg="#ffffff")
        self.inner.place(relx=0.5, rely=0.5, anchor="center")
        return self.inner

    def show_login(self):
        inner = self._create_frame(width=450, height=500)
        
        tk.Label(inner, text="Faculty Login", font=("Helvetica", 24, "bold"), bg="#ffffff", fg="#333").pack(pady=(0, 20))
        
        tk.Label(inner, text="Username", bg="#ffffff", font=("Arial", 10)).pack(anchor="w")
        self.username_entry = tk.Entry(inner, width=35, font=("Arial", 12), bg="#f8f9fa")
        self.username_entry.pack(pady=(5, 15))
        
        tk.Label(inner, text="Password", bg="#ffffff", font=("Arial", 10)).pack(anchor="w")
        self.password_entry = tk.Entry(inner, show="*", width=35, font=("Arial", 12), bg="#f8f9fa")
        self.password_entry.pack(pady=(5, 5))

        # Auto-fill if the user just registered a new account
        if self.last_registered_user:
            self.username_entry.insert(0, self.last_registered_user)
            self.password_entry.insert(0, self.last_registered_pwd)

        # Show/Hide Password toggle
        self.show_pwd_var = tk.BooleanVar(value=False)
        def toggle_pwd():
            self.password_entry.config(show="" if self.show_pwd_var.get() else "*")
        tk.Checkbutton(inner, text="Show Password", variable=self.show_pwd_var, command=toggle_pwd, bg="#ffffff", font=("Arial", 9)).pack(anchor="w", pady=(0, 10))

        # Allow pressing Enter to log in
        self.username_entry.bind("<Return>", lambda e: self.perform_login())
        self.password_entry.bind("<Return>", lambda e: self.perform_login())
        
        tk.Button(inner, text="LOG IN", command=self.perform_login, bg="#1a73e8", fg="white", font=("Arial", 12, "bold"), width=30, pady=5, relief=tk.FLAT, cursor="hand2").pack(pady=10)
        
        tk.Button(inner, text="Forgot Password?", command=self.show_forgot_password, bg="#ffffff", fg="#d93025", font=("Arial", 9, "underline"), bd=0, cursor="hand2").pack(pady=5)
        
        tk.Label(inner, text="New Faculty Member?", bg="#ffffff").pack(pady=(15, 5))
        tk.Button(inner, text="Create Account", command=self.show_register, bg="#ffffff", fg="#1a73e8", font=("Arial", 10, "bold"), bd=0, cursor="hand2").pack()

    def show_register(self):
        inner = self._create_frame(width=550, height=720)
        
        tk.Label(inner, text="Faculty Registration", font=("Helvetica", 20, "bold"), bg="#ffffff", fg="#333").pack(pady=(0, 5))
        tk.Label(inner, text="* Username and Password are required", font=("Arial", 9, "italic"), bg="#ffffff", fg="#666").pack(pady=(0, 10))

        canvas_frame = tk.Frame(inner, bg="#ffffff")
        canvas_frame.pack(fill="both", expand=True)
        
        canvas = tk.Canvas(canvas_frame, bg="#ffffff", highlightthickness=0, height=480, width=450)
        scrollbar = ttk.Scrollbar(canvas_frame, orient="vertical", command=canvas.yview)
        scroll_frame = tk.Frame(canvas, bg="#ffffff")

        scroll_frame.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0, 0), window=scroll_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)

        # Enable mousewheel scrolling on registration form
        def _on_mousewheel(event):
            if canvas.winfo_exists():
                canvas.yview_scroll(int(-1 * (event.delta / 120)), "units")
        canvas.bind("<Enter>", lambda e: canvas.bind_all("<MouseWheel>", _on_mousewheel))
        canvas.bind("<Leave>", lambda e: canvas.unbind_all("<MouseWheel>"))

        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")

        self.entries = {}

        def create_section(title, fields):
            lf = tk.LabelFrame(scroll_frame, text=title, font=("Arial", 11, "bold"), bg="#ffffff", fg="#1a73e8", padx=10, pady=10)
            lf.pack(fill="x", pady=8, padx=5)
            for label_text, key in fields:
                tk.Label(lf, text=label_text, bg="#ffffff", font=("Arial", 9)).pack(anchor="w")
                entry = tk.Entry(lf, font=("Arial", 11), bg="#f8f9fa", width=40)
                if "Password" in label_text: 
                    entry.config(show="*")
                entry.pack(pady=(2, 8))
                self.entries[key] = entry

        # Put Account Info first so Username & Password are immediately visible at the top
        create_section("Account Info (Required)", [("Username *", "reg_username"), ("Password *", "reg_password"), ("Security Question", "sec_question"), ("Security Answer", "sec_answer")])
        create_section("Personal Info", [("First Name", "first_name"), ("Last Name", "last_name"), ("Personal Email", "pers_email"), ("Phone Number", "phone")])
        create_section("Organization Info", [("Organization Name", "org_name"), ("Faculty ID", "org_fac_id"), ("Department", "dept"), ("Organization Email", "org_email")])

        # Pin REGISTER and Back buttons outside the scroll area so they are always accessible
        btn_frame = tk.Frame(inner, bg="#ffffff")
        btn_frame.pack(pady=15, fill="x")
        tk.Button(btn_frame, text="REGISTER", command=self.perform_register, bg="#42b72a", fg="white", font=("Arial", 12, "bold"), width=20, cursor="hand2").pack(side="left", padx=15)
        tk.Button(btn_frame, text="Back to Login", command=self.show_login, bg="#f0f2f5", fg="#333", font=("Arial", 10, "bold"), width=15, relief=tk.FLAT, cursor="hand2").pack(side="right", padx=15)
        
    def show_forgot_password(self):
        inner = self._create_frame(width=500, height=400)
        
        tk.Label(inner, text="Reset Password", font=("Helvetica", 20, "bold"), bg="#ffffff", fg="#333").pack(pady=(20, 20))
        tk.Label(inner, text="Enter your Username:", bg="#ffffff", font=("Arial", 10)).pack(anchor="w")
        
        self.fp_username_entry = tk.Entry(inner, width=35, font=("Arial", 12), bg="#f8f9fa")
        self.fp_username_entry.pack(pady=5)
        
        tk.Button(inner, text="Next", command=self.check_fp_username, bg="#1a73e8", fg="white", font=("Arial", 11, "bold"), width=20).pack(pady=20)
        tk.Button(inner, text="Cancel", command=self.show_login, bg="#ffffff", fg="#666", font=("Arial", 10), bd=0, cursor="hand2").pack()

    def _find_user_key(self, db, username_input):
        """Finds a username key in db using exact or case-insensitive matching."""
        if username_input in db:
            return username_input
        u_low = username_input.lower()
        for k, v in db.items():
            if str(k).strip().lower() == u_low:
                return k
            if isinstance(v, dict) and str(v.get('reg_username', '')).strip().lower() == u_low:
                return k
        return None

    def check_fp_username(self):
        username = self.fp_username_entry.get().strip()
        if not username:
            messagebox.showerror("Error", "Please enter your username.")
            return
        
        db = self.load_faculty_db()
        matched_key = self._find_user_key(db, username)
        if matched_key:
            user_data = db[matched_key]
            if "sec_question" in user_data and "sec_answer" in user_data:
                self.show_fp_challenge(matched_key, user_data)
            else:
                messagebox.showerror("Error", "This account does not have security questions set up.")
        else:
            messagebox.showerror("Error", "Username not found.")

    def show_fp_challenge(self, username, user_data):
        inner = self._create_frame(width=500, height=550)
        
        tk.Label(inner, text="Security Verification", font=("Helvetica", 18, "bold"), bg="#ffffff", fg="#333").pack(pady=15)
        tk.Label(inner, text="Security Question:", bg="#ffffff", font=("Arial", 10, "bold"), fg="#555").pack(anchor="w", pady=(10,0))
        tk.Label(inner, text=user_data.get("sec_question", "N/A"), bg="#f0f2f5", font=("Arial", 11, "italic"), width=40, anchor="w", padx=5, pady=5).pack(pady=5)
        
        tk.Label(inner, text="Your Answer:", bg="#ffffff", font=("Arial", 10)).pack(anchor="w")
        self.fp_answer_entry = tk.Entry(inner, width=35, font=("Arial", 12), bg="#f8f9fa")
        self.fp_answer_entry.pack(pady=5)
        
        tk.Label(inner, text="New Password:", bg="#ffffff", font=("Arial", 10)).pack(anchor="w", pady=(15,0))
        self.fp_new_pass = tk.Entry(inner, show="*", width=35, font=("Arial", 12), bg="#f8f9fa")
        self.fp_new_pass.pack(pady=5)
        
        tk.Label(inner, text="Confirm New Password:", bg="#ffffff", font=("Arial", 10)).pack(anchor="w")
        self.fp_conf_pass = tk.Entry(inner, show="*", width=35, font=("Arial", 12), bg="#f8f9fa")
        self.fp_conf_pass.pack(pady=5)
        
        tk.Button(inner, text="Reset Password", command=lambda: self.perform_reset_password(username, user_data), bg="#42b72a", fg="white", font=("Arial", 12, "bold"), width=20).pack(pady=20)
        tk.Button(inner, text="Cancel", command=self.show_login, bg="#ffffff", fg="#666", font=("Arial", 10), bd=0).pack()

    def perform_reset_password(self, username, user_data):
        answer = self.fp_answer_entry.get().strip()
        new_p = self.fp_new_pass.get().strip()
        conf_p = self.fp_conf_pass.get().strip()
        
        if not answer or not new_p or not conf_p:
            messagebox.showerror("Error", "All fields are required.")
            return
        if answer.lower() != str(user_data.get("sec_answer", "")).strip().lower():
            messagebox.showerror("Error", "Incorrect Security Answer.")
            return
        if new_p != conf_p:
            messagebox.showerror("Error", "Passwords do not match.")
            return
            
        db = self.load_faculty_db()
        if username in db:
            db[username]['reg_password'] = new_p
            db[username]['password'] = new_p
            self.save_faculty_db(db)
            self.last_registered_user = username
            self.last_registered_pwd = new_p
            messagebox.showinfo("Success", "Password has been reset successfully!\nPlease log in.")
            self.show_login()
        else:
            messagebox.showerror("Error", "Database error occurred.")

    def load_faculty_db(self):
        global MEMORY_FACULTY_DB
        combined_db = dict(MEMORY_FACULTY_DB)

        # Check both script directory and current working directory
        candidate_paths = list({os.path.abspath("faculty.json"), os.path.join(BASE_DIR, "faculty.json"), FACULTY_FILE})
        for path in candidate_paths:
            if os.path.exists(path):
                try:
                    with open(path, 'r', encoding='utf-8') as f:
                        loaded = json.load(f)
                        if isinstance(loaded, dict):
                            combined_db.update(loaded)
                        elif isinstance(loaded, list):
                            for item in loaded:
                                if isinstance(item, dict):
                                    uname = item.get('reg_username') or item.get('username')
                                    if uname:
                                        combined_db[str(uname).strip()] = item
                except Exception as e:
                    print(f"Warning reading {path}: {e}")

        MEMORY_FACULTY_DB.update(combined_db)
        return combined_db

    def save_faculty_db(self, data):
        global MEMORY_FACULTY_DB
        MEMORY_FACULTY_DB.update(data)
        saved_any = False
        candidate_paths = list({os.path.abspath("faculty.json"), os.path.join(BASE_DIR, "faculty.json"), FACULTY_FILE})
        for path in candidate_paths:
            try:
                with open(path, 'w', encoding='utf-8') as f:
                    json.dump(MEMORY_FACULTY_DB, f, indent=4)
                saved_any = True
            except Exception as e:
                print(f"Error saving faculty DB to {path}: {e}")
        return saved_any

    def perform_register(self):
        data = {key: entry.get().strip() for key, entry in self.entries.items()}
        
        if not data.get('reg_username') or not data.get('reg_password'):
            messagebox.showerror("Error", "Username and Password are required!")
            return

        # Fill optional fields with sensible defaults if left blank
        defaults = {
            "org_name": "AIUB",
            "org_fac_id": "N/A",
            "dept": "General",
            "org_email": "N/A",
            "first_name": data['reg_username'],
            "last_name": "",
            "pers_email": "N/A",
            "phone": "N/A",
            "sec_question": "Default Question",
            "sec_answer": "admin"
        }
        for k, default_val in defaults.items():
            if not data.get(k):
                data[k] = default_val

        # Store password under both keys for backward/forward compatibility
        data['password'] = data['reg_password']

        db = self.load_faculty_db()
        existing_key = self._find_user_key(db, data['reg_username'])
        if existing_key:
            if not messagebox.askyesno("Username Exists", f"Username '{existing_key}' already exists.\nDo you want to update its password and profile with the new details?"):
                return
            db[existing_key] = data
        else:
            db[data['reg_username']] = data

        self.save_faculty_db(db)
        self.last_registered_user = data['reg_username']
        self.last_registered_pwd = data['reg_password']
        messagebox.showinfo("Success", f"Welcome, {data['first_name']}! Your account is ready.\nClick LOG IN to continue.")
        self.show_login()

    def perform_login(self):
        user = self.username_entry.get().strip()
        pwd = self.password_entry.get().strip()
        if not user or not pwd:
            messagebox.showerror("Error", "Please enter both Username and Password.")
            return

        db = self.load_faculty_db()
        matched_key = self._find_user_key(db, user)

        if matched_key is not None:
            faculty_info = db[matched_key]
            saved_pwd = str(faculty_info.get('reg_password', faculty_info.get('password', ''))).strip()
            if saved_pwd == pwd:
                if self.frame:
                    self.frame.destroy()
                self.on_success(self.root, faculty_info)
                return

        messagebox.showerror("Error", "Invalid Username or Password.\n\nTip: Click 'Create Account' below to register or update your account.")


class AttendanceSystem(tk.Frame):
    def __init__(self, parent, faculty_info, logout_cb):
        super().__init__(parent)
        self.parent = parent
        self.faculty_info = faculty_info
        self.logout_cb = logout_cb
        self.pack(fill="both", expand=True)
        
        self.parent.lift()
        self.parent.focus_force()
        
        self.ensure_client_secrets_file()
        
        org_name = faculty_info.get('org_name', 'School')
        teacher_name = f"{faculty_info.get('first_name', '')} {faculty_info.get('last_name', '')}".strip()
        self.parent.title(f"{org_name} - Smart Manager Pro | Logged in as: {teacher_name}")
        self.parent.geometry("1400x850") 
        
        self.students = self.load_database()
        self.courses = self.load_courses()
        self.history = self.load_history()
        
        self.current_session_course = None 
        self.view_date_str = datetime.now().strftime("%Y-%m-%d") 
        self.end_date_str = datetime.now().strftime("%Y-%m-%d")
        self.search_query = tk.StringVar() 
        self.student_search_query = tk.StringVar()
        self.import_course_var = tk.StringVar()
        self.analytics_course_var = tk.StringVar()
        self.analytics_student_var = tk.StringVar()
        self.ext_student_var = tk.StringVar()
        
        self.notebook = ttk.Notebook(self)
        self.notebook.pack(pady=10, expand=True, fill="both")
        
        self.tab_attendance = tk.Frame(self.notebook, bg="#f5f5f5")
        self.tab_students = tk.Frame(self.notebook, bg="#f5f5f5") 
        self.tab_analytics = tk.Frame(self.notebook, bg="#f5f5f5") 
        self.tab_co_analysis = tk.Frame(self.notebook, bg="#f5f5f5")
        self.tab_courses = tk.Frame(self.notebook, bg="#f5f5f5") 
        self.tab_register = tk.Frame(self.notebook, bg="#f5f5f5")
        self.tab_blood_group = tk.Frame(self.notebook, bg="#f5f5f5") 
        self.tab_google_forms = tk.Frame(self.notebook, bg="#f5f5f5")
        self.tab_faculty = tk.Frame(self.notebook, bg="#f5f5f5")
        self.tab_developer = tk.Frame(self.notebook, bg="#f5f5f5")

        self.notebook.add(self.tab_attendance, text=" 📅 Daily Attendance ")
        self.notebook.add(self.tab_students, text=" 🎓 Student Records ") 
        self.notebook.add(self.tab_analytics, text=" 📊 Data Analytics & AI ") 
        self.notebook.add(self.tab_co_analysis, text=" 📈 CO Analysis ")
        self.notebook.add(self.tab_courses, text=" 📚 Manage Courses ") 
        self.notebook.add(self.tab_register, text=" ➕ Register New Student ")
        self.notebook.add(self.tab_blood_group, text=" 🩸 Blood Bank ") 
        self.notebook.add(self.tab_google_forms, text=" 📥 Load Google Forms ")
        self.notebook.add(self.tab_faculty, text=" 👤 Faculty Access ")
        self.notebook.add(self.tab_developer, text=" ℹ️ Developer Contact ")
        
        self.setup_attendance_tab()
        self.setup_student_records_tab()
        self.setup_analytics_tab()
        self.setup_co_analysis_tab()
        self.setup_course_tab()
        self.setup_registration_tab()
        self.setup_blood_group_tab() 
        self.setup_google_forms_tab()
        self.setup_faculty_tab()
        self.setup_developer_tab()

        self.notebook.bind("<<NotebookTabChanged>>", self.on_tab_change)

    def ensure_client_secrets_file(self):
        if os.path.exists("client_secrets.json"): return
        if "PASTE_YOUR" in GOOGLE_CLIENT_ID: return 
        data = {
            "installed": {
                "client_id": GOOGLE_CLIENT_ID,
                "project_id": "attendance-app-project", 
                "auth_uri": "",
                "token_uri": "",
                "auth_provider_x509_cert_url": "",
                "client_secret": GOOGLE_CLIENT_SECRET,
                "redirect_uris": [""]
            }
        }
        try:
            with open("client_secrets.json", "w") as f: json.dump(data, f, indent=4)
        except: pass

    def load_database(self):
        if not os.path.exists(DB_FILE): return {}
        try:
            with open(DB_FILE, 'r', encoding='utf-8') as f: return json.load(f)
        except: return {}

    def save_database(self):
        try:
            with open(DB_FILE, 'w', encoding='utf-8') as f: json.dump(self.students, f, indent=4)
        except Exception as e: print(f"Error saving database: {e}")

    def load_courses(self):
        if not os.path.exists(COURSES_FILE): return {}
        try:
            with open(COURSES_FILE, 'r', encoding='utf-8') as f: return json.load(f)
        except: return {}

    def save_courses_db(self):
        try:
            with open(COURSES_FILE, 'w', encoding='utf-8') as f: json.dump(self.courses, f, indent=4)
        except Exception as e: print(f"Error saving courses: {e}")

    def load_history(self):
        if not os.path.exists(HISTORY_FILE): return {}
        try:
            with open(HISTORY_FILE, 'r', encoding='utf-8') as f: return json.load(f)
        except: return {}

    def save_history(self):
        try:
            with open(HISTORY_FILE, 'w', encoding='utf-8') as f: json.dump(self.history, f, indent=4)
        except Exception as e: print(f"Error saving history: {e}")

    def on_tab_change(self, event):
        selected_tab = event.widget.select()
        tab_text = event.widget.tab(selected_tab, "text")
        
        if "Register New Student" in tab_text: self.refresh_course_dropdown()
        if "Daily Attendance" in tab_text: self.refresh_attendance_session_dropdown()
        if "Student Records" in tab_text: self.refresh_student_filter_dropdown()
        if "Load Google Forms" in tab_text: self.refresh_import_course_dropdown()
        if "Data Analytics & AI" in tab_text: self.refresh_analytics_course_dropdown()
        if "Blood Bank" in tab_text: self.refresh_bg_course_dropdown()
        if "CO Analysis" in tab_text: self.refresh_co_course_dropdown()

    def process_absentees(self):
        if not self.students or not self.current_session_course:
            messagebox.showinfo("Info", "Select a course first.")
            return
            
        date_key = self.view_date_str
        course_key = f"{self.current_session_course['c_name']} ({self.current_session_course['c_sec']})"
        present_records = self.history.get(date_key, {}).get(course_key, [])
        present_ids = {r['id'] for r in present_records if r.get('status') == "1"}
        target_id = str(self.current_session_course['c_id']).strip()
        target_sec = str(self.current_session_course['c_sec']).strip()
        
        absent_list = []
        for cid, info in self.students.items():
            c_str = info.get('course', '')
            if f"ID:{target_id}" in c_str and f"Sec:{target_sec}" in c_str:
                if cid not in present_ids: 
                    absent_list.append(info)
                    
        if not absent_list:
            messagebox.showinfo("Great!", "100% Attendance!")
            return
            
        if not messagebox.askyesno("Confirm SMS", f"Found {len(absent_list)} absent students. Send SMS?"): return
            
        fac_name = f"{self.faculty_info.get('first_name', '')} {self.faculty_info.get('last_name', '')}"
        fac_phone = self.faculty_info.get('phone', '')
        
        def run_sms():
            count = 0
            for s in absent_list:
                msg = f"Alert: {s['name']} marked ABSENT on {date_key}. Contact {fac_name} ({fac_phone})."
                if self.send_sms(s['phone'], msg): count += 1
                time.sleep(0.5)
            messagebox.showinfo("Done", f"Sent {count} messages.")
            
        threading.Thread(target=run_sms).start()

    def send_sms(self, phone, message):
        if not SMS_ENABLED:
            print(f"[MOCK SMS] To {phone}: {message}")
            return True
        try:
            from twilio.rest import Client
            client = Client(TWILIO_SID, TWILIO_AUTH)
            client.messages.create(body=message, from_=TWILIO_PHONE, to=phone)
            return True
        except: return False

    def generate_and_upload(self):
        if not self.current_session_course:
            messagebox.showinfo("Error", "Select a course first.")
            return
            
        start_dt = datetime.strptime(self.view_date_str, "%Y-%m-%d")
        end_dt = datetime.strptime(self.end_date_str, "%Y-%m-%d")
        
        if end_dt < start_dt:
             messagebox.showerror("Error", "End Date cannot be before Start Date")
             return
             
        course_key = f"{self.current_session_course['c_name']} ({self.current_session_course['c_sec']})"
        target_id = str(self.current_session_course['c_id']).strip()
        target_sec = str(self.current_session_course['c_sec']).strip()
        
        all_records = []
        curr_dt = start_dt
        while curr_dt <= end_dt:
            d_key = curr_dt.strftime("%Y-%m-%d")
            day_logs = {rec['id']: rec for rec in self.history.get(d_key, {}).get(course_key, [])}
            for cid, s_info in self.students.items():
                c_str = s_info.get('course', '')
                if f"ID:{target_id}" not in c_str or f"Sec:{target_sec}" not in c_str: continue
                if cid in day_logs: 
                    rec = day_logs[cid]
                    status = rec['status']
                    time_val = rec['time']
                else: 
                    status = "0"
                    time_val = ""
                    
                all_records.append({
                    "Date": d_key, 
                    "Card ID": cid, 
                    "Name": s_info['name'], 
                    "Student ID": s_info.get('student_id', ''), 
                    "Time": time_val, 
                    "Status": status
                })
            curr_dt += timedelta(days=1)
            
        if not all_records: 
            messagebox.showinfo("Empty", "No records found.")
            return
            
        filename = f"Attendance_{self.view_date_str}_to_{self.end_date_str}.xlsx"
        df = pd.DataFrame(all_records)
        cols_to_keep = ["Date", "Card ID", "Name", "Student ID", "Time", "Status"]
        df = df[cols_to_keep]
        
        fac_name = f"{self.faculty_info.get('first_name', '')} {self.faculty_info.get('last_name', '')}"
        title = f"Attendance Report: {self.faculty_info.get('org_name', '')}"
        headers = [f"Faculty: {fac_name}", f"Course: {course_key}", f"Range: {self.view_date_str} to {self.end_date_str}"]
        self.prompt_export_location(df, filename, title, headers)

    def generate_student_excel(self):
        if not self.students: return
            
        filename = f"All_Students_{datetime.now().strftime('%Y-%m-%d')}.xlsx"
        data_list = []
        for cid, info in self.students.items():
            info['card_id'] = cid
            data_list.append(info)
            
        df = pd.DataFrame(data_list)
        if not df.empty:
            cols = ["card_id", "name", "student_id", "course", "blood_group", "phone", 
                    "mid_quiz", "mid_marks", "mid_obe", "mid_att", "mid_other",
                    "final_quiz", "final_marks", "final_obe", "final_att", "final_other"]
            cols = [c for c in cols if c in df.columns]
            df = df[cols]
            
            rename_map = {
                "card_id": "Card ID", "name": "Name", "student_id": "Student ID", 
                "course": "Course", "blood_group": "Blood Grp", "phone": "Phone",
                "mid_quiz": "MID Quiz (20%)", "mid_marks": "MID Marks (40%)",
                "mid_obe": "MID OBE (20%)", "mid_att": "MID Att (10%)",
                "mid_other": "MID Other (10%)", "final_quiz": "FINAL Quiz (20%)",
                "final_marks": "FINAL Marks (40%)", "final_obe": "FINAL OBE (20%)",
                "final_att": "FINAL Att (10%)", "final_other": "FINAL Other (10%)"
            }
            df.rename(columns=rename_map, inplace=True)
            
        fac_name = f"{self.faculty_info.get('first_name', '')} {self.faculty_info.get('last_name', '')}"
        title = f"Student Database: {self.faculty_info.get('org_name', '')}"
        headers = [f"Faculty: {fac_name}", f"Report Date: {datetime.now().strftime('%Y-%m-%d')}"]
        self.prompt_export_location(df, filename, title, headers)

    def prompt_export_location(self, df, default_filename, title, headers):
        popup = tk.Toplevel(self.parent)
        popup.title("Export Options")
        popup.geometry("450x200")
        popup.configure(bg="#f5f5f5")
        popup.transient(self.parent); popup.grab_set(); popup.lift(); popup.focus_force()
        tk.Label(popup, text="Do you want to save in the device or Update to Drive?", font=("Arial", 12, "bold"), bg="#f5f5f5", wraplength=400).pack(pady=20)
        btn_frame = tk.Frame(popup, bg="#f5f5f5"); btn_frame.pack(pady=10)
        def save_local():
            path = filedialog.asksaveasfilename(initialfile=default_filename, defaultextension=".xlsx", filetypes=[("Excel files", "*.xlsx")], title="Save Excel File", parent=popup)
            if path:
                if self.save_excel_file(df, path, title, headers): messagebox.showinfo("Success", f"File saved successfully to:\n{path}"); popup.destroy()
        def save_drive():
            if self.save_excel_file(df, default_filename, title, headers):
                popup.destroy()
                threading.Thread(target=self.upload_to_drive, args=(default_filename,)).start()
        tk.Button(btn_frame, text="Save to Device", command=save_local, bg="#4CAF50", fg="white", font=("Arial", 11, "bold"), width=15).pack(side=tk.LEFT, padx=15)
        tk.Button(btn_frame, text="Update to Drive", command=save_drive, bg="#2196F3", fg="white", font=("Arial", 11, "bold"), width=15).pack(side=tk.LEFT, padx=15)

    def save_excel_file(self, df, filename, title, headers):
        try:
            df.to_excel(filename, index=False, startrow=6)
            try:
                import openpyxl
                from openpyxl.styles import Font
                wb = openpyxl.load_workbook(filename)
                ws = wb.active
                ws['A1'] = title
                ws['A1'].font = Font(size=14, bold=True, color="0000FF")
                
                row_idx = 2
                for h_text in headers: 
                    cell = ws.cell(row=row_idx, column=1)
                    cell.value = h_text
                    cell.font = Font(bold=True)
                    row_idx += 1
                    
                for column in ws.columns:
                    max_length = 0
                    column_letter = column[0].column_letter
                    for cell in column:
                        try:
                            if cell.value: 
                                length = len(str(cell.value))
                                if length > max_length: max_length = length
                        except: pass
                    ws.column_dimensions[column_letter].width = (max_length + 2) * 1.1
                wb.save(filename)
                return True
            except ImportError: return True
            except Exception as e: 
                messagebox.showerror("Format Error", f"{e}")
                return True 
        except Exception as e: 
            messagebox.showerror("Save Error", f"{e}")
            return False

    def upload_to_drive(self, filepath):
        def show_error(msg): self.after(0, lambda: messagebox.showerror("Upload Failed", msg))
        def show_success(msg): self.after(0, lambda: messagebox.showinfo("Cloud Upload", msg))
            
        if not CLOUD_LIBRARY_INSTALLED or not os.path.exists("client_secrets.json"):
            show_error("Google Drive configuration not found.\n(Need pydrive2 + client_secrets.json)")
            return
            
        try:
            gauth = GoogleAuth()
            gauth.LoadCredentialsFile("mycreds.txt")
            if gauth.credentials is None: 
                gauth.LocalWebserverAuth() 
            elif gauth.access_token_expired:
                try: gauth.Refresh()
                except: gauth.LocalWebserverAuth()
            else: 
                gauth.Authorize()
                
            gauth.SaveCredentialsFile("mycreds.txt")
            drive = GoogleDrive(gauth)
            f = drive.CreateFile({'title': os.path.basename(filepath)})
            f.SetContentFile(filepath)
            f.Upload()
            show_success("Uploaded successfully to Google Drive!")
        except Exception as e: 
            show_error(str(e))

    # ==========================================
    # TAB 1: ATTENDANCE LOGIC
    # ==========================================
    def setup_attendance_tab(self):
        top_bar = tk.Frame(self.tab_attendance, bg="white", relief=tk.RIDGE, bd=1)
        top_bar.pack(fill=tk.X, padx=10, pady=(10, 0))
        date_frame = tk.Frame(top_bar, bg="white")
        date_frame.pack(side=tk.TOP, fill=tk.X, padx=10, pady=10)
        tk.Label(date_frame, text="View/Start Date:", font=("Arial", 10, "bold"), bg="white").pack(side=tk.LEFT)
        
        if TKCALENDAR_INSTALLED:
            self.cal = DateEntry(date_frame, width=12, background='#2196F3', foreground='white', borderwidth=2, date_pattern='yyyy-mm-dd')
            self.cal.pack(side=tk.LEFT, padx=10)
            self.cal.bind("<<DateEntrySelected>>", self.on_date_change)
            tk.Label(date_frame, text="End Date (For Report):", font=("Arial", 10, "bold"), bg="white").pack(side=tk.LEFT, padx=(20, 0))
            self.cal_end = DateEntry(date_frame, width=12, background='#FF5722', foreground='white', borderwidth=2, date_pattern='yyyy-mm-dd')
            self.cal_end.pack(side=tk.LEFT, padx=10)
            self.cal_end.bind("<<DateEntrySelected>>", self.on_end_date_change)
        else: 
            tk.Label(date_frame, text="(Install tkcalendar)", font=("Arial", 9), bg="white", fg="red").pack(side=tk.LEFT)
            
        fac_name = f"{self.faculty_info.get('first_name', '')} {self.faculty_info.get('last_name', '')}"
        tk.Label(date_frame, text=f" |  Faculty: {fac_name}", font=("Arial", 10, "italic"), bg="white", fg="#555").pack(side=tk.RIGHT, padx=10)
        
        course_frame = tk.Frame(top_bar, bg="white")
        course_frame.pack(side=tk.TOP, fill=tk.X, padx=10, pady=(0, 10))
        tk.Label(course_frame, text="Select Course:", font=("Arial", 11, "bold"), bg="white", fg="#1976D2").pack(side=tk.LEFT)
        
        self.session_course_var = tk.StringVar()
        self.session_combo = ttk.Combobox(course_frame, textvariable=self.session_course_var, width=40, state="readonly")
        self.session_combo.pack(side=tk.LEFT, padx=10)
        self.session_combo.bind("<<ComboboxSelected>>", self.on_session_select)
        
        info_frame = tk.Frame(self.tab_attendance, bg="#e8f5e9", pady=5)
        info_frame.pack(fill=tk.X, padx=10, pady=5)
        self.lbl_course_name = tk.Label(info_frame, text="Course: --", font=("Arial", 11, "bold"), bg="#e8f5e9", fg="#2e7d32")
        self.lbl_course_name.pack(side=tk.LEFT, padx=20)
        self.lbl_course_id = tk.Label(info_frame, text="ID: --", font=("Arial", 11), bg="#e8f5e9")
        self.lbl_course_id.pack(side=tk.LEFT, padx=20)
        self.lbl_section = tk.Label(info_frame, text="Section: --", font=("Arial", 11), bg="#e8f5e9")
        self.lbl_section.pack(side=tk.LEFT, padx=20)
        
        input_frame = tk.Frame(self.tab_attendance, bg="#f5f5f5")
        input_frame.pack(pady=5)
        tk.Label(input_frame, text="Scan Card:", bg="#f5f5f5", font=("Arial", 12)).pack(side=tk.LEFT, padx=5)
        self.att_entry = tk.Entry(input_frame, font=("Arial", 14), width=20)
        self.att_entry.pack(side=tk.LEFT, padx=5)
        self.att_entry.bind('<Return>', self.mark_attendance)
        self.att_entry.focus_set()
        tk.Label(input_frame, text="   |   Search Student ID:", bg="#f5f5f5", font=("Arial", 11, "bold")).pack(side=tk.LEFT, padx=5)
        self.search_entry = tk.Entry(input_frame, textvariable=self.search_query, font=("Arial", 12), width=15)
        self.search_entry.pack(side=tk.LEFT, padx=5)
        self.search_query.trace_add("write", lambda *args: self.refresh_attendance_table())
        
        self.status_label = tk.Label(self.tab_attendance, text="Ready.", font=("Arial", 12), bg="#f5f5f5", fg="gray")
        self.status_label.pack(pady=5)
        
        cols = ("Time", "Card ID", "Name", "Student ID", "Status")
        self.tree = ttk.Treeview(self.tab_attendance, columns=cols, show='headings', height=10)
        for col in cols:
            self.tree.heading(col, text=col)
            self.tree.column(col, width=120, anchor="center")
        self.tree.column("Name", width=200)
        self.tree.pack(padx=20, pady=5, fill="both", expand=True)
        
        log_action_frame = tk.Frame(self.tab_attendance, bg="#f5f5f5")
        log_action_frame.pack(pady=5, fill=tk.X, padx=20)
        tk.Button(log_action_frame, text="✏️ Modify Record", command=self.modify_attendance_entry, bg="#FFC107", fg="black").pack(side=tk.LEFT, padx=5)
        tk.Button(log_action_frame, text="🗑️ Delete Record", command=self.delete_attendance_entry, bg="#F44336", fg="white").pack(side=tk.LEFT, padx=5)
        
        btn_frame = tk.Frame(self.tab_attendance, bg="#f5f5f5")
        btn_frame.pack(pady=10, fill=tk.X)
        tk.Button(btn_frame, text="Generate Excel (Range)", command=self.generate_and_upload, bg="#4CAF50", fg="white", font=("Arial", 12, "bold"), padx=10).pack(side=tk.RIGHT, padx=20)
        tk.Button(btn_frame, text="⚠️ Send SMS (Today's Absentees)", command=self.process_absentees, bg="#FF5722", fg="white", font=("Arial", 12, "bold"), padx=10).pack(side=tk.LEFT, padx=20)

    def get_selected_date_str(self):
        if TKCALENDAR_INSTALLED: return self.cal.get_date().strftime("%Y-%m-%d")
        else: return datetime.now().strftime("%Y-%m-%d")
            
    def get_end_date_str(self):
        if TKCALENDAR_INSTALLED: return self.cal_end.get_date().strftime("%Y-%m-%d")
        else: return datetime.now().strftime("%Y-%m-%d")
            
    def on_date_change(self, event):
        self.view_date_str = self.get_selected_date_str()
        self.refresh_attendance_table()
        
    def on_end_date_change(self, event):
        self.end_date_str = self.get_end_date_str()
        
    def refresh_attendance_session_dropdown(self):
        course_names = list(self.courses.keys())
        self.session_combo['values'] = course_names
        if not self.current_session_course and course_names:
            self.session_combo.current(0)
            self.on_session_select(None)
            
    def on_session_select(self, event):
        selection = self.session_course_var.get()
        if selection in self.courses:
            self.current_session_course = self.courses[selection]
            self.lbl_course_name.config(text=f"Course: {self.current_session_course['c_name']}")
            self.lbl_course_id.config(text=f"ID: {self.current_session_course['c_id']}")
            self.lbl_section.config(text=f"Section: {self.current_session_course['c_sec']}")
        else:
            self.current_session_course = None
            self.lbl_course_name.config(text="Course: --")
            self.lbl_course_id.config(text="ID: --")
            self.lbl_section.config(text="Section: --")
        self.refresh_attendance_table()
        
    def refresh_attendance_table(self):
        for item in self.tree.get_children(): self.tree.delete(item)
            
        if not self.current_session_course: return
            
        c_data = self.current_session_course
        target_id = str(c_data['c_id']).strip()
        target_sec = str(c_data['c_sec']).strip()
        course_key = f"{c_data['c_name']} ({c_data['c_sec']})"
        date_key = self.view_date_str
        
        history_map = {}
        if date_key in self.history and course_key in self.history[date_key]:
            for rec in self.history[date_key][course_key]: history_map[rec['id']] = rec
                
        search_term = self.search_query.get().strip().lower()
        
        for cid, s_info in self.students.items():
            c_str = s_info.get('course', '')
            if f"ID:{target_id}" not in c_str or f"Sec:{target_sec}" not in c_str: continue
                
            s_id_txt = str(s_info.get('student_id', '')).lower()
            s_name_txt = str(s_info.get('name', '')).lower()
            
            if search_term and (search_term not in s_id_txt and search_term not in s_name_txt and search_term not in str(cid)): 
                continue
                
            if cid in history_map:
                rec = history_map[cid]
                status = rec['status']
                time_val = rec['time']
            else:
                status = "0"
                time_val = "" 
                
            try:
                self.tree.insert("", "end", iid=cid, values=(time_val, cid, s_info['name'], s_info.get('student_id', ''), status))
            except tk.TclError: pass 

    def mark_attendance(self, event):
        card_id = self.att_entry.get().strip()
        self.att_entry.delete(0, tk.END)
        
        if not card_id or not self.current_session_course:
            if not self.current_session_course: messagebox.showerror("Error", "Please select a Course first!")
            return
            
        if card_id not in self.students: 
            self.status_label.config(text=f"❌ Unknown Card: {card_id}", fg="red")
            return
            
        student = self.students[card_id]
        now_time = datetime.now().strftime("%H:%M:%S")
        date_key = self.view_date_str
        course_key = f"{self.current_session_course['c_name']} ({self.current_session_course['c_sec']})"
        
        if date_key not in self.history: self.history[date_key] = {}
        if course_key not in self.history[date_key]: self.history[date_key][course_key] = []
            
        current_records = self.history[date_key][course_key]
        found_record_index = -1
        
        for i, r in enumerate(current_records):
            if r['id'] == card_id: 
                found_record_index = i
                break
                
        if found_record_index != -1:
            existing_rec = current_records[found_record_index]
            if existing_rec['status'] == "1":
                self.status_label.config(text=f"⚠️ {student['name']} already present.", fg="orange")
                return
            else:
                existing_rec['status'] = "1"
                existing_rec['time'] = now_time
                self.save_history()
                self.refresh_attendance_table()
                self.status_label.config(text=f"✅ Updated: {student['name']} to Present", fg="green")
                return
                
        new_record = {"id": card_id, "name": student['name'], "student_id": student.get('student_id', 'N/A'), "time": now_time, "status": "1", "phone": student.get('phone', '')}
        self.history[date_key][course_key].append(new_record)
        self.save_history()
        self.refresh_attendance_table()
        self.status_label.config(text=f"✅ Marked: {student['name']}", fg="green")

    def modify_attendance_entry(self):
        selected_item = self.tree.selection()
        if not selected_item: return
        
        card_id = selected_item[0]
        values = self.tree.item(selected_item[0])['values']
        current_status = values[4]
        
        new_status = simpledialog.askstring("Modify Status", f"Current: {current_status}\nEnter '1' for Present, '0' for Absent:", initialvalue=current_status)
        
        if new_status:
            date_key = self.view_date_str
            course_key = f"{self.current_session_course['c_name']} ({self.current_session_course['c_sec']})"
            
            if date_key not in self.history: self.history[date_key] = {}
            if course_key not in self.history[date_key]: self.history[date_key][course_key] = []
            
            records = self.history[date_key][course_key]
            found = False
            for rec in records:
                if str(rec['id']) == card_id: 
                    rec['status'] = new_status
                    found = True
                    break
                    
            if not found and card_id in self.students:
                s = self.students[card_id]
                records.append({"id": card_id, "name": s['name'], "student_id": s.get('student_id',''), "time": "", "status": new_status, "phone": s.get('phone','')})
                
            self.save_history()
            self.refresh_attendance_table()

    def delete_attendance_entry(self):
        selected_item = self.tree.selection()
        if not selected_item: return
        
        if not messagebox.askyesno("Confirm", "Reset this record to default?"): return
        
        card_id = selected_item[0]
        date_key = self.view_date_str
        course_key = f"{self.current_session_course['c_name']} ({self.current_session_course['c_sec']})"
        
        self.history[date_key][course_key] = [r for r in self.history[date_key][course_key] if str(r['id']) != card_id]
        self.save_history()
        self.refresh_attendance_table()

    # ==========================================
    # TAB 2: STUDENT RECORDS
    # ==========================================
    def setup_student_records_tab(self):
        top_bar = tk.Frame(self.tab_students, bg="#f5f5f5")
        top_bar.pack(fill=tk.X, padx=20, pady=15)
        
        search_frame = tk.Frame(top_bar, bg="#f5f5f5")
        search_frame.pack(side=tk.LEFT)
        tk.Label(search_frame, text="Search Student:", bg="#f5f5f5", font=("Arial", 11, "bold")).pack(side=tk.LEFT)
        
        search_entry = tk.Entry(search_frame, textvariable=self.student_search_query, font=("Arial", 11), width=25)
        search_entry.pack(side=tk.LEFT, padx=10)
        self.student_search_query.trace_add("write", lambda *args: self.refresh_student_table())
        
        filter_frame = tk.Frame(top_bar, bg="#f5f5f5")
        filter_frame.pack(side=tk.RIGHT)
        tk.Label(filter_frame, text="Filter by Course:", bg="#f5f5f5", font=("Arial", 11, "bold")).pack(side=tk.LEFT)
        
        self.student_filter_var = tk.StringVar()
        self.student_filter_combo = ttk.Combobox(filter_frame, textvariable=self.student_filter_var, width=30, state="readonly")
        self.student_filter_combo.pack(side=tk.LEFT, padx=10)
        self.student_filter_combo.bind("<<ComboboxSelected>>", lambda e: self.refresh_student_table())
        
        cols = ("Card ID", "Name", "Student ID", "Course", "Blood Grp", "Phone", "MID Quiz (20%)", "MID Marks (40%)", "MID OBE (20%)", "MID Att (10%)", "MID Other (10%)", "FINAL Quiz (20%)", "FINAL Marks (40%)", "FINAL OBE (20%)", "FINAL Att (10%)", "FINAL Other (10%)")
        self.stud_tree = ttk.Treeview(self.tab_students, columns=cols, show='headings', height=18)
        
        for col in cols: 
            self.stud_tree.heading(col, text=col)
            width = 110 if "%" in col else 100
            if col == "Name" or col == "Course": width = 150
            elif col == "Card ID" or col == "Student ID": width = 120
            self.stud_tree.column(col, width=width, anchor="center")
            
        h_scroll = ttk.Scrollbar(self.tab_students, orient="horizontal", command=self.stud_tree.xview)
        self.stud_tree.configure(xscrollcommand=h_scroll.set)
        h_scroll.pack(side=tk.BOTTOM, fill=tk.X)
        self.stud_tree.pack(padx=20, pady=5, fill="both", expand=True)
        
        btn_frame = tk.Frame(self.tab_students, bg="#f5f5f5")
        btn_frame.pack(pady=15, fill=tk.X, padx=20)
        
        tk.Button(btn_frame, text="✏️ Modify Full Info", command=self.modify_student, bg="#FFC107", fg="black").pack(side=tk.LEFT, padx=5)
        tk.Button(btn_frame, text="🗑️ Delete Student", command=self.delete_student, bg="#F44336", fg="white").pack(side=tk.LEFT, padx=5)
        tk.Button(btn_frame, text="📊 Generate Student Excel", command=self.generate_student_excel, bg="#2196F3", fg="white", font=("Arial", 11, "bold")).pack(side=tk.RIGHT, padx=5)

    def refresh_student_filter_dropdown(self):
        course_options = ["All Courses"]
        for c_key, data in self.courses.items():
            label = f"{data['c_name']} | ID:{data['c_id']} | Sec:{data['c_sec']} | {data['c_days']}"
            course_options.append(label)
        self.student_filter_combo['values'] = course_options
        if not self.student_filter_var.get(): 
            self.student_filter_combo.current(0)

    def refresh_student_table(self):
        if not hasattr(self, 'stud_tree'): return
        
        for item in self.stud_tree.get_children():
            self.stud_tree.delete(item)
            
        query = self.student_search_query.get().lower()
        course_filter = self.student_filter_var.get()
        
        count_id = 0
        for cid, data in self.students.items():
            if course_filter and course_filter != "All Courses":
                if data.get('course') != course_filter: 
                    continue
                    
            txt = f"{cid} {data['name']} {data.get('student_id', '')}".lower()
            if query in txt:
                 tree_id = f"{cid}_{count_id}"
                 count_id += 1
                 try: 
                     self.stud_tree.insert("", "end", iid=tree_id, values=(
                         cid, 
                         data['name'], 
                         data.get('student_id', ''), 
                         data.get('course', ''), 
                         data.get('blood_group', 'Unknown'),
                         data.get('phone', ''),
                         data.get('mid_quiz', ''),
                         data.get('mid_marks', ''),
                         data.get('mid_obe', ''),
                         data.get('mid_att', ''),
                         data.get('mid_other', ''),
                         data.get('final_quiz', ''),
                         data.get('final_marks', ''),
                         data.get('final_obe', ''),
                         data.get('final_att', ''),
                         data.get('final_other', '')
                     ))
                 except tk.TclError: 
                     pass

    def modify_student(self):
        sel = self.stud_tree.selection()
        if not sel: 
            messagebox.showwarning("Selection", "Please select a student to modify.")
            return
            
        selected_id = sel[0]
        old_cid = selected_id.rsplit('_', 1)[0]
        
        if old_cid not in self.students:
            vals = self.stud_tree.item(sel[0])['values']
            sid = str(vals[2])
            for k, v in self.students.items():
                if v.get('student_id') == sid:
                    old_cid = k
                    break

        if old_cid not in self.students: 
            messagebox.showerror("Error", "Selected student not found in database!")
            return
            
        student_data = self.students[old_cid]
        
        edit_win = tk.Toplevel(self)
        edit_win.title("Modify Student Record")
        edit_win.geometry("600x780") 
        edit_win.configure(bg="#f5f5f5")
        
        edit_win.transient(self)
        edit_win.grab_set()
        edit_win.lift()
        edit_win.focus_force()

        tk.Label(edit_win, text="Edit Student & Academic Info", font=("Arial", 14, "bold"), bg="#f5f5f5").pack(pady=15)
        
        canvas = tk.Canvas(edit_win, bg="#f5f5f5", highlightthickness=0)
        scrollbar = ttk.Scrollbar(edit_win, orient="vertical", command=canvas.yview)
        scroll_frame = tk.Frame(canvas, bg="#f5f5f5")
        
        scroll_frame.bind("<Configure>", lambda e: canvas.configure(scrollregion=canvas.bbox("all")))
        canvas.create_window((0, 0), window=scroll_frame, anchor="nw")
        canvas.configure(yscrollcommand=scrollbar.set)
        
        canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")

        entries = {}
        original_values = {}
        calc_labels = []

        bm_frame = tk.Frame(scroll_frame, bg="#e8f0fe", bd=1, relief=tk.SOLID)
        bm_frame.pack(fill=tk.X, padx=20, pady=10)
        tk.Label(bm_frame, text="⚙️ Conversion Settings", font=("Arial", 10, "bold"), bg="#e8f0fe", fg="#1a73e8").pack(anchor="w", padx=10, pady=(5,0))
        
        bm_inner = tk.Frame(bm_frame, bg="#e8f0fe")
        bm_inner.pack(fill=tk.X, padx=10, pady=5)
        tk.Label(bm_inner, text="Default Base Mark (Out of):", bg="#e8f0fe", font=("Arial", 10)).pack(side=tk.LEFT)
        
        base_mark_var = tk.StringVar(value="100")
        base_mark_combo = ttk.Combobox(bm_inner, textvariable=base_mark_var, values=["10", "20", "30", "40", "50", "100"], width=10)
        base_mark_combo.pack(side=tk.LEFT, padx=10)
        tk.Label(bm_inner, text="*Press ENTER in a box to apply & lock base mark.", bg="#e8f0fe", fg="gray", font=("Arial", 8)).pack(side=tk.LEFT)

        def on_base_mark_change(*args):
            for fn in calc_labels: fn()
            
        base_mark_var.trace_add("write", on_base_mark_change)
        base_mark_combo.bind("<<ComboboxSelected>>", on_base_mark_change)

        def add_field(label, key, val, is_combo=False, combo_vals=None, weight=None):
            frame = tk.Frame(scroll_frame, bg="#f5f5f5")
            frame.pack(fill=tk.X, padx=20, pady=5)
            tk.Label(frame, text=label, width=18, anchor="w", bg="#f5f5f5").pack(side=tk.LEFT)
            
            if is_combo:
                if combo_vals:
                    course_opts = combo_vals
                else:
                    course_opts = []
                    for c_key, data in self.courses.items(): 
                        course_opts.append(f"{data['c_name']} | ID:{data['c_id']} | Sec:{data['c_sec']} | {data['c_days']}")
                widget = ttk.Combobox(frame, values=course_opts, width=28, state="readonly")
                if val in course_opts: 
                    widget.set(val)
            else:
                widget = tk.Entry(frame, width=20)
                widget.insert(0, str(val))
                widget.pack(side=tk.LEFT)
                original_values[key] = str(val)
                
                if weight is not None:
                    calc_lbl = tk.Label(frame, text="", fg="#1a73e8", bg="#f5f5f5", font=("Arial", 9, "bold"))
                    calc_lbl.pack(side=tk.LEFT, padx=10)
                    
                    def update_lbl(event=None, w=weight, entry=widget, l=calc_lbl, k=key):
                        l.config(fg="#1a73e8")
                        raw = entry.get().strip()
                        if not raw or raw == original_values.get(k, ""):
                            l.config(text="")
                            return
                        try:
                            if '/' in raw:
                                obt, total = map(float, raw.split('/'))
                                res = (obt/total)*w if total != 0 else 0
                                l.config(text=f"➜ {res:.2f} / {w}")
                            else:
                                v = float(raw)
                                try: base = float(base_mark_var.get())
                                except: base = 100.0
                                res = (v/base)*w if base != 0 else 0
                                l.config(text=f"➜ {res:.2f} / {w}")
                        except:
                            l.config(text="➜ Invalid format", fg="red")
                            
                    def apply_conversion(event=None, w=weight, entry=widget, l=calc_lbl, k=key):
                        raw = entry.get().strip()
                        if not raw or raw == original_values.get(k, ""):
                            return "break"
                        try:
                            if '/' in raw:
                                obt, total = map(float, raw.split('/'))
                                res = (obt/total)*w if total != 0 else 0
                            else:
                                v = float(raw)
                                try: base = float(base_mark_var.get())
                                except: base = 100.0
                                res = (v/base)*w if base != 0 else 0
                            
                            final_str = f"{res:.2f}"
                            entry.delete(0, tk.END)
                            entry.insert(0, final_str)
                            original_values[k] = final_str 
                            l.config(text=f"✓ Locked: {final_str}", fg="green")
                        except:
                            l.config(text="➜ Invalid format", fg="red")
                        return "break" 

                    widget.bind("<KeyRelease>", update_lbl)
                    widget.bind("<Return>", apply_conversion)
                    calc_labels.append(update_lbl)
                    
            entries[key] = widget
            
        tk.Label(scroll_frame, text="Basic Info", font=("Arial", 10, "bold"), bg="#f5f5f5", fg="blue").pack(fill=tk.X, padx=20, pady=(10,5))
        add_field("Card ID:", "card_id", old_cid)
        add_field("Name:", "name", student_data['name'])
        add_field("Student ID:", "student_id", student_data.get('student_id', ''))
        add_field("Blood Group:", "blood_group", student_data.get('blood_group', 'Unknown'), is_combo=True, combo_vals=['A+', 'A-', 'B+', 'B-', 'AB+', 'AB-', 'O+', 'O-', 'Unknown'])
        add_field("Phone:", "phone", student_data.get('phone', ''))
        add_field("Course:", "course", student_data.get('course', ''), is_combo=True)
        
        tk.Label(scroll_frame, text="Academic Scores (Press ENTER in box to lock conversion)", font=("Arial", 10, "bold"), bg="#f5f5f5", fg="green").pack(fill=tk.X, padx=20, pady=(20,5))
        
        add_field("MID Quiz (20%):", "mid_quiz", student_data.get('mid_quiz', ''), weight=20)
        add_field("MID Marks (40%):", "mid_marks", student_data.get('mid_marks', ''), weight=40)
        add_field("MID OBE (20%):", "mid_obe", student_data.get('mid_obe', ''), weight=20)
        add_field("MID Att (10%):", "mid_att", student_data.get('mid_att', ''), weight=10)
        add_field("MID Other (10%):", "mid_other", student_data.get('mid_other', ''), weight=10)
        
        add_field("FINAL Quiz (20%):", "final_quiz", student_data.get('final_quiz', ''), weight=20)
        add_field("FINAL Marks (40%):", "final_marks", student_data.get('final_marks', ''), weight=40)
        add_field("FINAL OBE (20%):", "final_obe", student_data.get('final_obe', ''), weight=20)
        add_field("FINAL Att (10%):", "final_att", student_data.get('final_att', ''), weight=10)
        add_field("FINAL Other (10%):", "final_other", student_data.get('final_other', ''), weight=10)

        def save_changes():
            new_cid = entries['card_id'].get().strip()
            new_name = entries['name'].get().strip()
            new_sid = entries['student_id'].get().strip()
            
            if not new_cid and not new_sid: 
                messagebox.showerror("Error", "Either Card ID or Student ID is required.")
                return

            if new_cid != old_cid and new_cid in self.students:
                messagebox.showerror("Error", "This new Card ID already exists!")
                return
            
            if new_cid != old_cid:
                del self.students[old_cid]
            
            final_key = new_cid if new_cid else new_sid

            def convert_mark(raw_val, weight, key):
                raw_val = raw_val.strip()
                if not raw_val: return ""
                if raw_val == original_values.get(key, ""): return raw_val

                try:
                    if '/' in raw_val:
                        obt, total = map(float, raw_val.split('/'))
                        if total == 0: return "0"
                        return str(round((obt / total) * weight, 2))
                    else:
                        v = float(raw_val)
                        try: base = float(base_mark_var.get())
                        except: base = 100.0
                        if base == 0: return "0"
                        return str(round((v / base) * weight, 2))
                except:
                    return raw_val

            self.students[final_key] = {
                "name": new_name,
                "student_id": new_sid,
                "phone": entries['phone'].get().strip(),
                "course": entries['course'].get(),
                "blood_group": entries['blood_group'].get().strip(),
                
                "mid_quiz": convert_mark(entries['mid_quiz'].get(), 20, "mid_quiz"),
                "mid_marks": convert_mark(entries['mid_marks'].get(), 40, "mid_marks"),
                "mid_obe": convert_mark(entries['mid_obe'].get(), 20, "mid_obe"),
                "mid_att": convert_mark(entries['mid_att'].get(), 10, "mid_att"),
                "mid_other": convert_mark(entries['mid_other'].get(), 10, "mid_other"),
                
                "final_quiz": convert_mark(entries['final_quiz'].get(), 20, "final_quiz"),
                "final_marks": convert_mark(entries['final_marks'].get(), 40, "final_marks"),
                "final_obe": convert_mark(entries['final_obe'].get(), 20, "final_obe"),
                "final_att": convert_mark(entries['final_att'].get(), 10, "final_att"),
                "final_other": convert_mark(entries['final_other'].get(), 10, "final_other"),
            }
            self.save_database()
            self.refresh_student_table()
            messagebox.showinfo("Success", "Record updated! Marks were automatically scaled to their respective percentages.")
            edit_win.destroy()
            
        tk.Button(scroll_frame, text="Save Changes", command=save_changes, bg="#4CAF50", fg="white", font=("Arial", 11, "bold")).pack(pady=30)

    def delete_student(self):
        sel = self.stud_tree.selection()
        if not sel: return
        if not messagebox.askyesno("Confirm", "Delete this student completely?"): return
        
        selected_id = sel[0]
        cid = selected_id.rsplit('_', 1)[0]
        
        if cid not in self.students:
            vals = self.stud_tree.item(sel[0])['values']
            sid = str(vals[2])
            for k, v in self.students.items():
                if v.get('student_id') == sid:
                    cid = k
                    break
        
        if cid in self.students: 
            del self.students[cid]
            self.save_database()
            self.refresh_student_table()
        else: 
            messagebox.showerror("Error", "Could not find record to delete.")
    
    # ==========================================
    # TAB 3: COURSE MANAGEMENT
    # ==========================================
    def setup_course_tab(self):
        container = tk.Frame(self.tab_courses, bg="#f5f5f5")
        container.place(relx=0.5, rely=0.5, anchor="center", width=850, height=650)
        
        tk.Label(container, text="Manage Courses", font=("Arial", 18, "bold"), bg="#f5f5f5").grid(row=0, columnspan=2, pady=15)
        fields_frame = tk.Frame(container, bg="#f5f5f5")
        fields_frame.grid(row=1, columnspan=2)
        
        self.course_entries = {}
        def create_row(row_idx, label, key):
            tk.Label(fields_frame, text=label, bg="#f5f5f5", font=("Arial", 10)).grid(row=row_idx, column=0, sticky="e", pady=10, padx=10)
            entry = tk.Entry(fields_frame, width=30)
            entry.grid(row=row_idx, column=1, pady=10, sticky="w")
            self.course_entries[key] = entry
            return entry
            
        create_row(0, "Course Name:", "c_name")
        create_row(1, "Course ID:", "c_id")
        create_row(2, "Section:", "c_sec")
        
        tk.Label(fields_frame, text="Select Days:", bg="#f5f5f5", font=("Arial", 10)).grid(row=3, column=0, sticky="e", pady=10, padx=10)
        days_frame = tk.Frame(fields_frame, bg="#f5f5f5")
        days_frame.grid(row=3, column=1, sticky="w", pady=10)
        self.days_vars = {}
        days_list = ["SUN", "MON", "TUE", "WED", "THU", "FRI", "SAT"]
        for day in days_list: 
            var = tk.BooleanVar()
            self.days_vars[day] = var
            tk.Checkbutton(days_frame, text=day, variable=var, bg="#f5f5f5").pack(side=tk.LEFT, padx=2)
            
        create_row(4, "Time (e.g., 10:00 AM):", "c_time")
        create_row(5, "Max Capacity:", "c_cap")
        
        btn_frame = tk.Frame(container, bg="#f5f5f5")
        btn_frame.grid(row=2, columnspan=2, pady=20)
        tk.Button(btn_frame, text="➕ Add Course", command=self.add_course, bg="#2196F3", fg="white", font=("Arial", 11, "bold"), width=15).pack(side=tk.LEFT, padx=10)
        tk.Button(btn_frame, text="🔄 Update Selected", command=self.update_course, bg="#FF9800", fg="white", font=("Arial", 11, "bold"), width=15).pack(side=tk.LEFT, padx=10)
        tk.Button(btn_frame, text="🗑️ Delete Selected", command=self.delete_course, bg="#F44336", fg="white", font=("Arial", 11, "bold"), width=15).pack(side=tk.LEFT, padx=10)
        
        tk.Label(container, text="Existing Courses:", bg="#f5f5f5", font=("Arial", 10, "bold")).grid(row=3, columnspan=2, pady=(10,5))
        cols = ("Name", "ID", "Section", "Day", "Time", "Cap")
        self.course_tree = ttk.Treeview(container, columns=cols, show='headings', height=8)
        for col in cols: 
            self.course_tree.heading(col, text=col)
            self.course_tree.column(col, width=150 if col=="Name" else 80, anchor="center")
        self.course_tree.bind("<<TreeviewSelect>>", self.on_course_select)
        self.course_tree.grid(row=4, columnspan=2, padx=20, sticky="ew")
        
        self.refresh_course_list()

    def add_course(self):
        data = self._get_form_data()
        if not data: return
        course_display_name = f"{data['c_name']} ({data['c_sec']})"
        if course_display_name in self.courses: 
            messagebox.showerror("Error", "This Course/Section already exists!")
            return
        self.courses[course_display_name] = data
        self.save_courses_db()
        self.refresh_course_list()
        self._clear_form()

    def update_course(self):
        if not self.editing_course_key: return
        data = self._get_form_data()
        if not data: return
        new_key = f"{data['c_name']} ({data['c_sec']})"
        if new_key != self.editing_course_key and new_key in self.courses: 
            messagebox.showerror("Error", "Conflict.")
            return
        if new_key != self.editing_course_key: 
            del self.courses[self.editing_course_key]
        self.courses[new_key] = data
        self.save_courses_db()
        self.refresh_course_list()
        self._clear_form()

    def delete_course(self):
        if not self.course_tree.selection(): return
        if not messagebox.askyesno("Confirm", "Delete?"): return
        vals = self.course_tree.item(self.course_tree.selection())['values']
        key = f"{vals[0]} ({vals[2]})"
        if key in self.courses: 
            del self.courses[key]
            self.save_courses_db()
            self.refresh_course_list()

    def on_course_select(self, event):
        sel = self.course_tree.selection()
        if not sel: return
        vals = self.course_tree.item(sel)['values']
        key = f"{vals[0]} ({vals[2]})"
        if key in self.courses:
            data = self.courses[key]
            self.editing_course_key = key
            
            self.course_entries['c_name'].delete(0, tk.END)
            self.course_entries['c_name'].insert(0, data['c_name'])
            self.course_entries['c_id'].delete(0, tk.END)
            self.course_entries['c_id'].insert(0, data['c_id'])
            self.course_entries['c_sec'].delete(0, tk.END)
            self.course_entries['c_sec'].insert(0, data['c_sec'])
            self.course_entries['c_time'].delete(0, tk.END)
            self.course_entries['c_time'].insert(0, data['c_time'])
            self.course_entries['c_cap'].delete(0, tk.END)
            self.course_entries['c_cap'].insert(0, data['c_cap'])
            
            for var in self.days_vars.values(): var.set(False)
            if data.get('c_days'):
                for d in data['c_days'].split(','): 
                    if d in self.days_vars: 
                        self.days_vars[d].set(True)

    def _get_form_data(self):
        data = {key: entry.get().strip() for key, entry in self.course_entries.items()}
        selected_days = [day for day, var in self.days_vars.items() if var.get()]
        data['c_days'] = ",".join(selected_days)
        if not all(data.values()) or not selected_days: 
            return None
        return data

    def _clear_form(self):
        for entry in self.course_entries.values(): 
            entry.delete(0, tk.END)
        for var in self.days_vars.values(): 
            var.set(False)
        self.editing_course_key = None

    def refresh_course_list(self):
        for item in self.course_tree.get_children(): 
            self.course_tree.delete(item)
        for c_key, c_data in self.courses.items(): 
            self.course_tree.insert("", "end", values=(c_data['c_name'], c_data['c_id'], c_data['c_sec'], c_data['c_days'], c_data['c_time'], c_data['c_cap']))

    # ==========================================
    # TAB 4: REGISTRATION
    # ==========================================
    def setup_registration_tab(self):
        form_frame = tk.Frame(self.tab_register, bg="#f5f5f5")
        form_frame.place(relx=0.5, rely=0.5, anchor="center")
        tk.Label(form_frame, text="New Student Registration", font=("Arial", 18, "bold"), bg="#f5f5f5").grid(row=0, columnspan=2, pady=25)
        v_pad = 12
        tk.Label(form_frame, text="Full Name:", bg="#f5f5f5", font=("Arial", 11)).grid(row=1, column=0, sticky="e", pady=v_pad, padx=10)
        self.reg_name = tk.Entry(form_frame, width=35, font=("Arial", 11))
        self.reg_name.grid(row=1, column=1, pady=v_pad, sticky="w")
        tk.Label(form_frame, text="Student ID:", bg="#f5f5f5", font=("Arial", 11)).grid(row=2, column=0, sticky="e", pady=v_pad, padx=10)
        self.reg_student_id = tk.Entry(form_frame, width=35, font=("Arial", 11))
        self.reg_student_id.grid(row=2, column=1, pady=v_pad, sticky="w")
        tk.Label(form_frame, text="Select Course:", bg="#f5f5f5", font=("Arial", 11)).grid(row=3, column=0, sticky="e", pady=v_pad, padx=10)
        self.reg_course_var = tk.StringVar()
        self.reg_course_combo = ttk.Combobox(form_frame, textvariable=self.reg_course_var, width=33, state="readonly", font=("Arial", 11))
        self.reg_course_combo.grid(row=3, column=1, pady=v_pad, sticky="w")
        tk.Label(form_frame, text="Parent Phone:", bg="#f5f5f5", font=("Arial", 11)).grid(row=4, column=0, sticky="e", pady=v_pad, padx=10)
        self.reg_phone = tk.Entry(form_frame, width=35, font=("Arial", 11))
        self.reg_phone.grid(row=4, column=1, pady=v_pad, sticky="w")
        
        tk.Label(form_frame, text="Blood Group:", bg="#f5f5f5", font=("Arial", 11)).grid(row=5, column=0, sticky="e", pady=v_pad, padx=10)
        self.reg_bg_var = tk.StringVar()
        self.reg_bg_combo = ttk.Combobox(form_frame, textvariable=self.reg_bg_var, width=33, state="readonly", font=("Arial", 11), values=['A+', 'A-', 'B+', 'B-', 'AB+', 'AB-', 'O+', 'O-', 'Unknown'])
        self.reg_bg_combo.current(8)
        self.reg_bg_combo.grid(row=5, column=1, pady=v_pad, sticky="w")

        tk.Label(form_frame, text="Scan Card ID:", bg="#f5f5f5", font=("Arial", 11, "bold"), fg="blue").grid(row=6, column=0, sticky="e", pady=v_pad, padx=10)
        self.reg_card_id = tk.Entry(form_frame, width=35, bg="#e8f0fe", font=("Arial", 11))
        self.reg_card_id.grid(row=6, column=1, pady=v_pad, sticky="w")
        
        tk.Button(form_frame, text="💾 Save to Database", command=self.save_student, bg="#2196F3", fg="white", font=("Arial", 11, "bold"), width=30).grid(row=7, columnspan=2, pady=30)
        self.refresh_course_dropdown()

    def refresh_course_dropdown(self):
        course_options = []
        for c_key, data in self.courses.items():
            label = f"{data['c_name']} | ID:{data['c_id']} | Sec:{data['c_sec']} | {data['c_days']}"
            course_options.append(label)
        self.reg_course_combo['values'] = course_options
        if course_options: self.reg_course_combo.current(0)
        else: self.reg_course_combo.set("No courses available")

    def save_student(self):
        cid = self.reg_card_id.get().strip()
        name = self.reg_name.get().strip()
        sid = self.reg_student_id.get().strip()
        course_str = self.reg_course_var.get().strip()
        ph = self.reg_phone.get().strip()
        bg = self.reg_bg_var.get().strip()
        
        if not name or not sid or not course_str or course_str == "No courses available":
            messagebox.showerror("Error", "Name, ID, and Course are required.")
            return
        
        db_key = cid if cid else sid
        
        if db_key in self.students:
            messagebox.showerror("Error", f"ID '{db_key}' already registered!")
            return
        
        self.students[db_key] = {"name": name, "student_id": sid, "course": course_str, "phone": ph, "blood_group": bg}
        self.save_database()
        
        messagebox.showinfo("Success", f"Student {name} registered!")
        
        self.reg_name.delete(0, tk.END)
        self.reg_student_id.delete(0, tk.END)
        self.reg_card_id.delete(0, tk.END)
        self.reg_phone.delete(0, tk.END)
        self.reg_bg_combo.current(8)

    # ==========================================
    # TAB 5: GOOGLE FORMS IMPORT
    # ==========================================
    def setup_google_forms_tab(self):
        container = tk.Frame(self.tab_google_forms, bg="#f5f5f5")
        container.place(relx=0.5, rely=0.5, anchor="center")
        tk.Label(container, text="Import Attendance from Google Forms", font=("Arial", 18, "bold"), bg="#f5f5f5", fg="#1976D2").pack(pady=20)
        date_frame = tk.Frame(container, bg="#f5f5f5")
        date_frame.pack(pady=10)
        tk.Label(date_frame, text="Select Date for Import:", font=("Arial", 11, "bold"), bg="#f5f5f5").pack(side=tk.LEFT)
        
        if TKCALENDAR_INSTALLED:
            self.cal_import = DateEntry(date_frame, width=12, background='#2196F3', foreground='white', borderwidth=2, date_pattern='yyyy-mm-dd')
            self.cal_import.pack(side=tk.LEFT, padx=10)
        else: 
            tk.Label(date_frame, text="(Install tkcalendar)", font=("Arial", 9), fg="red").pack(side=tk.LEFT, padx=10)
            
        tk.Label(container, text="Select Target Course:", font=("Arial", 11, "bold"), bg="#f5f5f5").pack(pady=(20, 5))
        self.import_course_combo = ttk.Combobox(container, textvariable=self.import_course_var, width=40, state="readonly")
        self.import_course_combo.pack(pady=5)
        
        self.refresh_import_course_dropdown()
        btn_frame = tk.Frame(container, bg="#f5f5f5")
        btn_frame.pack(pady=30)
        tk.Button(btn_frame, text="📂 Upload CSV / Excel", command=self.import_google_form_data, bg="#FF9800", fg="white", font=("Arial", 14, "bold"), padx=20, pady=10).pack()
        tk.Label(container, text="Note: File must have a 'Student ID' column.\nMatched students will be marked Present (1).", font=("Arial", 9, "italic"), bg="#f5f5f5", fg="gray").pack(pady=20)

    def refresh_import_course_dropdown(self):
        course_options = []
        for c_key, data in self.courses.items(): 
            label = f"{data['c_name']} | ID:{data['c_id']} | Sec:{data['c_sec']} | {data['c_days']}"
            course_options.append(label)
        self.import_course_combo['values'] = course_options
        if course_options: 
            self.import_course_combo.current(0)

    def import_google_form_data(self):
        if TKCALENDAR_INSTALLED: 
            import_date = self.cal_import.get_date().strftime("%Y-%m-%d")
        else: 
            import_date = datetime.now().strftime("%Y-%m-%d")
            
        course_str = self.import_course_var.get()
        if not course_str: 
            messagebox.showerror("Error", "Please select a course.")
            return
            
        try:
            parts = course_str.split('|')
            c_name = parts[0].strip()
            c_sec = parts[2].split(':')[1].strip()
            history_course_key = f"{c_name} ({c_sec})"
        except: 
            messagebox.showerror("Error", "Invalid course format.")
            return
            
        file_path = filedialog.askopenfilename(title="Select Google Form File", filetypes=[("Data Files", "*.csv *.xlsx *.xls")])
        if not file_path: return
        
        try:
            if file_path.endswith('.csv'): df = pd.read_csv(file_path)
            else: df = pd.read_excel(file_path)
        except Exception as e: 
            messagebox.showerror("Error", f"Could not read file: {e}")
            return
            
        possible_cols = ["Student ID", "student id", "ID", "id", "Id", "Card ID", "Registration Number"]
        id_col = None
        for col in df.columns:
            if col.strip() in possible_cols: 
                id_col = col
                break
                
        if not id_col: 
            messagebox.showerror("Error", f"Could not find a 'Student ID' column.\nFound: {list(df.columns)}")
            return
            
        matched_count = 0
        sid_to_cid = {}
        for cid, info in self.students.items():
            s_id = str(info.get('student_id', '')).strip()
            if s_id: 
                sid_to_cid[s_id] = cid
                
        if import_date not in self.history: 
            self.history[import_date] = {}
        if history_course_key not in self.history[import_date]: 
            self.history[import_date][history_course_key] = []
            
        existing_records = self.history[import_date][history_course_key]
        existing_cids = {r['id'] for r in existing_records}
        
        for index, row in df.iterrows():
            form_sid = str(row[id_col]).strip()
            if form_sid in sid_to_cid:
                cid = sid_to_cid[form_sid]
                if cid not in existing_cids:
                    s_info = self.students[cid]
                    new_rec = {"id": cid, "name": s_info['name'], "student_id": s_info.get('student_id', ''), "time": datetime.now().strftime("%H:%M:%S"), "status": "1", "phone": s_info.get('phone', '')}
                    self.history[import_date][history_course_key].append(new_rec)
                    existing_cids.add(cid)
                    matched_count += 1
                    
        self.save_history()
        messagebox.showinfo("Import Success", f"Successfully marked {matched_count} students as Present for {import_date}.")

    # ==========================================
    # TAB 6: FACULTY ACCESS TAB
    # ==========================================
    def setup_faculty_tab(self):
        container = tk.Frame(self.tab_faculty, bg="#f5f5f5")
        container.place(relx=0.5, rely=0.5, anchor="center")
        tk.Label(container, text="Faculty Profile Management", font=("Arial", 18, "bold"), bg="#f5f5f5", fg="#1a73e8").pack(pady=20)
        self.fac_entries = {}
        def create_fac_section(title, fields):
            lf = tk.LabelFrame(container, text=title, font=("Arial", 11, "bold"), bg="#f5f5f5", padx=15, pady=10)
            lf.pack(fill="x", pady=10, padx=5)
            for lbl, key in fields:
                row = tk.Frame(lf, bg="#f5f5f5")
                row.pack(fill="x", pady=2)
                tk.Label(row, text=lbl, width=20, anchor="w", bg="#f5f5f5").pack(side="left")
                entry = tk.Entry(row, width=30)
                entry.insert(0, self.faculty_info.get(key, ""))
                entry.pack(side="left", fill="x", expand=True)
                self.fac_entries[key] = entry
                
        create_fac_section("Organization Info", [("Organization", "org_name"), ("Faculty ID", "org_fac_id"), ("Department", "dept"), ("Org Email", "org_email")])
        create_fac_section("Personal Info", [("First Name", "first_name"), ("Last Name", "last_name"), ("Phone", "phone"), ("Personal Email", "pers_email")])
        create_fac_section("Account Security", [("Security Question", "sec_question"), ("Security Answer", "sec_answer")])
        
        btn_frame = tk.Frame(container, bg="#f5f5f5")
        btn_frame.pack(pady=20)
        tk.Button(btn_frame, text="Update Profile", command=self.update_faculty_profile, bg="#4CAF50", fg="white", font=("Arial", 11, "bold"), width=15).pack(side="left", padx=10)
        tk.Button(btn_frame, text="Log Out", command=self.logout, bg="#F44336", fg="white", font=("Arial", 11, "bold"), width=15).pack(side="left", padx=10)

    def update_faculty_profile(self):
        for key, entry in self.fac_entries.items(): 
            self.faculty_info[key] = entry.get().strip()
        try:
            all_faculty = dict(MEMORY_FACULTY_DB)
            if os.path.exists(FACULTY_FILE):
                with open(FACULTY_FILE, 'r', encoding='utf-8') as f: 
                    all_faculty.update(json.load(f))
            username = self.faculty_info.get('reg_username')
            if username:
                all_faculty[username] = self.faculty_info
                MEMORY_FACULTY_DB[username] = self.faculty_info
                with open(FACULTY_FILE, 'w', encoding='utf-8') as f: 
                    json.dump(all_faculty, f, indent=4)
                messagebox.showinfo("Success", "Profile updated successfully!")
                t_name = f"{self.faculty_info.get('first_name')} {self.faculty_info.get('last_name')}"
                self.parent.title(f"{self.faculty_info.get('org_name')} - Smart Manager Pro | Logged in as: {t_name}")
        except Exception as e: 
            messagebox.showerror("Error", f"Failed to save: {e}")

    def logout(self):
        if messagebox.askyesno("Logout", "Are you sure you want to log out?"): 
            self.logout_cb()

    # ==========================================
    # TAB 7: DEVELOPER CONTACT TAB
    # ==========================================
    def setup_developer_tab(self):
        container = tk.Frame(self.tab_developer, bg="#f5f5f5")
        container.place(relx=0.5, rely=0.5, anchor="center")
        tk.Label(container, text="Developer Information", font=("Arial", 20, "bold"), bg="#f5f5f5", fg="#1a73e8").pack(pady=20)
        info_frame = tk.LabelFrame(container, text="Contact Details", font=("Arial", 11, "bold"), bg="#f5f5f5", padx=20, pady=15)
        info_frame.pack(fill="x", pady=10)
        details = [("Developer Name:", "Alif Arman"), ("Email:", "sheak745@gmail.com"), ("Phone:", "+8801717048885"), ("Version:", "1.0.0 Beta")]
        for label, value in details:
            row = tk.Frame(info_frame, bg="#f5f5f5")
            row.pack(fill="x", pady=5)
            tk.Label(row, text=label, width=15, anchor="w", font=("Arial", 10, "bold"), bg="#f5f5f5").pack(side="left")
            tk.Label(row, text=value, font=("Arial", 10), bg="#f5f5f5", fg="#333").pack(side="left")
        tk.Label(container, text="© 2023 Smart School Manager. All rights reserved.", font=("Arial", 8), bg="#f5f5f5", fg="gray").pack(side="bottom", pady=30)

    # ==========================================
    # TAB 8: DATA ANALYTICS & AI 
    # ==========================================
    def setup_analytics_tab(self):
        container = tk.Frame(self.tab_analytics, bg="#f5f5f5")
        container.pack(fill=tk.BOTH, expand=True)

        if not ANALYTICS_INSTALLED:
            tk.Label(container, text="Analytics modules missing.\nRun: pip install matplotlib scikit-learn", 
                     font=("Arial", 14), fg="red").pack(pady=50)
            return

        control_frame = tk.Frame(container, bg="#f5f5f5")
        control_frame.pack(fill=tk.X, padx=10, pady=10)

        tk.Label(control_frame, text="Select Course for Analysis:", bg="#f5f5f5", font=("Arial", 11, "bold")).pack(side=tk.LEFT)
        self.analytics_course_combo = ttk.Combobox(control_frame, textvariable=self.analytics_course_var, width=30, state="readonly")
        self.analytics_course_combo.pack(side=tk.LEFT, padx=10)

        tk.Label(control_frame, text="Student ID:", bg="#f5f5f5", font=("Arial", 10, "bold")).pack(side=tk.LEFT, padx=(20, 0))
        self.analytics_student_combo = ttk.Combobox(control_frame, textvariable=self.analytics_student_var, width=20, state="readonly")
        self.analytics_student_combo.pack(side=tk.LEFT, padx=5)

        self.refresh_analytics_course_dropdown()
        self.analytics_course_combo.bind("<<ComboboxSelected>>", self.refresh_analytics_student_dropdown)

        tk.Button(control_frame, text="📈 Show Student Graph", command=self.plot_student_analysis, bg="#2196F3", fg="white").pack(side=tk.LEFT, padx=10)
        tk.Button(control_frame, text="🤖 AI Insight", command=self.generate_ai_insight, bg="#4CAF50", fg="white").pack(side=tk.LEFT, padx=5)
        tk.Button(control_frame, text="📂 Load External CSV", command=self.analyze_external_file, bg="#FF9800", fg="white").pack(side=tk.LEFT, padx=20)

        self.plot_frame = tk.Frame(container, bg="white", relief=tk.SUNKEN, bd=2)
        self.plot_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

        self.refresh_analytics_student_dropdown(None)

    def refresh_analytics_course_dropdown(self):
        course_options = []
        for c_key, data in self.courses.items():
            label = f"{data['c_name']} | ID:{data['c_id']} | Sec:{data['c_sec']} | {data['c_days']}"
            course_options.append(label)
        self.analytics_course_combo['values'] = course_options
        if course_options: 
            self.analytics_course_combo.current(0)

    def refresh_analytics_student_dropdown(self, event):
        course_str = self.analytics_course_var.get()
        if not course_str: return
        
        student_ids = []
        for cid, info in self.students.items():
            if info.get('course') == course_str:
                sid = info.get('student_id', 'Unknown')
                student_ids.append(sid)
        
        self.analytics_student_combo['values'] = sorted(student_ids)
        if student_ids: 
            self.analytics_student_combo.current(0)
        else: 
            self.analytics_student_combo.set("")

    def get_course_data_for_analytics(self):
        course_str = self.analytics_course_var.get()
        if not course_str: return None
        
        try:
            parts = course_str.split('|')
            c_name = parts[0].strip()
            c_sec = parts[2].split(':')[1].strip()
            history_course_key = f"{c_name} ({c_sec})"
        except: 
            return None

        student_stats = {}
        total_class_days = 0
        
        for date_key, courses in self.history.items():
            if history_course_key in courses:
                total_class_days += 1
                for rec in courses[history_course_key]:
                    if rec['id'] not in student_stats:
                        student_stats[rec['id']] = {'present': 0}
                    if rec['status'] == "1":
                        student_stats[rec['id']]['present'] += 1
        
        if total_class_days == 0: 
            total_class_days = 1

        data = []
        for cid, info in self.students.items():
            if info.get('course') != course_str: continue
            
            stats = student_stats.get(cid, {'present': 0})
            att_pct = (stats['present'] / total_class_days) * 100
            
            def sf(k):
                try: return float(info.get(k, 0))
                except: return 0.0

            data.append({
                'Name': info['name'],
                'SID': info.get('student_id'),
                'Attendance': att_pct,
                'Q1': sf('mid_quiz'), 
                'Q2': sf('mid_marks'), 
                'OBE': sf('mid_obe'), 
                'MidAtt': sf('mid_att'),
                'MidOther': sf('mid_other'),
                
                'FinalQ': sf('final_quiz'),
                'Final': sf('final_marks'),
                'FinalOBE': sf('final_obe'),
                'FinalAtt': sf('final_att'),
                'FinalOther': sf('final_other')
            })
            
        return pd.DataFrame(data)

    def plot_student_analysis(self):
        df = self.get_course_data_for_analytics()
        if df is None or df.empty: 
            messagebox.showinfo("Info", "No data available.")
            return
        
        target_sid = self.analytics_student_var.get()
        student_row = df[df['SID'] == target_sid]
        
        if student_row.empty: 
            messagebox.showinfo("Error", "Student not found.")
            return
        
        row = student_row.iloc[0]
        
        mid_q = row['Q1']
        mid_m = row['Q2']
        mid_obe = row['OBE']
        mid_att = row.get('MidAtt', 0) 
        mid_other = row.get('MidOther', 0)
        mid_total = mid_q + mid_m + mid_obe + mid_att + mid_other

        fin_q = row['FinalQ']
        fin_m = row['Final']
        fin_obe = row['FinalOBE']
        fin_att = row.get('FinalAtt', 0)
        fin_other = row.get('FinalOther', 0)
        final_total = fin_q + fin_m + fin_obe + fin_att + fin_other
        
        total_grand = (mid_total*0.4) + (final_total*0.6)
        
        if total_grand >= 90: grade = "A+"
        elif total_grand >= 85: grade = "A"
        elif total_grand >= 80: grade = "B+"
        elif total_grand >= 75: grade = "B"
        elif total_grand >= 70: grade = "C+"
        elif total_grand >= 65: grade = "C"
        elif total_grand >= 60: grade = "D+"
        elif total_grand >= 50: grade = "D"
        else: grade = "F"

        for widget in self.plot_frame.winfo_children(): 
            widget.destroy()
            
        plt.close('all')
        
        fig, ax = plt.subplots(figsize=(12, 5))
        labels = ['MID Quiz', 'Mid Marks', 'MID OBE', 'MID Total', 'Final Quiz', 'Final Marks', 'Final OBE', 'Final Total']
        values = [mid_q, mid_m, mid_obe, mid_total, fin_q, fin_m, fin_obe, final_total]
        colors = ['green', 'blue', 'orange', 'gold', 'purple', 'pink', 'cyan', 'gold']
        
        bars = ax.bar(labels, values, color=colors)
        
        max_val = max(values) if values else 100
        ax.set_ylim(0, (max_val * 1.35) + 5) 

        ax.tick_params(axis='both', labelsize=12)

        for bar in bars:
            height = bar.get_height()
            ax.text(bar.get_x() + bar.get_width()/2., height + (max_val * 0.02),
                    f'{height:.1f}', ha='center', va='bottom', fontsize=12, fontweight='bold')

        ax.set_title(f"{row['Name']} ({target_sid}) Performance Analysis", pad=20, fontsize=18, fontweight='bold')
        ax.set_ylabel("Marks", fontsize=14, fontweight='bold')
        
        fig.tight_layout(pad=2.0)
        fig.subplots_adjust(bottom=0.25) 
        fig.text(0.5, 0.02, f"ESTIMATED GRADE: {grade}", ha='center', fontsize=18, weight='bold')
        
        canvas = FigureCanvasTkAgg(fig, master=self.plot_frame)
        canvas.draw()
        canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)

    def generate_ai_insight(self):
        df = self.get_course_data_for_analytics()
        if df is None or len(df) < 5: 
            messagebox.showinfo("Info", "Need more student data (5+) for accurate AI analysis.")
            return
        
        for widget in self.plot_frame.winfo_children(): 
            widget.destroy()
            
        plt.close('all')
        
        X = df[['Attendance']].values
        y = df['Final'].values
        
        model = LinearRegression()
        model.fit(X, y)
        trend = model.coef_[0]
        
        fig, ax = plt.subplots(figsize=(8, 4))
        ax.scatter(X, y, color='blue')
        ax.plot(X, model.predict(X), color='red', linewidth=2)
        
        ax.tick_params(axis='both', labelsize=12)
        ax.set_title("AI Analysis: Attendance vs Final Performance", fontsize=16, fontweight='bold')
        ax.set_xlabel("Attendance %", fontsize=14, fontweight='bold')
        ax.set_ylabel("Final Marks", fontsize=14, fontweight='bold')
        
        insight = f"Insight: For every 1% increase in attendance, final marks tend to increase by {trend:.2f} marks."
        fig.text(0.5, 0.01, insight, ha='center', fontsize=14, style='italic', weight='bold')
        
        canvas = FigureCanvasTkAgg(fig, master=self.plot_frame)
        canvas.draw()
        canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)

    def analyze_external_file(self):
        file_path = filedialog.askopenfilename(
            title="Select Student Data CSV/Excel",
            filetypes=[("Data Files", "*.csv *.xlsx *.xls")]
        )
        if not file_path: return

        try:
            if file_path.endswith('.csv'): 
                df = pd.read_csv(file_path, header=1)
                if not any(c.lower().strip() in ['id', 'student id', 'student id', 'card id'] for c in df.columns.astype(str)):
                    df = pd.read_csv(file_path, header=0)
            else: 
                df = pd.read_excel(file_path, header=1)
                if not any(c.lower().strip() in ['id', 'student id', 'student id', 'card id'] for c in df.columns.astype(str)):
                    df = pd.read_excel(file_path, header=0)
        except Exception as e:
            messagebox.showerror("Error", f"Read failed: {e}")
            return
            
        df.columns = df.columns.astype(str).str.strip()

        def find_col(possible_names):
            for name in possible_names:
                for col in df.columns:
                    if str(col).lower().strip() == str(name).lower().strip():
                        return col
            return None

        id_col = find_col(['ID', 'Student ID', 'Student id', 'Card ID'])
        name_col = find_col(['Name', 'Student Name', 'StudentName'])
        total_col = find_col(['Total', 'TOTAL', 'Grand Total'])
        att_col = find_col(['Att', 'Attendance', 'Attend'])

        if not id_col:
            messagebox.showerror("Error", "Missing required column 'ID' or 'Student ID'. Ensure file matches a supported template.")
            return

        df.rename(columns={id_col: 'ID'}, inplace=True)
        if name_col: df.rename(columns={name_col: 'Name'}, inplace=True)
        else: df['Name'] = "Unknown"

        df.dropna(subset=['ID'], inplace=True)
        df = df[df['ID'].astype(str).str.strip() != '']
        df = df[df['ID'].astype(str).str.lower() != 'nan']

        dash = tk.Toplevel(self)
        dash.title("Data Analysis (External File)")
        dash.geometry("1100x750")
        
        nb = ttk.Notebook(dash)
        nb.pack(fill=tk.BOTH, expand=True)

        if total_col:
            df['Total_Num'] = pd.to_numeric(df[total_col], errors='coerce')
            
            f1 = tk.Frame(nb)
            nb.add(f1, text="Overall Performance")
            
            totals = df['Total_Num'].dropna()
            if not totals.empty:
                fig1, ax1 = plt.subplots(figsize=(6, 4))
                ax1.hist(totals, bins=10, color='skyblue', edgecolor='black')
                ax1.tick_params(axis='both', labelsize=12)
                ax1.set_title("Total Marks Distribution", fontsize=16, fontweight='bold')
                ax1.set_xlabel("Marks", fontsize=14, fontweight='bold')
                ax1.set_ylabel("Count", fontsize=14, fontweight='bold')
                c1 = FigureCanvasTkAgg(fig1, master=f1)
                c1.draw()
                c1.get_tk_widget().pack(fill=tk.BOTH, expand=True)
            else:
                tk.Label(f1, text="No valid numeric 'Total' data found to plot.", font=("Arial", 12)).pack(pady=20)
                
            f3 = tk.Frame(nb)
            nb.add(f3, text="At Risk Students")
            risk_df = df[df['Total_Num'] < 50].dropna(subset=['Total_Num', 'Name'])
            
            if not risk_df.empty:
                fig3, ax3 = plt.subplots(figsize=(8, 4))
                ax3.bar(risk_df['Name'].astype(str), risk_df['Total_Num'], color='red')
                ax3.set_title("Students At Risk (Marks < 50)", fontsize=16, fontweight='bold')
                ax3.tick_params(axis='y', labelsize=12)
                plt.setp(ax3.get_xticklabels(), rotation=45, ha='right', fontsize=12, fontweight='bold')
                c3 = FigureCanvasTkAgg(fig3, master=f3)
                c3.draw()
                c3.get_tk_widget().pack(fill=tk.BOTH, expand=True)
            else:
                tk.Label(f3, text="No At-Risk Students Found!", font=("Arial", 14)).pack(pady=50)

            if att_col:
                f4 = tk.Frame(nb)
                nb.add(f4, text="AI Insights")
                
                df['Att_Num'] = pd.to_numeric(df[att_col], errors='coerce')
                df_clean = df.dropna(subset=['Att_Num', 'Total_Num'])
                
                if len(df_clean) > 2:
                    X = df_clean[['Att_Num']].values
                    y = df_clean['Total_Num'].values
                    model = LinearRegression().fit(X, y)
                    trend = model.coef_[0]
                    
                    fig4, ax4 = plt.subplots(figsize=(6, 4))
                    ax4.scatter(X, y, color='blue')
                    ax4.plot(X, model.predict(X), color='red')
                    ax4.tick_params(axis='both', labelsize=12)
                    ax4.set_title(f"Attendance Impact (Trend: {trend:.2f})", fontsize=16, fontweight='bold')
                    c4 = FigureCanvasTkAgg(fig4, master=f4)
                    c4.draw()
                    c4.get_tk_widget().pack(side=tk.TOP, fill=tk.BOTH, expand=True)
                    
                    txt = f"Analysis shows that for every class attended, student marks increase by approx {trend:.1f} points."
                    tk.Label(f4, text=txt, font=("Arial", 14, "bold")).pack(pady=10)
                else:
                    tk.Label(f4, text="Not enough valid data points for AI analysis").pack(pady=50)

        df['Display'] = df['Name'].astype(str) + " (" + df['ID'].astype(str) + ")"
        name_list = sorted(df['Display'].unique().tolist())

        f_sw = tk.Frame(nb)
        nb.add(f_sw, text="Student-Wise (Bar Chart)")
        
        ctrl_frame = tk.Frame(f_sw, bg="#f0f0f0")
        ctrl_frame.pack(fill=tk.X, padx=10, pady=10)
        
        tk.Label(ctrl_frame, text="Search/Select Student:", bg="#f0f0f0", font=("Arial", 10, "bold", "italic"), fg="darkblue").pack(side=tk.LEFT, padx=(5, 2))
        
        id_var = tk.StringVar()
        id_combo = ttk.Combobox(ctrl_frame, textvariable=id_var, values=name_list, width=40)
        id_combo.pack(side=tk.LEFT, padx=(0, 15))
        
        def filter_id(event):
            val = id_var.get()
            if val == '': id_combo['values'] = name_list
            else: id_combo['values'] = [x for x in name_list if val.lower() in x.lower()]
                
        id_combo.bind('<KeyRelease>', filter_id)

        plot_area_4 = tk.Frame(f_sw, bg="white")
        plot_area_4.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        
        def show_individual_graph():
            try:
                sel_id = id_var.get().strip()
                if not sel_id: 
                    messagebox.showinfo("Info", "Select an ID first.")
                    return
                    
                matches = df[df['Display'] == sel_id]
                if matches.empty: return
                row = matches.iloc[0]
                
                for widget in plot_area_4.winfo_children(): widget.destroy()
                plt.close('all')
                
                def get_val(possible_cols):
                    for c in possible_cols:
                        for col in df.columns:
                            if str(col).lower().strip() == str(c).lower().strip():
                                v = row[col]
                                try:
                                    if pd.isna(v): return 0.0
                                    val_str = str(v).strip().lower()
                                    if val_str in ['', 'nan', 'a', 'absent', 'null']: return 0.0
                                    return float(val_str)
                                except: pass
                    return 0.0

                q1 = get_val(['Qz 1', 'Qz1', 'Quiz1', 'Quiz 1', 'Q1'])
                q2 = get_val(['Qz 2', 'Qz2', 'Quiz2', 'Quiz 2', 'Q2'])
                q3 = get_val(['Qz 3', 'Qz3', 'Quiz3', 'Quiz 3', 'Q3'])
                q4 = get_val(['Qz 4', 'Qz4', 'Quiz4', 'Quiz 4', 'Q4'])
                qbest = get_val(['Quiz T', 'QuizT', 'QuizBest', 'Best Quiz'])
                obe = get_val(['OBE', 'O.B.E', 'MID OBE'])
                att = get_val(['Att', 'Attendance', 'Attend'])
                perf = get_val(['Per', 'Performance', 'Perf', 'Perf.'])
                exam = get_val(['MID', 'Exam', 'MidTerm', 'Mid Term'])
                total = get_val(['Total', 'TOTAL', 'Grand Total'])
                
                labels = ['Quiz1', 'Quiz2', 'Quiz3', 'Quiz4', 'QuizBest', 'OBE', 'Attendance', 'Performance', 'Exam', 'Total']
                vals = [q1, q2, q3, q4, qbest, obe, att, perf, exam, total]
                colors = ['green', 'green', 'green', 'green', 'blue', 'orange', 'purple', 'gray', 'pink', 'gold']
                
                fig5, ax5 = plt.subplots(figsize=(10, 6))
                bars = ax5.bar(labels, vals, color=colors)
                
                max_h = max(vals) if vals and max(vals) > 0 else 100
                ax5.set_ylim(0, (max_h * 1.35) + 5)
                ax5.tick_params(axis='y', labelsize=12)
                
                for bar in bars:
                    height = bar.get_height()
                    if pd.isna(height): height = 0.0
                    ax5.text(bar.get_x() + bar.get_width()/2., height + (max_h * 0.02), f'{height:.0f}', ha='center', va='bottom', fontsize=12, fontweight='bold')
                
                ax5.set_ylabel("Marks", fontsize=14, fontweight='bold')
                plt.setp(ax5.get_xticklabels(), rotation=90, ha='center', fontsize=12, fontweight='bold')
                
                ax5.set_title(f"{sel_id}", fontsize=18, pad=15, fontweight='bold')
                
                grade_col = find_col(['Grade', 'Mid Grade', 'MID-Grade'])
                grade = str(row[grade_col]) if grade_col else "N/A"
                if grade.lower() == 'nan': grade = "N/A"
                
                fig5.tight_layout(pad=2.0)
                fig5.subplots_adjust(bottom=0.25) 
                fig5.text(0.5, 0.02, f"MID-Grade: {grade}", ha='center', fontsize=18, weight='bold')
                
                c5_canvas = FigureCanvasTkAgg(fig5, master=plot_area_4)
                c5_canvas.draw()
                c5_canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
                
            except Exception as e:
                messagebox.showerror("Graph Error", f"An error occurred while generating the graph:\n{str(e)}")

        tk.Button(ctrl_frame, text="View Graph", command=show_individual_graph, bg="#2196F3", fg="white").pack(side=tk.LEFT, padx=15)

    # ==========================================
    # TAB: CO ANALYSIS (NEW & IMPROVED UI)
    # ==========================================
    def setup_co_analysis_tab(self):
        container = tk.Frame(self.tab_co_analysis, bg="#f5f5f5")
        container.pack(fill=tk.BOTH, expand=True)

        style = ttk.Style()
        try:
            if "clam" in style.theme_names(): style.theme_use("clam")
        except: pass
        
        style.configure("CO.Treeview.Heading", background="#4a148c", foreground="white", font=("Arial", 10, "bold"))
        style.map("CO.Treeview.Heading", background=[('active', '#7b1fa2')])
        style.configure("CO.Treeview", rowheight=28, font=("Arial", 9), background="#ffffff", fieldbackground="#ffffff")

        # Top Control Bar (Row 1)
        top_frame1 = tk.Frame(container, bg="#f5f5f5")
        top_frame1.pack(fill=tk.X, padx=10, pady=(10, 5))
        
        tk.Label(top_frame1, text="Course:", bg="#f5f5f5", font=("Arial", 10, "bold")).pack(side=tk.LEFT, padx=(5, 2))
        self.co_course_var = tk.StringVar()
        self.co_course_combo = ttk.Combobox(top_frame1, textvariable=self.co_course_var, state="readonly", width=35)
        self.co_course_combo.pack(side=tk.LEFT, padx=(0, 15))
        self.co_course_combo.bind("<<ComboboxSelected>>", self.load_internal_co_data)
        
        tk.Label(top_frame1, text="Course Type Filter:", bg="#f5f5f5", font=("Arial", 10, "bold")).pack(side=tk.LEFT, padx=(5, 2))
        self.co_type_var = tk.StringVar(value="Theory and Lab")
        self.co_type_combo = ttk.Combobox(top_frame1, textvariable=self.co_type_var, state="readonly", width=15, values=["Theory", "Lab", "Theory and Lab"])
        self.co_type_combo.pack(side=tk.LEFT, padx=(0, 15))
        self.co_type_combo.bind("<<ComboboxSelected>>", lambda e: self.filter_co_tabs())

        tk.Button(top_frame1, text="📂 Load CO Analysis Excel(s)", command=self.load_co_data, bg="#9C27B0", fg="white", font=("Arial", 10, "bold")).pack(side=tk.RIGHT, padx=10)

        # Top Control Bar (Row 2)
        top_frame2 = tk.Frame(container, bg="#f5f5f5")
        top_frame2.pack(fill=tk.X, padx=10, pady=5)

        tk.Label(top_frame2, text="Student for Spider Chart:", bg="#f5f5f5", font=("Arial", 10, "bold")).pack(side=tk.LEFT, padx=(5, 2))
        self.co_spider_var = tk.StringVar()
        self.co_spider_combo = ttk.Combobox(top_frame2, textvariable=self.co_spider_var, state="readonly", width=35)
        self.co_spider_combo.pack(side=tk.LEFT, padx=5)

        tk.Button(top_frame2, text="🕸️ Show Student Chart", command=self.show_co_spider_chart, bg="#2196F3", fg="white", font=("Arial", 10, "bold")).pack(side=tk.LEFT, padx=10)
        tk.Button(top_frame2, text="🕸️ Overall Section Chart", command=self.show_overall_spider_chart, bg="#FF5722", fg="white", font=("Arial", 10, "bold")).pack(side=tk.LEFT, padx=5)

        # Summary Control Bar (Row 3)
        summary_frame = tk.Frame(container, bg="#f5f5f5")
        summary_frame.pack(fill=tk.X, padx=10, pady=(5, 10))

        tk.Label(summary_frame, text="Benchmark (% of students):", bg="#f5f5f5", font=("Arial", 10, "bold")).pack(side=tk.LEFT, padx=(5, 2))
        self.co_benchmark_var = tk.StringVar(value="60")
        tk.Spinbox(summary_frame, from_=0, to=100, textvariable=self.co_benchmark_var, width=5, font=("Arial", 10)).pack(side=tk.LEFT, padx=5)
        
        tk.Button(summary_frame, text="📊 Generate CO Summary Graphs", command=self.show_co_summary_graphs, bg="#4CAF50", fg="white", font=("Arial", 10, "bold")).pack(side=tk.LEFT, padx=15)

        self.co_nb = ttk.Notebook(container)
        self.co_nb.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)

        self.all_co_tab_frames = {} 
        self.co_tabs = {}
        self.co_dfs = {}
        self.spider_data = {}

        tab_names = ["Internal DB Records", "Mid Term Theory", "Mid Term Lab", "Final Term Theory", "Final Term Lab", "CO Attainment", "CO Summary"]

        for name in tab_names:
            frame = tk.Frame(self.co_nb, bg="white")
            self.all_co_tab_frames[name] = frame 

            tv = ttk.Treeview(frame, show="headings", style="CO.Treeview")
            
            def make_yview(tree):
                def _yview(*args):
                    if args and args[0] == 'scroll' and args[2] == 'units':
                        tree.yview('scroll', int(args[1]) * 4, 'units')
                    else:
                        tree.yview(*args)
                return _yview

            def make_xview(tree):
                def _xview(*args):
                    if args and args[0] == 'scroll' and args[2] == 'units':
                        tree.xview('scroll', int(args[1]) * 10, 'units')
                    else:
                        tree.xview(*args)
                return _xview

            vsb = ttk.Scrollbar(frame, orient="vertical", command=make_yview(tv))
            hsb = ttk.Scrollbar(frame, orient="horizontal", command=make_xview(tv))
            tv.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)
            
            def on_mousewheel_v(event, tree=tv):
                delta = event.delta
                num = getattr(event, 'num', 0)
                if num == 5 or delta < 0: tree.yview_scroll(4, "units")
                elif num == 4 or delta > 0: tree.yview_scroll(-4, "units")
                return "break"
                
            def on_mousewheel_h(event, tree=tv):
                delta = event.delta
                num = getattr(event, 'num', 0)
                if num == 5 or delta < 0: tree.xview_scroll(10, "units")
                elif num == 4 or delta > 0: tree.xview_scroll(-10, "units")
                return "break"

            tv.bind("<MouseWheel>", on_mousewheel_v)
            tv.bind("<Shift-MouseWheel>", on_mousewheel_h)
            tv.bind("<Button-4>", on_mousewheel_v)
            tv.bind("<Button-5>", on_mousewheel_v)
            tv.bind("<Shift-Button-4>", on_mousewheel_h)
            tv.bind("<Shift-Button-5>", on_mousewheel_h)
            
            tv.tag_configure('evenrow', background='#f3e5f5')
            tv.tag_configure('oddrow', background='#ffffff')

            vsb.pack(side=tk.RIGHT, fill=tk.Y)
            hsb.pack(side=tk.BOTTOM, fill=tk.X)
            tv.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

            self.co_tabs[name] = tv
            
        self.filter_co_tabs()

    def refresh_co_course_dropdown(self):
        course_options = []
        for c_key, data in self.courses.items():
            label = f"{data['c_name']} | ID:{data['c_id']} | Sec:{data['c_sec']} | {data['c_days']}"
            course_options.append(label)
        self.co_course_combo['values'] = course_options
        if course_options and not self.co_course_var.get():
            self.co_course_combo.current(0)

    def filter_co_tabs(self):
        if not hasattr(self, 'all_co_tab_frames'): return
        
        selected_type = self.co_type_var.get()
        
        for tab in self.co_nb.tabs():
            self.co_nb.forget(tab)
            
        for sheet_name, frame in self.all_co_tab_frames.items():
            name_lower = sheet_name.lower()
            show_tab = False
            
            if selected_type == "Theory and Lab":
                show_tab = True
            elif selected_type == "Theory":
                if "theory" in name_lower or "attainment" in name_lower or "summary" in name_lower or "internal" in name_lower:
                    show_tab = True
            elif selected_type == "Lab":
                if "lab" in name_lower or "attainment" in name_lower or "summary" in name_lower or "internal" in name_lower:
                    show_tab = True
                    
            if "theory" not in name_lower and "lab" not in name_lower and "attainment" not in name_lower and "summary" not in name_lower and "internal" not in name_lower:
                show_tab = True
                
            if show_tab:
                self.co_nb.add(frame, text=f" {sheet_name} ")

    def load_internal_co_data(self, event=None):
        course_str = self.co_course_var.get()
        if not course_str: return
        
        course_students = []
        for cid, info in self.students.items():
            if info.get('course') == course_str:
                course_students.append({
                    "Card ID": cid,
                    "Name": info.get('name', ''),
                    "Student ID": info.get('student_id', ''),
                    "Mid Quiz": info.get('mid_quiz', '0'),
                    "Mid Marks": info.get('mid_marks', '0'),
                    "Mid OBE": info.get('mid_obe', '0'),
                    "Final Quiz": info.get('final_quiz', '0'),
                    "Final Marks": info.get('final_marks', '0'),
                    "Final OBE": info.get('final_obe', '0')
                })
        
        df = pd.DataFrame(course_students)
        if df.empty:
            df = pd.DataFrame(columns=["Card ID", "Name", "Student ID", "Mid Quiz", "Mid Marks", "Mid OBE", "Final Quiz", "Final Marks", "Final OBE"])
            
        if "Internal DB Records" in self.co_tabs:
            tv = self.co_tabs["Internal DB Records"]
            tv.delete(*tv.get_children())
            
            col_names = list(df.columns)
            tv["columns"] = col_names
            for col in col_names:
                tv.heading(col, text=col)
                tv.column(col, width=120, anchor="center")
                
            for idx, row in df.iterrows():
                tag = 'evenrow' if idx % 2 == 0 else 'oddrow'
                tv.insert("", "end", values=list(row), tags=(tag,))
                
        self.spider_data.clear()
        names_list = []
        for idx, row in df.iterrows():
            try:
                name = str(row['Name']).strip()
                if name:
                    def safe_float(v):
                        try: return float(v)
                        except: return 0.0
                        
                    co_vals = [
                        safe_float(row['Mid Quiz']),
                        safe_float(row['Mid Marks']),
                        safe_float(row['Mid OBE']),
                        safe_float(row['Final Quiz']),
                        safe_float(row['Final Marks']),
                        safe_float(row['Final OBE'])
                    ]
                    
                    display_name = f"{name} ({row['Student ID']})"
                    names_list.append(display_name)
                    self.spider_data[display_name] = {
                        'cats': ['Mid Quiz', 'Mid Marks', 'Mid OBE', 'Final Quiz', 'Final Marks', 'Final OBE'], 
                        'vals': co_vals
                    }
            except: pass
            
        self.co_spider_combo['values'] = names_list
        if names_list:
            self.co_spider_combo.current(0)
            
        try:
            for i, tab in enumerate(self.co_nb.tabs()):
                if "Internal DB Records" in self.co_nb.tab(tab, "text"):
                    self.co_nb.select(i)
                    break
        except: pass

    def load_co_data(self):
        file_paths = filedialog.askopenfilenames(
            title="Select CO Analysis Excel File(s) (You can select multiple)",
            filetypes=[("Excel Files", "*.xlsx *.xls")]
        )
        if not file_paths: return

        try:
            for frame in self.all_co_tab_frames.values():
                frame.destroy()
            self.all_co_tab_frames.clear()
            self.co_tabs.clear()
            self.co_dfs.clear()
            self.spider_data.clear()
            
            aggregated_sheets = {}

            for file_path in file_paths:
                xl = pd.ExcelFile(file_path)
                
                for sheet_name in xl.sheet_names:
                    df = xl.parse(sheet_name, header=None)
                    df.fillna("", inplace=True)

                    header_idx = 0
                    for idx, row in df.iterrows():
                        row_str = ' '.join(str(v).lower() for v in row.values)
                        if 'student id' in row_str or 'sl #' in row_str or 'co1' in row_str.split():
                            header_idx = idx
                            break
                            
                    if sheet_name not in aggregated_sheets:
                        col_names = []
                        for c_idx, val in enumerate(df.iloc[header_idx]):
                            v_str = str(val).strip()
                            if v_str.lower() in ["", "nan", "none"]:
                                v_str = f"Detail_{c_idx}"
                            
                            original_v_str = v_str
                            count = 1
                            while v_str in col_names:
                                v_str = f"{original_v_str} ({count})"
                                count += 1
                            col_names.append(v_str)
                            
                        aggregated_sheets[sheet_name] = {'cols': col_names, 'rows': [col_names]}
                        
                    for idx, row in df.iloc[header_idx+1:].iterrows():
                        if row.replace("", pd.NA).dropna().empty: continue 
                        aggregated_sheets[sheet_name]['rows'].append(list(row))
            
            for sheet_name, data in aggregated_sheets.items():
                col_names = data['cols']
                rows = data['rows']
                
                df_reconstructed = pd.DataFrame(rows)
                self.co_dfs[sheet_name] = df_reconstructed
                
                frame = tk.Frame(self.co_nb, bg="white")
                self.all_co_tab_frames[sheet_name] = frame

                tv = ttk.Treeview(frame, show="headings", style="CO.Treeview")
                
                def make_yview(tree):
                    def _yview(*args):
                        if args and args[0] == 'scroll' and args[2] == 'units':
                            tree.yview('scroll', int(args[1]) * 4, 'units')
                        else:
                            tree.yview(*args)
                    return _yview

                def make_xview(tree):
                    def _xview(*args):
                        if args and args[0] == 'scroll' and args[2] == 'units':
                            tree.xview('scroll', int(args[1]) * 10, 'units') 
                        else:
                            tree.xview(*args)
                    return _xview

                vsb = ttk.Scrollbar(frame, orient="vertical", command=make_yview(tv))
                hsb = ttk.Scrollbar(frame, orient="horizontal", command=make_xview(tv))
                tv.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)
                
                def on_mousewheel_v(event, tree=tv):
                    delta = event.delta
                    num = getattr(event, 'num', 0)
                    if num == 5 or delta < 0: tree.yview_scroll(4, "units")
                    elif num == 4 or delta > 0: tree.yview_scroll(-4, "units")
                    return "break"
                    
                def on_mousewheel_h(event, tree=tv):
                    delta = event.delta
                    num = getattr(event, 'num', 0)
                    if num == 5 or delta < 0: tree.xview_scroll(10, "units")
                    elif num == 4 or delta > 0: tree.xview_scroll(-10, "units")
                    return "break"

                tv.bind("<MouseWheel>", on_mousewheel_v)
                tv.bind("<Shift-MouseWheel>", on_mousewheel_h)
                tv.bind("<Button-4>", on_mousewheel_v)
                tv.bind("<Button-5>", on_mousewheel_v)
                tv.bind("<Shift-Button-4>", on_mousewheel_h)
                tv.bind("<Shift-Button-5>", on_mousewheel_h)
                
                tv.tag_configure('evenrow', background='#f3e5f5')
                tv.tag_configure('oddrow', background='#ffffff')

                vsb.pack(side=tk.RIGHT, fill=tk.Y)
                hsb.pack(side=tk.BOTTOM, fill=tk.X)
                tv.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

                self.co_tabs[sheet_name] = tv
                
                tv["columns"] = col_names
                for c_idx, col in enumerate(col_names):
                    tv.heading(col, text=col)
                    calc_w = len(str(col)) * 9 + 30
                    width = max(160 if "name" in str(col).lower() else 100, calc_w)
                    tv.column(col, width=width, anchor="center", minwidth=80)
                    
                for idx, row in enumerate(rows[1:]):
                    tag = 'evenrow' if idx % 2 == 0 else 'oddrow'
                    tv.insert("", "end", values=list(row), tags=(tag,))

            attainment_sheet = next((s for s in aggregated_sheets.keys() if "attainment" in s.lower()), None)
            
            if attainment_sheet:
                df_att = self.co_dfs[attainment_sheet]
                names_list = []
                
                att_header_idx = 0
                for idx, row in df_att.iterrows():
                    row_str = ' '.join(str(v).lower() for v in row.values)
                    if 'student id' in row_str or 'sl #' in row_str or 'co1' in row_str.split():
                        att_header_idx = idx
                        break
                        
                target_cos = ['CO1', 'CO2', 'CO3', 'CO4', 'CO5', 'CO6']
                co_col_map = []
                for c in target_cos:
                    last_idx = -1
                    for c_idx, val in enumerate(df_att.iloc[att_header_idx]):
                        if str(val).strip().upper() == c:
                            last_idx = c_idx
                    if last_idx != -1:
                        co_col_map.append((c, last_idx))
                
                for idx in range(att_header_idx + 1, len(df_att)):
                    try:
                        name = str(df_att.iloc[idx, 2]).strip()
                        if name and name.lower() not in ["student name", "nan", "none", "", "0"]:
                            vals = []
                            cats = []
                            for co_label, c_idx in co_col_map:
                                cats.append(co_label)
                                try: vals.append(float(df_att.iloc[idx, c_idx]))
                                except: vals.append(0.0)
                            
                            if cats:
                                display_name = f"{name} (Row {idx})"
                                names_list.append(display_name)
                                self.spider_data[display_name] = {'cats': cats, 'vals': vals}
                    except:
                        pass
                
                self.co_spider_combo['values'] = names_list
                if names_list:
                    self.co_spider_combo.current(0)

            self.filter_co_tabs()
            
            file_count = len(file_paths)
            messagebox.showinfo("Success", f"CO Analysis Data loaded successfully from {file_count} file(s)!")

        except Exception as e:
            messagebox.showerror("Error", f"Failed to load file: {e}")

    def show_co_spider_chart(self):
        selected = self.co_spider_var.get()
        if not selected or selected not in self.spider_data:
            messagebox.showinfo("Info", "Please load data and select a valid student first.")
            return

        if not ANALYTICS_INSTALLED:
            messagebox.showerror("Error", "Analytics modules (matplotlib) not installed.")
            return

        student_info = self.spider_data[selected]
        vals = list(student_info['vals'])
        cats = list(student_info['cats'])

        chart_win = tk.Toplevel(self)
        chart_win.title(f"Spider Chart - {selected}")
        chart_win.geometry("600x650")

        N = len(cats)
        if N == 0:
            tk.Label(chart_win, text="No CO data available to chart.", font=("Arial", 12)).pack(pady=50)
            return

        angles = [n / float(N) * 2 * np.pi for n in range(N)]
        vals = vals + vals[:1]
        angles = angles + angles[:1]

        plt.close('all')
        fig, ax = plt.subplots(figsize=(6, 6), subplot_kw=dict(polar=True))

        ax.plot(angles, vals, linewidth=2, linestyle='solid', color='#9C27B0', marker='o')
        ax.fill(angles, vals, '#9C27B0', alpha=0.25)

        ax.set_xticks(angles[:-1])
        ax.set_xticklabels(cats, fontsize=16, fontweight='bold')

        max_val = max(vals) if vals else 4.0
        if max_val <= 4.0:
            ax.set_ylim(0, 4)
            ax.set_yticks([1, 2, 3, 4])
            ax.set_yticklabels(['1', '2', '3', '4'], color="grey", size=14, fontweight='bold')
        else:
            ax.set_ylim(0, max_val * 1.1)
            ax.tick_params(axis='y', labelsize=14)

        ax.set_title(f"CO Attainment Profile\n{selected}", pad=20, fontsize=18, fontweight='bold')

        canvas = FigureCanvasTkAgg(fig, master=chart_win)
        canvas.draw()
        canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)

        btn_frame = tk.Frame(chart_win, bg="#f5f5f5")
        btn_frame.pack(fill=tk.X, pady=10)
        
        def save_graph():
            path = filedialog.asksaveasfilename(defaultextension=".png", filetypes=[("PNG Image", "*.png"), ("All Files", "*.*")], title="Save Graph")
            if path:
                fig.savefig(path, bbox_inches='tight')
                messagebox.showinfo("Saved", f"Graph successfully saved to:\n{path}")
                
        tk.Button(btn_frame, text="💾 Save Graph", command=save_graph, bg="#4CAF50", fg="white", font=("Arial", 11, "bold")).pack()

    def show_overall_spider_chart(self):
        if not self.spider_data:
            messagebox.showinfo("Info", "Please load CO Analysis Data first.")
            return

        if not ANALYTICS_INSTALLED:
            messagebox.showerror("Error", "Analytics modules (matplotlib) not installed.")
            return

        cat_sums = {}
        cat_counts = {}

        for student, data in self.spider_data.items():
            cats = data['cats']
            vals = data['vals']
            for c, v in zip(cats, vals):
                cat_sums[c] = cat_sums.get(c, 0.0) + v
                cat_counts[c] = cat_counts.get(c, 0) + 1

        if not cat_sums:
            messagebox.showinfo("Info", "No valid CO data found to calculate overall section average.")
            return

        all_cats = list(cat_sums.keys())
        avg_vals = [cat_sums[c] / cat_counts[c] for c in all_cats]

        chart_win = tk.Toplevel(self)
        chart_win.title("Spider Chart - Overall Section Average")
        chart_win.geometry("600x650")

        N = len(all_cats)
        angles = [n / float(N) * 2 * np.pi for n in range(N)]
        avg_vals = avg_vals + avg_vals[:1]
        angles = angles + angles[:1]

        plt.close('all')
        fig, ax = plt.subplots(figsize=(6, 6), subplot_kw=dict(polar=True))

        ax.plot(angles, avg_vals, linewidth=2, linestyle='solid', color='#FF5722', marker='o')
        ax.fill(angles, avg_vals, '#FF5722', alpha=0.25)

        ax.set_xticks(angles[:-1])
        ax.set_xticklabels(all_cats, fontsize=16, fontweight='bold')

        max_val = max(avg_vals) if avg_vals else 4.0
        if max_val <= 4.0:
            ax.set_ylim(0, 4)
            ax.set_yticks([1, 2, 3, 4])
            ax.set_yticklabels(['1', '2', '3', '4'], color="grey", size=14, fontweight='bold')
        else:
            ax.set_ylim(0, max_val * 1.1)
            ax.tick_params(axis='y', labelsize=14)

        ax.set_title(f"Overall Section Average\nCO Attainment Profile", pad=20, fontsize=18, fontweight='bold')

        canvas = FigureCanvasTkAgg(fig, master=chart_win)
        canvas.draw()
        canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)

        btn_frame = tk.Frame(chart_win, bg="#f5f5f5")
        btn_frame.pack(fill=tk.X, pady=10)
        
        def save_graph():
            path = filedialog.asksaveasfilename(defaultextension=".png", filetypes=[("PNG Image", "*.png"), ("All Files", "*.*")], title="Save Graph")
            if path:
                fig.savefig(path, bbox_inches='tight')
                messagebox.showinfo("Saved", f"Graph successfully saved to:\n{path}")
                
        tk.Button(btn_frame, text="💾 Save Graph", command=save_graph, bg="#4CAF50", fg="white", font=("Arial", 11, "bold")).pack()

    def show_co_summary_graphs(self):
        if not self.spider_data:
            messagebox.showinfo("Info", "Please load CO Analysis Data first.")
            return

        if not ANALYTICS_INSTALLED:
            messagebox.showerror("Error", "Analytics modules (matplotlib) not installed.")
            return

        try:
            benchmark_pct = float(self.co_benchmark_var.get())
        except ValueError:
            benchmark_pct = 60.0

        co_scores = {} 

        for student, data in self.spider_data.items():
            cats = data['cats']
            vals = data['vals']
            for c, v in zip(cats, vals):
                if c not in co_scores:
                    co_scores[c] = []
                co_scores[c].append(v)

        if not co_scores:
            return
            
        all_cats = list(co_scores.keys())

        co_passing_pct = []
        co_averages = []
        
        max_possible = max([max(scores) if scores else 0 for scores in co_scores.values()] + [4.0])
        SCORE_THRESHOLD = 2.4 if max_possible <= 4.0 else (max_possible * 0.6) 

        for c in all_cats:
            scores = co_scores[c]
            total = len(scores)
            if total == 0:
                co_passing_pct.append(0)
                co_averages.append(0)
                continue
                
            passed = sum(1 for s in scores if s >= SCORE_THRESHOLD)
            co_passing_pct.append((passed / total) * 100)
            co_averages.append(sum(scores) / total)

        dash = tk.Toplevel(self)
        dash.title("CO Summary Dashboards")
        dash.geometry("1100x600")
        dash.configure(bg="#f5f5f5")

        fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(11, 5))
        fig.patch.set_facecolor('#f5f5f5')

        bars1 = ax1.bar(all_cats, co_passing_pct, color='#2196F3')
        ax1.axhline(y=benchmark_pct, color='r', linestyle='--', linewidth=2, label=f'Benchmark ({benchmark_pct}%)')
        ax1.set_ylim(0, 115)
        ax1.set_ylabel('% of Students', fontsize=14, fontweight='bold')
        ax1.set_title(f'Percentage of Students Achieving >= {SCORE_THRESHOLD:.1f} per CO', pad=15, fontsize=16, fontweight='bold')
        ax1.tick_params(axis='both', labelsize=14)
        ax1.legend(fontsize=12)
        
        for bar in bars1:
            yval = bar.get_height()
            ax1.text(bar.get_x() + bar.get_width()/2, yval + 2, f'{yval:.1f}%', ha='center', va='bottom', fontsize=14, fontweight='bold')

        bars2 = ax2.bar(all_cats, co_averages, color='#4CAF50')
        ax2.axhline(y=SCORE_THRESHOLD, color='r', linestyle='--', linewidth=2, label=f'Target Avg ({SCORE_THRESHOLD:.1f})')
        
        if max_possible <= 4.0:
            ax2.set_ylim(0, 4.5)
            ax2.set_ylabel('Average Score (Out of 4.0)', fontsize=14, fontweight='bold')
        else:
            ax2.set_ylim(0, max_possible * 1.1)
            ax2.set_ylabel(f'Average Score (Out of {max_possible:.0f})', fontsize=14, fontweight='bold')
            
        ax2.set_title('Class Average Score per CO', pad=15, fontsize=16, fontweight='bold')
        ax2.tick_params(axis='both', labelsize=14)
        ax2.legend(fontsize=12)
        
        for bar in bars2:
            yval = bar.get_height()
            ax2.text(bar.get_x() + bar.get_width()/2, yval + 0.1, f'{yval:.2f}', ha='center', va='bottom', fontsize=14, fontweight='bold')

        fig.tight_layout(pad=3.0)
        canvas = FigureCanvasTkAgg(fig, master=dash)
        canvas.draw()
        canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True, padx=20, pady=20)
        
        btn_frame = tk.Frame(dash, bg="#f5f5f5")
        btn_frame.pack(fill=tk.X, pady=(0, 20))
        
        def save_summary_graph():
            path = filedialog.asksaveasfilename(defaultextension=".png", filetypes=[("PNG Image", "*.png"), ("All Files", "*.*")], title="Save Summary Dashboard")
            if path:
                fig.savefig(path, bbox_inches='tight')
                messagebox.showinfo("Saved", f"Dashboard successfully saved to:\n{path}")
                
        tk.Button(btn_frame, text="💾 Save Dashboard", command=save_summary_graph, bg="#4CAF50", fg="white", font=("Arial", 11, "bold")).pack()


    # ==========================================
    # TAB 9: BLOOD BANK / BLOOD GROUPS
    # ==========================================
    def setup_blood_group_tab(self):
        container = tk.Frame(self.tab_blood_group, bg="#f5f5f5")
        container.pack(fill=tk.BOTH, expand=True)

        top_frame = tk.Frame(container, bg="#f5f5f5")
        top_frame.pack(fill=tk.X, padx=10, pady=10)
        
        tk.Label(top_frame, text="Select Course:", bg="#f5f5f5", font=("Arial", 11, "bold")).pack(side=tk.LEFT)
        self.bg_course_var = tk.StringVar()
        self.bg_course_combo = ttk.Combobox(top_frame, textvariable=self.bg_course_var, state="readonly", width=35)
        self.bg_course_combo.pack(side=tk.LEFT, padx=10)
        self.bg_course_combo.bind("<<ComboboxSelected>>", lambda e: self.refresh_blood_group_data())
        
        tk.Label(top_frame, text="Blood Group:", bg="#f5f5f5", font=("Arial", 11, "bold")).pack(side=tk.LEFT, padx=(20,0))
        self.bg_filter_var = tk.StringVar()
        self.bg_filter_combo = ttk.Combobox(top_frame, textvariable=self.bg_filter_var, state="readonly", width=12, values=['All', 'A+', 'A-', 'B+', 'B-', 'AB+', 'AB-', 'O+', 'O-', 'Unknown'])
        self.bg_filter_combo.current(0)
        self.bg_filter_combo.pack(side=tk.LEFT, padx=5)
        self.bg_filter_combo.bind("<<ComboboxSelected>>", lambda e: self.refresh_blood_group_data())

        self.refresh_bg_course_dropdown()

        content_frame = tk.Frame(container, bg="#f5f5f5")
        content_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        
        table_frame = tk.Frame(content_frame, bg="#f5f5f5")
        table_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        
        cols = ("Name", "Student ID", "Blood Grp", "Course", "Phone")
        self.bg_tree = ttk.Treeview(table_frame, columns=cols, show='headings', height=15)
        for c in cols: 
            self.bg_tree.heading(c, text=c)
            width = 80 if c == "Blood Grp" else (150 if c == "Name" or c == "Course" else 100)
            self.bg_tree.column(c, anchor="center", width=width)
            
        bg_scroll = ttk.Scrollbar(table_frame, orient="vertical", command=self.bg_tree.yview)
        self.bg_tree.configure(yscrollcommand=bg_scroll.set)
        self.bg_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        bg_scroll.pack(side=tk.RIGHT, fill=tk.Y)
        
        self.bg_chart_frame = tk.Frame(content_frame, bg="white", relief=tk.SUNKEN, bd=2)
        self.bg_chart_frame.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True, padx=(10,0))
        
        self.refresh_blood_group_data()

    def refresh_bg_course_dropdown(self):
        course_options = ["All Courses"]
        for c_key, data in self.courses.items():
            label = f"{data['c_name']} | ID:{data['c_id']} | Sec:{data['c_sec']} | {data['c_days']}"
            course_options.append(label)
        self.bg_course_combo['values'] = course_options
        if not self.bg_course_var.get(): 
            self.bg_course_combo.current(0)
            
    def refresh_blood_group_data(self):
        if not hasattr(self, 'bg_tree'): return
        for item in self.bg_tree.get_children(): self.bg_tree.delete(item)
        
        course_filter = self.bg_course_var.get()
        bg_filter = self.bg_filter_var.get()
        
        bg_counts = {'A+':0, 'A-':0, 'B+':0, 'B-':0, 'AB+':0, 'AB-':0, 'O+':0, 'O-':0, 'Unknown':0}
        
        for cid, data in self.students.items():
            c = data.get('course', '')
            bg = data.get('blood_group', 'Unknown')
            if not bg: bg = 'Unknown'
            
            if course_filter and course_filter != "All Courses":
                if c != course_filter: continue
                
            if bg in bg_counts: bg_counts[bg] += 1
            else: bg_counts['Unknown'] += 1
            
            if bg_filter and bg_filter != "All":
                if bg != bg_filter: continue
                
            self.bg_tree.insert("", "end", values=(data.get('name',''), data.get('student_id',''), bg, c, data.get('phone','')))
            
        self.plot_blood_group_pie(bg_counts, course_filter)
        
    def plot_blood_group_pie(self, bg_counts, course_filter):
        if not hasattr(self, 'bg_chart_frame'): return
        for widget in self.bg_chart_frame.winfo_children(): widget.destroy()
        
        if not ANALYTICS_INSTALLED:
            tk.Label(self.bg_chart_frame, text="Analytics modules missing.\nRun: pip install matplotlib", fg="red").pack(pady=50)
            return

        labels = []
        sizes = []
        
        color_map = {'A+': '#ff9999', 'A-': '#ffb3e6', 'B+': '#c2c2f0', 'B-': '#99ff99', 
                     'AB+': '#ffcc99', 'AB-': '#c4e17f', 'O+': '#ff6666', 'O-': '#66b3ff', 'Unknown': '#d9d9d9'}
        colors = []
        
        for bg, count in bg_counts.items():
            if count > 0:
                labels.append(f"{bg} ({count})")
                sizes.append(count)
                colors.append(color_map.get(bg, '#d9d9d9'))
                
        plt.close('all')
        fig, ax = plt.subplots(figsize=(5,5))
        
        if not sizes:
            ax.text(0.5, 0.5, "No Data Available", ha='center', va='center', fontsize=16, fontweight='bold')
            ax.axis('off')
        else:
            ax.pie(sizes, labels=labels, autopct='%1.1f%%', startangle=140, colors=colors, textprops={'fontsize': 14, 'weight': 'bold'})
            ax.axis('equal')
            title_text = "Overall Blood Group Distribution" if not course_filter or course_filter == "All Courses" else "Blood Groups for Selected Course"
            ax.set_title(title_text, pad=20, fontsize=16, fontweight='bold')
            
        canvas = FigureCanvasTkAgg(fig, master=self.bg_chart_frame)
        canvas.draw()
        canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)

def launch_app():
    root = tk.Tk()
    
    def show_login_screen():
        for widget in root.winfo_children():
            widget.destroy()
        FacultyAuth(root, show_main_app)
        
    def show_main_app(root_window, faculty_data):
        for widget in root.winfo_children():
            widget.destroy()
            
        loading_frame = tk.Frame(root_window, bg="#f0f2f5")
        loading_frame.pack(fill="both", expand=True)
        tk.Label(loading_frame, text="Initializing Smart Environment...", font=("Helvetica", 16, "bold"), bg="#f0f2f5", fg="#1a73e8").place(relx=0.5, rely=0.45, anchor="center")
        tk.Label(loading_frame, text="Loading AI modules and databases. Please wait a moment.", font=("Arial", 10), bg="#f0f2f5", fg="#555").place(relx=0.5, rely=0.52, anchor="center")
        root_window.update()
        
        load_heavy_libraries()
        
        loading_frame.destroy()
        AttendanceSystem(root_window, faculty_data, logout_cb=show_login_screen)

    show_login_screen()
    root.mainloop()

if __name__ == "__main__":
    launch_app()