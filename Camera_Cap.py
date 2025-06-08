import cv2
import numpy as np
import mss
import sys
import time
import psutil
import platform
import uuid

from PySide6.QtWidgets import (
    QApplication, QWidget, QVBoxLayout, QHBoxLayout, QLabel, QPushButton,
    QComboBox, QMainWindow, QSizePolicy, QListWidget, QDialog, QDialogButtonBox,
    QListWidgetItem, QMessageBox
)
from PySide6.QtCore import Qt, QTimer, Signal, QPoint, QRectF
from PySide6.QtGui import QImage, QPixmap, QMouseEvent, QWheelEvent, QCursor

if platform.system() == "Windows":
    try:
        import win32gui
        import win32process
        import win32con
        HAS_WIN32 = True
    except ImportError:
        print("Ostrzeżenie: Moduł pywin32 nie jest zainstalowany. Funkcje wykrywania okien mogą działać nieprawidłowo.")
        print("Zainstaluj: pip install pywin32")
        HAS_WIN32 = False
else:
    HAS_WIN32 = False
    print("Ostrzeżenie: Ten system operacyjny nie jest Windows. Niektóre funkcje mogą działać nieprawidłowo lub nie być dostępne.")

PREVIEW_WINDOW_NAME = "Podgląd Kamery + Obszar Ekranu"
DEFAULT_CAM_WIDTH = 1280
DEFAULT_CAM_HEIGHT = 720
INITIAL_PREVIEW_WINDOW_WIDTH = 1280
INITIAL_PREVIEW_WINDOW_HEIGHT = 720
MIN_LAYER_SIZE = 10
MAX_LAYER_SIZE = 4000
RESIZE_HANDLE_SIZE = 10
MOVE_STEP = 5
SOURCE_TYPE_CAMERA = "Camera"
SOURCE_TYPE_SCREEN_REGION = "Screen Region"

class ImageState:
    def __init__(self, name, source_type, initial_width, initial_height, initial_x, initial_y,
                 is_on_top=False, is_visible=True, camera_index=None, screen_region=None):
        self.id = str(uuid.uuid4())
        self.name = name
        self.source_type = source_type
        self.original_image = None
        self.display_width = max(MIN_LAYER_SIZE, initial_width)
        self.display_height = max(MIN_LAYER_SIZE, initial_height)
        self.x = initial_x
        self.y = initial_y
        self.is_dragging = False
        self.is_on_top = is_on_top
        self.is_visible = is_visible
        self.drag_offset_x = 0
        self.drag_offset_y = 0
        self.aspect_ratio = initial_width / initial_height if initial_height > 0 else 1.0
        self.camera_index = camera_index
        self.screen_region = screen_region
        self.selected_app_window_info = None

def list_cameras():
    available_cameras = []
    for i in range(5):
        cap = cv2.VideoCapture(i, cv2.CAP_DSHOW)
        if cap.isOpened():
            available_cameras.append(i)
            cap.release()
    return available_cameras

ALL_WINDOWS_INFO = {}

def enum_windows_callback(hwnd, lParam):
    if not win32gui.IsWindowVisible(hwnd):
        return True
    if win32gui.IsIconic(hwnd):
        return True
    title = win32gui.GetWindowText(hwnd)
    thread_id, process_id = win32process.GetWindowThreadProcessId(hwnd)
    rect = win32gui.GetWindowRect(hwnd)
    width = rect[2] - rect[0]
    height = rect[3] - rect[1]
    ignored_window_titles_starts_with = [
        PREVIEW_WINDOW_NAME,
        "Zaznacz obszar do przechwycenia w:",
        "python.exe",
        "py.exe",
        "dwm.exe",
        "NVIDIA GeForce Overlay",
        "Program Manager",
        "Default IME",
        "MSCTFIME UI",
        "IME",
        "Pasek zadań"
    ]
    ignored_window_titles_contains = [
        "Windows Defender Notification"
    ]
    if any(title.strip().startswith(s) for s in ignored_window_titles_starts_with) or \
       any(s in title for s in ignored_window_titles_contains):
        return True
    if width < 50 or height < 50:
        return True
    global ALL_WINDOWS_INFO
    ALL_WINDOWS_INFO[hwnd] = {
        'hwnd': hwnd,
        'title': title,
        'rect': rect,
        'pid': process_id,
        'width': width,
        'height': height,
        'left': rect[0],
        'top': rect[1]
    }
    return True

def get_processes_with_windows_pywin32():
    if not HAS_WIN32:
        return []
    global ALL_WINDOWS_INFO
    ALL_WINDOWS_INFO = {}
    win32gui.EnumWindows(enum_windows_callback, None)
    process_pid_to_name = {}
    for proc in psutil.process_iter(['pid', 'name']):
        process_pid_to_name[proc.info['pid']] = proc.info['name']
    process_map = {}
    for hwnd, win_info in ALL_WINDOWS_INFO.items():
        pid = win_info['pid']
        process_name = process_pid_to_name.get(pid, f"PID_{pid}_UNKNOWN")
        if process_name not in process_map:
            process_map[process_name] = {'pids': set(), 'windows': []}
        process_map[process_name]['pids'].add(pid)
        process_map[process_name]['windows'].append(win_info)
    unique_processes_with_windows = []
    for name, data in process_map.items():
        unique_processes_with_windows.append({
            "name": name,
            "pids": sorted(list(data['pids'])),
            "windows": data['windows']
        })
    unique_processes_with_windows.sort(key=lambda x: x['name'].lower())
    return unique_processes_with_windows

class CameraScreenOverlayApp(QMainWindow):
    update_image_signal = Signal(np.ndarray)

    def __init__(self):
        super().__init__()
        self.setWindowTitle(PREVIEW_WINDOW_NAME)
        self.setGeometry(100, 100, INITIAL_PREVIEW_WINDOW_WIDTH, INITIAL_PREVIEW_WINDOW_HEIGHT)
        self.cap = None
        self.screen_capture_instance = mss.mss()
        self.image_states = []
        self.active_camera_layer_id = None
        self.active_draggable_image_state = None
        self.active_resizable_image_state = None
        self.resize_handle_active = None
        self.last_mouse_x = -1
        self.last_mouse_y = -1
        self.is_roi_selection_active = False
        self.selected_app_window_info_for_new_layer = None
        self.init_ui()
        self.init_camera_layer()
        self.timer = QTimer(self)
        self.timer.timeout.connect(self.update_frame)
        self.timer.start(30)
        print("\n--- INSTRUKCJE UŻYTKOWANIA ---")
        print("1. Wybierz kamerę z listy 'Wybierz kamerę'.")
        print("2. Aby dodać warstwę z aplikacji:")
        print("   - Wybierz 'Wybierz aplikację'.")
        print("   - Jeśli aplikacja ma wiele okien, wybierz konkretne okno z 'Wybierz okno'.")
        print("   - Kliknij 'Dodaj warstwę z ROI', a następnie w nowym oknie zaznacz obszar myszką i zatwierdź ENTER.")
        print("   - Nowa warstwa zostanie dodana do listy 'Zarządzaj warstwami'.")
        print("3. Użyj listy 'Zarządzaj warstwami' i przycisków obok, aby kontrolować warstwy:")
        print("   - 'Włącz/Wyłącz': Przełącza widoczność wybranej warstwy.")
        print("   - 'Na wierzch': Przenosi wybraną warstwę na górę kolejności rysowania.")
        print("   - 'Na spód': Przenosi wybraną warstwę na dół kolejności rysowania.")
        print("   - 'Przesuń w górę': Przesuwa wybraną warstwę o jedną pozycję w górę.")
        print("   - 'Przesuń w dół': Przesuwa wybraną warstwę o jedną pozycję w dół.")
        print("   - 'Usuń warstwę': Usuwa wybraną warstwę.")
        print("4. W oknie podglądu możesz interaktywnie zmieniać warstwy (jeśli są widoczne):")
        print("   - Kliknij i przeciągnij warstwę, aby ją przesuwać.")
        print("   - Użyj kółka myszy nad warstwą, aby ją skalować (zoom).")
        print("   - Przeciągnij krawędzie lub rogi warstwy, aby zmienić jej rozmiar (zachowując proporcje).")
        print("   - Zaznacz warstwę w comboboxie 'Zarządzaj warstwami', a następnie użyj klawiszy strzałek (↑↓←→), aby precyzyjnie przesuwać wybraną warstwę.")

    def init_ui(self):
        self.central_widget = QWidget()
        self.setCentralWidget(self.central_widget)
        self.main_layout = QVBoxLayout(self.central_widget)
        self.control_panel = QWidget()
        self.control_layout = QHBoxLayout(self.control_panel)
        self.main_layout.addWidget(self.control_panel)
        self.camera_label = QLabel("Wybierz kamerę:")
        self.camera_combobox = QComboBox()
        self.camera_combobox.currentIndexChanged.connect(self.select_camera_source)
        self.control_layout.addWidget(self.camera_label)
        self.control_layout.addWidget(self.camera_combobox)
        self.app_label = QLabel("Wybierz aplikację:")
        self.app_combobox = QComboBox()
        self.app_combobox.currentIndexChanged.connect(self.select_application_for_roi)
        self.control_layout.addWidget(self.app_label)
        self.control_layout.addWidget(self.app_combobox)
        self.window_label = QLabel("Wybierz okno:")
        self.window_combobox = QComboBox()
        self.window_combobox.currentIndexChanged.connect(self.select_window_for_roi)
        self.window_combobox.setEnabled(False)
        self.control_layout.addWidget(self.window_label)
        self.control_layout.addWidget(self.window_combobox)
        self.add_roi_layer_button = QPushButton("Dodaj warstwę z ROI")
        self.add_roi_layer_button.clicked.connect(self.start_roi_selection_for_new_layer)
        self.control_layout.addWidget(self.add_roi_layer_button)
        self.control_layout.addStretch(1)
        self.layer_management_panel = QWidget()
        self.layer_management_layout = QHBoxLayout(self.layer_management_panel)
        self.main_layout.addWidget(self.layer_management_panel)
        self.layers_label = QLabel("Zarządzaj warstwami:")
        self.layers_combobox = QComboBox()
        self.layers_combobox.currentIndexChanged.connect(self.on_layer_selection_changed)
        self.layer_management_layout.addWidget(self.layers_label)
        self.layer_management_layout.addWidget(self.layers_combobox)
        self.toggle_visibility_button = QPushButton("Włącz/Wyłącz")
        self.toggle_visibility_button.clicked.connect(self.toggle_selected_layer_visibility)
        self.layer_management_layout.addWidget(self.toggle_visibility_button)
        self.move_up_button = QPushButton("Przesuń w górę")
        self.move_up_button.clicked.connect(self.move_selected_layer_up)
        self.layer_management_layout.addWidget(self.move_up_button)
        self.move_down_button = QPushButton("Przesuń w dół")
        self.move_down_button.clicked.connect(self.move_selected_layer_down)
        self.layer_management_layout.addWidget(self.move_down_button)
        self.move_to_front_button = QPushButton("Na wierzch")
        self.move_to_front_button.clicked.connect(self.move_selected_layer_to_front)
        self.layer_management_layout.addWidget(self.move_to_front_button)
        self.move_to_back_button = QPushButton("Na spód")
        self.move_to_back_button.clicked.connect(self.move_selected_layer_to_back)
        self.layer_management_layout.addWidget(self.move_to_back_button)
        self.remove_layer_button = QPushButton("Usuń warstwę")
        self.remove_layer_button.clicked.connect(self.remove_selected_layer)
        self.layer_management_layout.addWidget(self.remove_layer_button)
        self.layer_management_layout.addStretch(1)
        self.video_label = QLabel(self)
        self.video_label.setAlignment(Qt.AlignCenter)
        self.video_label.setStyleSheet("background-color: black;")
        self.video_label.setSizePolicy(QSizePolicy.Expanding, QSizePolicy.Expanding)
        self.main_layout.addWidget(self.video_label)
        self.video_label.setMouseTracking(True)
        self.video_label.mousePressEvent = self.preview_mouse_press_event
        self.video_label.mouseReleaseEvent = self.preview_mouse_release_event
        self.video_label.mouseMoveEvent = self.preview_mouse_move_event
        self.video_label.wheelEvent = self.preview_mouse_wheel_event
        self.update_image_signal.connect(self.update_video_label)
        self.populate_camera_combobox()
        self.populate_app_combobox()
        self.update_layers_combobox()

    def init_camera_layer(self):
        cam_width = 200
        cam_height = 200
        cam_x = (INITIAL_PREVIEW_WINDOW_WIDTH - cam_width) // 2
        cam_y = (INITIAL_PREVIEW_WINDOW_HEIGHT - cam_height) // 2
        cam_state = ImageState("Kamera", SOURCE_TYPE_CAMERA,
                               cam_width, cam_height,
                               cam_x, cam_y, is_visible=True)
        self.add_layer(cam_state)
        self.active_camera_layer_id = cam_state.id
        print("Domyślna warstwa 'Kamera' została dodana do listy warstw. Użytkownik musi ją wybrać, aby ją uruchomić.")

    def add_layer(self, layer_state):
        self.image_states.append(layer_state)
        self.update_layers_combobox()
        index = self.layers_combobox.findData(layer_state.id)
        if index != -1:
            self.layers_combobox.setCurrentIndex(index)

    def remove_layer(self, layer_id):
        layer_to_remove = self.get_layer_by_id(layer_id)
        if layer_to_remove:
            self.image_states.remove(layer_to_remove)
            if layer_id == self.active_camera_layer_id:
                self.active_camera_layer_id = None
                if self.cap and self.cap.isOpened():
                    self.cap.release()
                    self.cap = None
                self.camera_combobox.setCurrentIndex(
                    self.camera_combobox.findData(None)
                )
            self.update_layers_combobox()

    def get_layer_by_id(self, layer_id):
        for state in self.image_states:
            if state.id == layer_id:
                return state
        return None

    def update_layers_combobox(self):
        current_selected_id = self.layers_combobox.currentData()
        self.layers_combobox.clear()
        for layer_state in reversed(self.image_states):
            visibility_prefix = "✅" if layer_state.is_visible else "❌"
            self.layers_combobox.addItem(f"{visibility_prefix} {layer_state.name}", userData=layer_state.id)
        has_layers = bool(self.image_states)
        self.layers_combobox.setEnabled(has_layers)
        self.toggle_visibility_button.setEnabled(has_layers)
        self.move_up_button.setEnabled(has_layers)
        self.move_down_button.setEnabled(has_layers)
        self.move_to_front_button.setEnabled(has_layers)
        self.move_to_back_button.setEnabled(has_layers)
        self.remove_layer_button.setEnabled(has_layers)
        if not has_layers:
            self.layers_combobox.addItem("Brak warstw")
            return
        if current_selected_id:
            index = self.layers_combobox.findData(current_selected_id)
            if index != -1:
                self.layers_combobox.setCurrentIndex(index)
            else:
                self.layers_combobox.setCurrentIndex(0)
        elif self.layers_combobox.count() > 0:
            self.layers_combobox.setCurrentIndex(0)
        self.on_layer_selection_changed(self.layers_combobox.currentIndex())

    def on_layer_selection_changed(self, index):
        selected_layer_id = self.layers_combobox.currentData()
        if selected_layer_id:
            selected_layer_index_in_list = -1
            for i, layer in enumerate(self.image_states):
                if layer.id == selected_layer_id:
                    selected_layer_index_in_list = i
                    break
            if selected_layer_index_in_list != -1:
                self.move_to_front_button.setEnabled(selected_layer_index_in_list < len(self.image_states) - 1)
                self.move_to_back_button.setEnabled(selected_layer_index_in_list > 0)
                self.move_up_button.setEnabled(selected_layer_index_in_list < len(self.image_states) - 1)
                self.move_down_button.setEnabled(selected_layer_index_in_list > 0)
            else:
                self.move_to_front_button.setEnabled(False)
                self.move_to_back_button.setEnabled(False)
                self.move_up_button.setEnabled(False)
                self.move_down_button.setEnabled(False)
        else:
            self.move_to_front_button.setEnabled(False)
            self.move_to_back_button.setEnabled(False)
            self.move_up_button.setEnabled(False)
            self.move_down_button.setEnabled(False)

    def toggle_selected_layer_visibility(self):
        selected_layer_id = self.layers_combobox.currentData()
        if selected_layer_id:
            layer = self.get_layer_by_id(selected_layer_id)
            if layer:
                layer.is_visible = not layer.is_visible
                print(f"Warstwa '{layer.name}' widoczność: {layer.is_visible}")
                self.update_layers_combobox()
                index = self.layers_combobox.findData(layer.id)
                if index != -1:
                    self.layers_combobox.setCurrentIndex(index)

    def move_selected_layer_up(self):
        selected_layer_id = self.layers_combobox.currentData()
        if selected_layer_id:
            layer_index = -1
            for i, layer_state in enumerate(self.image_states):
                if layer_state.id == selected_layer_id:
                    layer_index = i
                    break
            if layer_index != -1 and layer_index < len(self.image_states) - 1:
                self.image_states[layer_index], self.image_states[layer_index + 1] = \
                    self.image_states[layer_index + 1], self.image_states[layer_index]
                self.update_layers_combobox()
                index = self.layers_combobox.findData(selected_layer_id)
                if index != -1:
                    self.layers_combobox.setCurrentIndex(index)
                print(f"Warstwa '{self.get_layer_by_id(selected_layer_id).name}' przesunięta w górę.")
            else:
                QMessageBox.information(self, "Informacja", "Warstwa jest już na samym wierzchu.", QMessageBox.Ok)

    def move_selected_layer_down(self):
        selected_layer_id = self.layers_combobox.currentData()
        if selected_layer_id:
            layer_index = -1
            for i, layer_state in enumerate(self.image_states):
                if layer_state.id == selected_layer_id:
                    layer_index = i
                    break
            if layer_index != -1 and layer_index > 0:
                self.image_states[layer_index], self.image_states[layer_index - 1] = \
                    self.image_states[layer_index - 1], self.image_states[layer_index]
                self.update_layers_combobox()
                index = self.layers_combobox.findData(selected_layer_id)
                if index != -1:
                    self.layers_combobox.setCurrentIndex(index)
                print(f"Warstwa '{self.get_layer_by_id(selected_layer_id).name}' przesunięta w dół.")
            else:
                QMessageBox.information(self, "Informacja", "Warstwa jest już na samym spodzie.", QMessageBox.Ok)

    def move_selected_layer_to_front(self):
        selected_layer_id = self.layers_combobox.currentData()
        if selected_layer_id:
            layer = self.get_layer_by_id(selected_layer_id)
            if layer and layer in self.image_states:
                if not self.image_states or self.image_states[-1].id == layer.id:
                    return
                self.image_states.remove(layer)
                self.image_states.append(layer)
                self.update_layers_combobox()
                index = self.layers_combobox.findData(layer.id)
                if index != -1:
                    self.layers_combobox.setCurrentIndex(index)
                print(f"Warstwa '{layer.name}' przeniesiona na wierzch.")

    def move_selected_layer_to_back(self):
        selected_layer_id = self.layers_combobox.currentData()
        if selected_layer_id:
            layer = self.get_layer_by_id(selected_layer_id)
            if layer and layer in self.image_states:
                if not self.image_states or self.image_states[0].id == layer.id:
                    return
                self.image_states.remove(layer)
                self.image_states.insert(0, layer)
                self.update_layers_combobox()
                index = self.layers_combobox.findData(layer.id)
                if index != -1:
                    self.layers_combobox.setCurrentIndex(index)
                print(f"Warstwa '{layer.name}' przeniesiona na spód.")

    def remove_selected_layer(self):
        selected_layer_id = self.layers_combobox.currentData()
        if selected_layer_id:
            layer = self.get_layer_by_id(selected_layer_id)
            if layer:
                reply = QMessageBox.question(self, 'Usuń Warstwę',
                                             f"Czy na pewno chcesz usunąć warstwę '{layer.name}'?",
                                             QMessageBox.Yes | QMessageBox.No, QMessageBox.No)
                if reply == QMessageBox.Yes:
                    self.remove_layer(selected_layer_id)
                    print(f"Warstwa '{layer.name}' usunięta.")

    def populate_camera_combobox(self):
        self.camera_combobox.clear()
        self.available_cameras = list_cameras()
        self.camera_combobox.addItem("-- Wybierz kamerę --", userData=None)
        if not self.available_cameras:
            self.camera_combobox.setEnabled(False)
            print("Brak dostępnych kamer.")
            return
        for i in self.available_cameras:
            self.camera_combobox.addItem(f"Kamera {i}", userData=i)
        self.camera_combobox.setEnabled(True)
        self.camera_combobox.setCurrentIndex(0)

    def select_camera_source(self, index):
        camera_index = self.camera_combobox.itemData(index)
        camera_layer = self.get_layer_by_id(self.active_camera_layer_id)
        if camera_index is not None and camera_layer is None:
            cam_width = 200
            cam_height = 200
            cam_x = (self.video_label.width() - cam_width) // 2 if self.video_label.width() > 0 else (INITIAL_PREVIEW_WINDOW_WIDTH - cam_width) // 2
            cam_y = (self.video_label.height() - cam_height) // 2 if self.video_label.height() > 0 else (INITIAL_PREVIEW_WINDOW_HEIGHT - cam_height) // 2
            new_cam_state = ImageState("Kamera", SOURCE_TYPE_CAMERA,
                                       cam_width, cam_height,
                                       cam_x, cam_y, is_visible=True)
            self.add_layer(new_cam_state)
            self.active_camera_layer_id = new_cam_state.id
            camera_layer = new_cam_state
            print("Utworzono nową warstwę 'Kamera' po wyborze kamery.")
        if self.cap and self.cap.isOpened():
            self.cap.release()
            self.cap = None
            print("Poprzednia kamera zwolniona.")
        if camera_layer:
            if camera_index is None:
                camera_layer.original_image = None
                camera_layer.camera_index = None
                print("Nie wybrano kamery. Warstwa kamery jest pusta.")
                return
            self.cap = cv2.VideoCapture(camera_index, cv2.CAP_DSHOW)
            if not self.cap.isOpened():
                print(f"Błąd: Nie można otworzyć kamery o indeksie {camera_index}. Upewnij się, że nie jest używana przez inną aplikację.")
                self.cap = None
                camera_layer.original_image = None
                camera_layer.camera_index = None
                return
            self.cap.set(cv2.CAP_PROP_FRAME_WIDTH, DEFAULT_CAM_WIDTH)
            self.cap.set(cv2.CAP_PROP_FRAME_HEIGHT, DEFAULT_CAM_HEIGHT)
            ret, frame_camera = self.cap.read()
            if ret:
                actual_cam_height, actual_cam_width, _ = frame_camera.shape
                print(f"Kamera {camera_index} otwarta. Rzeczywista rozdzielczość: {actual_cam_width}x{actual_cam_height}")
                camera_layer.aspect_ratio = actual_cam_width / actual_cam_height if actual_cam_height > 0 else 1.0
                camera_layer.camera_index = camera_index
                camera_layer.original_image = cv2.flip(frame_camera, 1)
                if camera_layer.aspect_ratio > 0:
                    current_display_width = max(MIN_LAYER_SIZE, camera_layer.display_width)
                    camera_layer.display_height = int(current_display_width / camera_layer.aspect_ratio)
                    camera_layer.display_height = max(MIN_LAYER_SIZE, camera_layer.display_height)
                else:
                    camera_layer.display_height = camera_layer.display_width
                print(f"Warstwa kamery ustawiona na rozmiar: {camera_layer.display_width}x{camera_layer.display_height}")
            else:
                print(f"Błąd: Kamera {camera_index} zwróciła pustą klatkę podczas inicjalizacji. Sprawdź, czy kamera jest używana przez inną aplikację.")
                self.cap.release()
                self.cap = None
                camera_layer.original_image = None
                camera_layer.camera_index = None
        else:
            print("Nie wybrano kamery lub nie znaleziono warstwy kamery do przypisania źródła.")

    def populate_app_combobox(self):
        self.app_combobox.clear()
        self.window_combobox.clear()
        self.window_combobox.setEnabled(False)
        self.add_roi_layer_button.setEnabled(False)
        self.available_processes_with_windows = []
        if HAS_WIN32:
            self.available_processes_with_windows = get_processes_with_windows_pywin32()
        if not self.available_processes_with_windows:
            self.app_combobox.addItem("Brak dostępnych aplikacji")
            self.app_combobox.setEnabled(False)
            print("Brak dostępnych aplikacji z widocznymi oknami.")
            return
        self.app_combobox.addItem("-- Wybierz aplikację --", userData=None)
        for i, proc_info in enumerate(self.available_processes_with_windows):
            self.app_combobox.addItem(f"{proc_info['name']}", userData=proc_info)
        self.app_combobox.setEnabled(True)

    def select_application_for_roi(self, index):
        self.window_combobox.clear()
        self.window_combobox.setEnabled(False)
        self.add_roi_layer_button.setEnabled(False)
        selected_proc_info = self.app_combobox.itemData(index)
        if selected_proc_info and selected_proc_info.get('windows'):
            windows_list = selected_proc_info['windows']
            if len(windows_list) > 1:
                self.window_combobox.addItem("-- Wybierz okno --", userData=None)
                for win_info in windows_list:
                    title = win_info['title'] if win_info['title'] else f"Okno bez tytułu (ID: {win_info['hwnd']})"
                    self.window_combobox.addItem(f"{title} ({win_info['width']}x{win_info['height']})", userData=win_info)
                self.window_combobox.setEnabled(True)
                self.selected_app_window_info_for_new_layer = None
            else:
                self.selected_app_window_info_for_new_layer = windows_list[0]
                title = self.selected_app_window_info_for_new_layer['title'] if self.selected_app_window_info_for_new_layer['title'] else f"Okno bez tytułu (ID: {self.selected_app_window_info_for_new_layer['hwnd']})"
                self.window_combobox.addItem(f"{title} (Automatycznie wybrano)", userData=self.selected_app_window_info_for_new_layer)
                self.window_combobox.setEnabled(False)
                self.add_roi_layer_button.setEnabled(True)
                print(f"Wybrano jedyne okno dla procesu: '{self.selected_app_window_info_for_new_layer['title']}'")
        else:
            self.selected_app_window_info_for_new_layer = None
            print("Brak okien dla wybranej aplikacji lub nie wybrano aplikacji.")

    def select_window_for_roi(self, index):
        self.selected_app_window_info_for_new_layer = self.window_combobox.itemData(index)
        if self.selected_app_window_info_for_new_layer:
            self.add_roi_layer_button.setEnabled(True)
            print(f"Wybrano okno: '{self.selected_app_window_info_for_new_layer['title']}'")
        else:
            self.add_roi_layer_button.setEnabled(False)
            print("Nie wybrano konkretnego okna.")

    def start_roi_selection_for_new_layer(self):
        if self.is_roi_selection_active:
            print("Tryb zaznaczania ROI jest już aktywny.")
            return
        if not HAS_WIN32:
            QMessageBox.warning(self, "Błąd", "Pywin32 nie jest zainstalowane. Ta funkcja wymaga pywin32 na Windowsie.", QMessageBox.Ok)
            return
        if not self.selected_app_window_info_for_new_layer:
            QMessageBox.warning(self, "Błąd", "Proszę najpierw wybrać aplikację i okno do zaznaczenia ROI.", QMessageBox.Ok)
            return
        self.is_roi_selection_active = True
        self.hide()
        roi_result = self._draw_roi_on_selected_window(self.selected_app_window_info_for_new_layer)
        self.show()
        self.is_roi_selection_active = False
        if roi_result:
            selected_region, window_info = roi_result
            new_layer_name = f"Ekran: {window_info['title']}"
            target_width = int(self.video_label.width() * 0.5)
            target_height = int(target_width / (selected_region['width'] / selected_region['height']) if selected_region['height'] > 0 else target_width)
            target_width = max(MIN_LAYER_SIZE, target_width)
            target_height = max(MIN_LAYER_SIZE, target_height)
            initial_x = (self.video_label.width() - target_width) // 2
            initial_y = (self.video_label.height() - target_height) // 2
            new_layer = ImageState(
                name=new_layer_name,
                source_type=SOURCE_TYPE_SCREEN_REGION,
                initial_width=target_width,
                initial_height=target_height,
                initial_x=initial_x,
                initial_y=initial_y,
                is_visible=True,
                screen_region=selected_region
            )
            new_layer.selected_app_window_info = window_info
            new_layer.aspect_ratio = selected_region['width'] / selected_region['height'] if selected_region['height'] > 0 else 1.0
            self.add_layer(new_layer)
            QMessageBox.information(self, "Sukces", f"Dodano nową warstwę: '{new_layer_name}'", QMessageBox.Ok)
        else:
            QMessageBox.warning(self, "Anulowano", "Zaznaczenie obszaru ROI zostało anulowane.", QMessageBox.Ok)

    def _draw_roi_on_selected_window(self, app_window_info):
        print(f"\n--- ZAZNACZANIE OBSZARU W WYBRANYM OKNIE '{app_window_info['title']}' ---")
        print("Zaznacz myszką prostokątny obszar w tym oknie,")
        print("a następnie naciśnij 'ENTER' lub 'SPACE' aby zatwierdzić.")
        print("Naciśnij 'C' aby anulować zaznaczenie.")
        local_sct = mss.mss()
        app_window_region_coords = {
            "top": app_window_info['top'],
            "left": app_window_info['left'],
            "width": app_window_info['width'],
            "height": app_window_info['height'],
        }
        if app_window_region_coords["width"] <= 0 or app_window_region_coords["height"] <= 0:
            print("Błąd: Wybrane okno ma zerowe lub ujemne wymiary. Nie można wykonać zrzutu. Spróbuj wybrać inne okno.")
            return None
        try:
            sct_img = local_sct.grab(app_window_region_coords)
            if sct_img is None or not sct_img.pixels:
                print("Błąd: Zrzut wybranego okna jest pusty. Upewnij się, że okno jest widoczne i aktywne.")
                return None
            window_np = np.array(sct_img)[:, :, :3]
            print("Pomyślnie wykonano zrzut wybranego okna do zaznaczenia ROI.")
        except mss.exception.ScreenShotError as e:
            print(f"Błąd podczas próby zrzutu wybranego okna (MSS): {e}. Upewnij się, że okno jest widoczne i nie jest zminimalizowane.")
            return None
        except Exception as e:
            print(f"Nieoczekiwany błąd podczas przygotowania zrzutu okna: {e}. Anuluję.")
            return None
        roi_window_title = f"Zaznacz obszar do przechwycenia w: '{app_window_info['title']}'"
        cv2.namedWindow(roi_window_title, cv2.WINDOW_NORMAL)
        if HAS_WIN32:
            roi_hwnd = None
            for _ in range(20):
                roi_hwnd = win32gui.FindWindow(None, roi_window_title)
                if roi_hwnd:
                    break
                time.sleep(0.1)
            if roi_hwnd:
                try:
                    win32gui.ShowWindow(roi_hwnd, win32con.SW_RESTORE)
                    win32gui.SetForegroundWindow(roi_hwnd)
                    print(f"Ustawiono fokus na oknie: '{roi_window_title}' (HW ID: {roi_hwnd})")
                except Exception as e:
                    print(f"Ostrzeżenie: Nie udało się ustawić fokusu na oknie ROI: {e}")
            else:
                print(f"Ostrzeżenie: Nie można znaleźć okna '{roi_window_title}' po jego utworzeniu.")
        roi_rect = cv2.selectROI(roi_window_title,
                                 window_np, fromCenter=False, showCrosshair=True)
        cv2.destroyWindow(roi_window_title)
        x_local, y_local, w, h = roi_rect
        if w > 0 and h > 0:
            x_global = app_window_info['left'] + x_local
            y_global = app_window_info['top'] + y_local
            if w == 0 or h == 0:
                print("Zaznaczenie ROI anulowane lub rozmiar jest zerowy.")
                return None
            selected_screen_region_result = {
                "top": y_global,
                "left": x_global,
                "width": w,
                "height": h,
            }
            print(f"Zaznaczono obszar (Lokalny w oknie: {x_local},{y_local},{w},{h} | GLOBALNY: {x_global},{y_global},{w},{h})")
            return selected_screen_region_result, app_window_info
        else:
            print("Zaznaczenie ROI anulowane lub rozmiar jest zerowy.")
            return None

    def update_frame(self):
        current_preview_window_width = self.video_label.width()
        current_preview_window_height = self.video_label.height()
        if current_preview_window_width <= 0 or current_preview_window_height <= 0:
            blank_frame = np.zeros((max(1, INITIAL_PREVIEW_WINDOW_HEIGHT), max(1, INITIAL_PREVIEW_WINDOW_WIDTH), 3), dtype=np.uint8)
            self.update_image_signal.emit(blank_frame)
            return
        display_frame = np.zeros((current_preview_window_height, current_preview_window_width, 3), dtype=np.uint8)
        for layer_state in self.image_states:
            if not layer_state.is_visible:
                layer_state.original_image = None
                continue
            if layer_state.source_type == SOURCE_TYPE_CAMERA:
                if self.cap and self.cap.isOpened() and layer_state.id == self.active_camera_layer_id:
                    ret, frame_camera = self.cap.read()
                    if ret:
                        frame_camera = cv2.flip(frame_camera, 1)
                        layer_state.original_image = frame_camera
                    else:
                        layer_state.original_image = None
                        print(f"Błąd odczytu klatki z kamery {layer_state.camera_index}. Być może kamera jest używana przez inną aplikację lub odłączona.")
                else:
                    layer_state.original_image = None
            elif layer_state.source_type == SOURCE_TYPE_SCREEN_REGION:
                if layer_state.screen_region:
                    try:
                        sct_img = self.screen_capture_instance.grab(layer_state.screen_region)
                        layer_state.original_image = np.array(sct_img)[:, :, :3]
                    except mss.exception.ScreenShotError:
                        layer_state.original_image = None
                    except Exception as e:
                        layer_state.original_image = None
        for layer_state in self.image_states:
            if not layer_state.is_visible or layer_state.original_image is None or \
               layer_state.display_width <= 0 or layer_state.display_height <= 0:
                continue
            target_width = max(1, layer_state.display_width)
            target_height = max(1, layer_state.display_height)
            if layer_state.original_image.shape[0] == 0 or layer_state.original_image.shape[1] == 0:
                continue
            scaled_image = cv2.resize(layer_state.original_image,
                                      (target_width, target_height),
                                      interpolation=cv2.INTER_AREA)
            x1, y1 = int(layer_state.x), int(layer_state.y)
            x2, y2 = int(layer_state.x + layer_state.display_width), int(layer_state.y + layer_state.display_height)
            paste_x1 = max(0, x1)
            paste_y1 = max(0, y1)
            paste_x2 = min(current_preview_window_width, x2)
            paste_y2 = min(current_preview_window_height, y2)
            src_x1 = max(0, -x1)
            src_y1 = max(0, -y1)
            src_x2 = src_x1 + (paste_x2 - paste_x1)
            src_y2 = src_y1 + (paste_y2 - paste_y1)
            if paste_x2 > paste_x1 and paste_y2 > paste_y1 and \
               src_x2 > src_x1 and src_y2 > src_y1 and \
               src_x2 <= scaled_image.shape[1] and src_y2 <= scaled_image.shape[0]:
                display_frame[paste_y1:paste_y2, paste_x1:paste_x2] = scaled_image[src_y1:src_y2, src_x1:src_x2]
        self.update_image_signal.emit(display_frame)

    def update_video_label(self, cv_img):
        if cv_img is None:
            height, width = self.video_label.height(), self.video_label.width()
            if height <= 0 or width <= 0:
                height = INITIAL_PREVIEW_WINDOW_HEIGHT
                width = INITIAL_PREVIEW_WINDOW_WIDTH
            cv_img = np.zeros((height, width, 3), dtype=np.uint8)
        if len(cv_img.shape) == 3:
            height, width, channel = cv_img.shape
            bytes_per_line = 3 * width
            q_img = QImage(cv_img.data, width, height, bytes_per_line, QImage.Format_RGB888).rgbSwapped()
        else:
            height, width = cv_img.shape
            bytes_per_line = 1 * width
            q_img = QImage(cv_img.data, width, height, bytes_per_line, QImage.Format_Grayscale8)
        pixmap = QPixmap.fromImage(q_img)
        self.video_label.setPixmap(pixmap.scaled(self.video_label.size(),
                                                 Qt.KeepAspectRatio,
                                                 Qt.SmoothTransformation))

    def get_resize_handle_type(self, img_state, mouse_x, mouse_y):
        x, y, w, h = img_state.x, img_state.y, img_state.display_width, img_state.display_height
        handle_size = RESIZE_HANDLE_SIZE
        if (x - handle_size <= mouse_x <= x + handle_size and
            y - handle_size <= mouse_y <= y + handle_size):
            return 'top_left'
        if (x + w - handle_size <= mouse_x <= x + w + handle_size and
            y - handle_size <= mouse_y <= y + handle_size):
            return 'top_right'
        if (x - handle_size <= mouse_x <= x + handle_size and
            y + h - handle_size <= mouse_y <= y + h + handle_size):
            return 'bottom_left'
        if (x + w - handle_size <= mouse_x <= x + w + handle_size and
            y + h - handle_size <= mouse_y <= y + h + handle_size):
            return 'bottom_right'
        if (x - handle_size <= mouse_x <= x + handle_size and
            y + handle_size <= mouse_y <= y + h - handle_size):
            return 'left'
        if (x + w - handle_size <= mouse_x <= x + w + handle_size and
            y + handle_size <= mouse_y <= y + h - handle_size):
            return 'right'
        if (y - handle_size <= mouse_y <= y + handle_size and
            x + handle_size <= mouse_x <= x + w - handle_size):
            return 'top'
        if (y + h - handle_size <= mouse_y <= y + h + handle_size and
            x + handle_size <= mouse_x <= x + w - handle_size):
            return 'bottom'
        return None

    def set_cursor_for_resize_handle(self, handle_type):
        if handle_type == 'top_left' or handle_type == 'bottom_right':
            self.video_label.setCursor(Qt.SizeFDiagCursor)
        elif handle_type == 'top_right' or handle_type == 'bottom_left':
            self.video_label.setCursor(Qt.SizeBDiagCursor)
        elif handle_type == 'left' or handle_type == 'right':
            self.video_label.setCursor(Qt.SizeHorCursor)
        elif handle_type == 'top' or handle_type == 'bottom':
            self.video_label.setCursor(Qt.SizeVerCursor)
        else:
            self.video_label.setCursor(Qt.ArrowCursor)

    def preview_mouse_press_event(self, event: QMouseEvent):
        x, y = event.position().x(), event.position().y()
        self.last_mouse_x = x
        self.last_mouse_y = y
        self.active_draggable_image_state = None
        self.active_resizable_image_state = None
        self.resize_handle_active = None
        for img_state in reversed(self.image_states):
            if not img_state.is_visible or img_state.original_image is None or \
               img_state.display_width <= 0 or img_state.display_height <= 0:
                continue
            handle_type = self.get_resize_handle_type(img_state, x, y)
            if handle_type:
                self.active_resizable_image_state = img_state
                self.resize_handle_active = handle_type
                self.set_cursor_for_resize_handle(handle_type)
                return
            if img_state.x <= x <= img_state.x + img_state.display_width and \
               img_state.y <= y <= img_state.y + img_state.display_height:
                self.active_draggable_image_state = img_state
                self.active_draggable_image_state.is_dragging = True
                self.active_draggable_image_state.drag_offset_x = x - self.active_draggable_image_state.x
                self.active_draggable_image_state.drag_offset_y = y - self.active_draggable_image_state.y
                self.video_label.setCursor(Qt.ClosedHandCursor)
                return

    def preview_mouse_release_event(self, event: QMouseEvent):
        if self.active_draggable_image_state:
            self.active_draggable_image_state.is_dragging = False
        self.active_draggable_image_state = None
        self.active_resizable_image_state = None
        self.resize_handle_active = None
        self.video_label.setCursor(Qt.ArrowCursor)
        self.last_mouse_x = -1
        self.last_mouse_y = -1

    def preview_mouse_move_event(self, event: QMouseEvent):
        x, y = event.position().x(), event.position().y()
        if self.active_resizable_image_state and self.resize_handle_active:
            current_state = self.active_resizable_image_state
            dx = x - self.last_mouse_x
            dy = y - self.last_mouse_y
            original_x = current_state.x
            original_y = current_state.y
            original_width = current_state.display_width
            original_height = current_state.display_height
            new_width = original_width
            new_height = original_height
            new_x = original_x
            new_y = original_y
            if 'right' in self.resize_handle_active:
                new_width = original_width + dx
            if 'bottom' in self.resize_handle_active:
                new_height = original_height + dy
            if 'left' in self.resize_handle_active:
                new_width = original_width - dx
                new_x = original_x + dx
            if 'top' in self.resize_handle_active:
                new_height = original_height - dy
                new_y = original_y + dy
            if current_state.aspect_ratio > 0:
                if 'right' in self.resize_handle_active or 'left' in self.resize_handle_active:
                    new_height = int(new_width / current_state.aspect_ratio)
                elif 'bottom' in self.resize_handle_active or 'top' in self.resize_handle_active:
                    new_width = int(new_height * current_state.aspect_ratio)
            new_width = max(MIN_LAYER_SIZE, min(MAX_LAYER_SIZE, new_width))
            new_height = max(MIN_LAYER_SIZE, min(MAX_LAYER_SIZE, new_height))
            if 'left' in self.resize_handle_active:
                new_x = original_x + (original_width - new_width)
            if 'top' in self.resize_handle_active:
                new_y = original_y + (original_height - new_height)
            current_state.display_width = new_width
            current_state.display_height = new_height
            current_state.x = new_x
            current_state.y = new_y
        elif self.active_draggable_image_state and self.active_draggable_image_state.is_dragging:
            current_state = self.active_draggable_image_state
            current_state.x = int(x - current_state.drag_offset_x)
            current_state.y = int(y - current_state.drag_offset_y)
            self.video_label.setCursor(Qt.ClosedHandCursor)
        else:
            found_handle = False
            for img_state in reversed(self.image_states):
                if img_state.is_visible and img_state.original_image is not None:
                    handle_type = self.get_resize_handle_type(img_state, x, y)
                    if handle_type:
                        self.set_cursor_for_resize_handle(handle_type)
                        found_handle = True
                        break
            if not found_handle:
                self.video_label.setCursor(Qt.ArrowCursor)
        self.last_mouse_x = x
        self.last_mouse_y = y

    def preview_mouse_wheel_event(self, event: QWheelEvent):
        x, y = event.position().x(), event.position().y()
        delta = event.angleDelta().y() / 120
        zoom_factor = 1.0 + delta * 0.1
        target_state = None
        for img_state in reversed(self.image_states):
            if img_state.is_visible and img_state.original_image is not None and \
               img_state.x <= x <= img_state.x + img_state.display_width and \
               img_state.y <= y <= img_state.y + img_state.display_height:
                target_state = img_state
                break
        if target_state is None:
            return
        if target_state.original_image is not None:
            new_width = int(target_state.display_width * zoom_factor)
            new_height = int(target_state.display_height * zoom_factor)
            new_width = max(MIN_LAYER_SIZE, min(MAX_LAYER_SIZE, new_width))
            if target_state.aspect_ratio > 0:
                new_height = int(new_width / target_state.aspect_ratio)
            new_height = max(MIN_LAYER_SIZE, min(MAX_LAYER_SIZE, new_height))
            if target_state.aspect_ratio > 0:
                if new_height != int(new_width / target_state.aspect_ratio):
                    new_width = int(new_height * target_state.aspect_ratio)
                    new_width = max(MIN_LAYER_SIZE, min(MAX_LAYER_SIZE, new_width))
            rel_x = (x - target_state.x) / target_state.display_width if target_state.display_width > 0 else 0.5
            rel_y = (y - target_state.y) / target_state.display_height if target_state.display_height > 0 else 0.5
            target_state.display_width = new_width
            target_state.display_height = new_height
            target_state.x = int(x - rel_x * target_state.display_width)
            target_state.y = int(y - rel_y * target_state.display_height)

    def keyPressEvent(self, event):
        selected_layer_id = self.layers_combobox.currentData()
        if selected_layer_id:
            layer = self.get_layer_by_id(selected_layer_id)
            if layer:
                if event.key() == Qt.Key_Left:
                    layer.x -= MOVE_STEP
                elif event.key() == Qt.Key_Right:
                    layer.x += MOVE_STEP
                elif event.key() == Qt.Key_Up:
                    layer.y -= MOVE_STEP
                elif event.key() == Qt.Key_Down:
                    layer.y += MOVE_STEP
                event.accept()
            else:
                event.ignore()
        else:
            event.ignore()

    def closeEvent(self, event):
        if self.cap and self.cap.isOpened():
            self.cap.release()
        self.timer.stop()
        print("Aplikacja zamknięta.")
        super().closeEvent(event)

if __name__ == "__main__":
    app = QApplication(sys.argv)
    window = CameraScreenOverlayApp()
    window.show()
    sys.exit(app.exec())
