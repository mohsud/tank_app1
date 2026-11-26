import array
import io
import json
import math
import os
import random
import tempfile
import traceback
import wave
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple

from kivy.app import App
from kivy.clock import Clock
from kivy.core.audio import SoundLoader
from kivy.core.image import Image as CoreImage
from kivy.core.text import Label as CoreLabel
from kivy.core.window import Window
from kivy.graphics import Color, Ellipse, Line, PopMatrix, PushMatrix, Rectangle, Rotate, Scale, Translate
from kivy.uix.widget import Widget
from kivy.utils import platform

# ==============================================================================
# 1. DISPLAY & GAME CONSTANTS 
# ==============================================================================

SCREEN_WIDTH = 540
SCREEN_HEIGHT = 900
FPS = 60.0
TITLE = "Base Defense"

SAVE_FILE = "t_save.json"
MAP_IMAGE_PATH = "assets/map.png"

MAX_TURRET_TIER = 4
MAX_POINTS = 15.0
STARTING_POINTS = 6.0
BASE_POINTS_REGEN_PER_SEC = 0.45
POINTS_REGEN_PER_SEC = BASE_POINTS_REGEN_PER_SEC
BASE_MAX_HP = 10
DOCK_SLOTS_COUNT = 6
DEFENSE_SLOTS_COUNT = 6

# Unified turret HP per tier across all 3 turret types
TURRET_TIER_HP: Dict[int, float] = {
    1: 55.0,
    2: 70.0,
    3: 78.0,
    4: 95.0,
}

# Healer: heals ONE damaged turret every 3.0 seconds
HEALER_INTERVAL_SEC = 3.0
HEALER_BUILD_COST = 10
HEALER_UPGRADE_COSTS: Dict[int, int] = {
    1: 8,
    2: 9,
    3: 12,
    4: 15,
}
HEALER_MAX_LEVEL = 5
HEALER_HEAL_PER_TICK: Dict[int, float] = {
    1: 10.0,
    2: 14.0,
    3: 18.0,
    4: 22.0,
    5: 26.0,
}

BOSS_ATTACK_INTERVAL_SEC = 3.0


def rgb(r: int, g: int, b: int, a: float = 1.0) -> Tuple[float, float, float, float]:
    return (r / 255.0, g / 255.0, b / 255.0, a)


BG_DARK = rgb(14, 24, 16)
PANEL_BG = rgb(16, 28, 18, 0.92)
SLOT_BG = rgb(20, 42, 22, 0.86)
SLOT_BORDER = rgb(125, 195, 110, 0.90)

WHITE = rgb(245, 250, 245)
BLACK = rgb(8, 12, 10)
GRAY = rgb(150, 165, 155)
CYAN = rgb(50, 175, 245)
BLUE = rgb(65, 145, 255)
PURPLE = rgb(185, 75, 255)
PINK = rgb(255, 70, 165)
RED = rgb(235, 65, 55)
ORANGE = rgb(255, 145, 35)
YELLOW = rgb(245, 195, 45)
GREEN = rgb(65, 225, 115)
TEAL = rgb(45, 220, 185)
GOLD = rgb(255, 215, 65)

DIFFICULTY_CONFIGS: Dict[str, Dict[str, object]] = {
    "EASY": {
        "label": "EASY",
        "color": GREEN,
        "points_regen": BASE_POINTS_REGEN_PER_SEC * 1.35,
        "enemy_speed_mult": 0.82,
        "enemy_hp_mult": 0.95,
    },
    "MEDIUM": {
        "label": "MEDIUM",
        "color": YELLOW,
        "points_regen": BASE_POINTS_REGEN_PER_SEC,
        "enemy_speed_mult": 1.0,
        "enemy_hp_mult": 1.18,
    },
    "HARD": {
        "label": "HARD",
        "color": RED,
        "points_regen": BASE_POINTS_REGEN_PER_SEC * 0.90,
        "enemy_speed_mult": 1.22,
        "enemy_hp_mult": 1.48,
    },
}
DIFFICULTY_ORDER = ["EASY", "MEDIUM", "HARD"]
CURRENT_DIFFICULTY = "MEDIUM"


def get_difficulty_cfg(diff: Optional[str] = None) -> Dict[str, object]:
    key = diff or CURRENT_DIFFICULTY
    return DIFFICULTY_CONFIGS.get(key, DIFFICULTY_CONFIGS["MEDIUM"])


# ==============================================================================
# 2. MATH, MAP WAYPOINTS & TWO CLEAR PARALLEL LANES
# ==============================================================================

def clamp(v: float, lo: float, hi: float) -> float:
    return max(lo, min(hi, v))


def dist(x1: float, y1: float, x2: float, y2: float) -> float:
    return math.hypot(x2 - x1, y2 - y1)


def norm(dx: float, dy: float) -> Tuple[float, float]:
    d = math.hypot(dx, dy)
    if d == 0:
        return 0.0, 0.0
    return dx / d, dy / d


def to_ky(y: float) -> float:
    return SCREEN_HEIGHT - y


def norm_to_logical(nx: float, ny_bottom_up: float) -> Tuple[float, float]:
    return nx * SCREEN_WIDTH, (1.0 - ny_bottom_up) * SCREEN_HEIGHT


PATH_WAYPOINTS_NORM: List[Tuple[float, float]] = [
    (0.08, 0.805),
    (0.30, 0.798),
    (0.55, 0.785),
    (0.76, 0.778),
    (0.84, 0.742),
    (0.855, 0.650),
    (0.845, 0.562),
    (0.78, 0.530),
    (0.55, 0.526),
    (0.32, 0.536),
    (0.165, 0.520),
    (0.145, 0.460),
    (0.145, 0.340),
    (0.165, 0.275),
    (0.24, 0.245),
    (0.48, 0.238),
    (0.72, 0.242),
    (0.92, 0.235),
]

LANE_POINTS: List[Tuple[float, float]] = [norm_to_logical(nx, ny) for nx, ny in PATH_WAYPOINTS_NORM]

DEFENSE_SLOTS_NORM: List[Tuple[float, float]] = [
    (0.27, 0.655),
    (0.50, 0.655),
    (0.72, 0.655),
    (0.35, 0.398),
    (0.55, 0.398),
    (0.74, 0.405),
]

TOWER_PADS: List[Tuple[float, float]] = [norm_to_logical(nx, ny) for nx, ny in DEFENSE_SLOTS_NORM]

HEALER_PAD_NORM: Tuple[float, float] = (0.89, 0.168)
HEALER_PAD: Tuple[float, float] = norm_to_logical(HEALER_PAD_NORM[0], HEALER_PAD_NORM[1])


def _segment_normal(idx: int) -> Tuple[float, float, float]:
    n_pts = len(LANE_POINTS)
    if n_pts < 2:
        return 0.0, -1.0, 0.0
    i0 = int(clamp(idx, 0, n_pts - 2))
    x1, y1 = LANE_POINTS[i0]
    x2, y2 = LANE_POINTS[i0 + 1]
    dx = x2 - x1
    dy = y2 - y1
    d = math.hypot(dx, dy) or 1.0
    ang = math.degrees(math.atan2(dy, dx))
    return -dy / d, dx / d, ang


def get_lane_point_logical(seg_idx: int, t: float, lane_sign: float) -> Tuple[float, float, float]:
    if seg_idx >= len(LANE_POINTS) - 1:
        nx, ny, ang = _segment_normal(len(LANE_POINTS) - 2)
        ex, ey = LANE_POINTS[-1]
        sep = SCREEN_WIDTH * 0.025
        return ex + nx * lane_sign * sep, ey + ny * lane_sign * sep, ang

    x1, y1 = LANE_POINTS[seg_idx]
    x2, y2 = LANE_POINTS[seg_idx + 1]
    dx = x2 - x1
    dy = y2 - y1
    ang = math.degrees(math.atan2(dy, dx))

    nx1, ny1, _ = _segment_normal(seg_idx)
    if seg_idx < len(LANE_POINTS) - 2:
        nx2, ny2, _ = _segment_normal(seg_idx + 1)
        blend = clamp((t - 0.65) / 0.35, 0.0, 1.0)
        nx = nx1 * (1.0 - blend) + nx2 * blend
        ny = ny1 * (1.0 - blend) + ny2 * blend
        nx, ny = norm(nx, ny)
    else:
        nx, ny = nx1, ny1

    lane_sep = SCREEN_WIDTH * 0.025
    bx = x1 + dx * t + nx * lane_sign * lane_sep
    by = y1 + dy * t + ny * lane_sign * lane_sep
    return bx, by, ang


# ==============================================================================
# 3. SPRITE ASSETS LOADER & SAVE DATA
# ==============================================================================

TURRET_CAP_PREFIX: Dict[str, str] = {
    "sniper": "Sniper",
    "gatling": "Machine_Gun",
    "mortar": "Cannon",
}

TURRET_FILE_PREFIX: Dict[str, str] = {
    "sniper": "sniper",
    "gatling": "machine_gun",
    "mortar": "cannon",
}

# Strictly 5 enemy sprites: tank_1.png .. tank_5.png
TANK_FILE_NAMES: Dict[str, List[str]] = {
    "scout": ["tank_1.png", "tank_scout.png"],
    "light": ["tank_2.png", "tank_light.png"],
    "armored": ["tank_3.png", "tank_armored.png"],
    "siege": ["tank_4.png", "tank_siege.png"],
    "boss": ["tank_5.png", "tank_boss.png", "boss.png"],
}


def resolve_base_dir() -> str:
    return os.path.dirname(os.path.abspath(__file__))


def resolve_assets_dir() -> str:
    return os.path.join(resolve_base_dir(), "assets")


def resolve_save_path() -> str:
    return os.path.join(resolve_base_dir(), SAVE_FILE)


def load_best_stats() -> Tuple[int, int]:
    path = resolve_save_path()
    if os.path.exists(path):
        try:
            with open(path, "r", encoding="utf-8") as f:
                data = json.load(f)
            return int(data.get("high_score", data.get("best_score", 0))), int(data.get("best_wave", 1))
        except Exception:
            pass
    return 0, 1


def save_best_stats(best_score: int, best_wave: int):
    path = resolve_save_path()
    try:
        with open(path, "w", encoding="utf-8") as f:
            json.dump({"high_score": int(best_score), "best_wave": int(best_wave)}, f, indent=2)
    except Exception:
        pass


def _find_image_file(filename: str) -> Optional[str]:
    search_roots = [resolve_assets_dir(), resolve_base_dir()]
    for root in search_roots:
        if not os.path.isdir(root):
            continue
        direct = os.path.join(root, filename)
        if os.path.exists(direct):
            return direct
        for current_dir, _, _ in os.walk(root):
            candidate = os.path.join(current_dir, filename)
            if os.path.exists(candidate):
                return candidate
    return None


def load_texture_by_candidates(filenames: List[str]) -> Optional[object]:
    for fname in filenames:
        found = _find_image_file(fname)
        if found:
            try:
                img = CoreImage(found)
                if img.texture is not None:
                    return img.texture
            except Exception as exc:
                print(f"[ASSET ERROR] {found}: {exc}")
    return None


def load_turret_textures() -> Dict[Tuple[str, int], object]:
    textures: Dict[Tuple[str, int], object] = {}
    for unit_type, cap_prefix in TURRET_CAP_PREFIX.items():
        low_prefix = TURRET_FILE_PREFIX[unit_type]
        for tier in range(1, MAX_TURRET_TIER + 1):
            candidates = [
                f"{cap_prefix}_{tier}.png",
                f"{low_prefix}_level_{tier}.png",
                f"T{tier}_{low_prefix}.png",
            ]
            tex = load_texture_by_candidates(candidates)
            if tex is not None:
                textures[(unit_type, tier)] = tex
    return textures


def load_tank_textures() -> Dict[str, object]:
    textures: Dict[str, object] = {}
    for tank_kind, candidates in TANK_FILE_NAMES.items():
        tex = load_texture_by_candidates(candidates)
        if tex is not None:
            textures[tank_kind] = tex
    return textures


# ==============================================================================
# 4. PROCEDURAL WAV AUDIO ENGINE
# ==============================================================================

class AudioEngine:
    def __init__(self):
        self.sounds: Dict[str, object] = {}
        self._temp_files: List[str] = []
        self._build_sounds()

    def _make_wav_file(
        self,
        name: str,
        dur: float,
        f0: float,
        f1: float,
        wave_type: str = "sine",
        vol: float = 0.2,
        decay: float = 1.3,
    ):
        sr = 22050
        n = max(1, int(sr * dur))
        samples = array.array("h", [0] * n)
        phase = 0.0
        for i in range(n):
            t = i / max(1, n - 1)
            freq = f0 + (f1 - f0) * t
            phase += (2.0 * math.pi * freq) / sr
            if wave_type == "square":
                s = 1.0 if math.sin(phase) >= 0 else -1.0
            elif wave_type == "saw":
                s = 2.0 * ((phase / (2.0 * math.pi)) % 1.0) - 1.0
            else:
                s = math.sin(phase)
            env = ((1.0 - t) ** decay) * vol
            samples[i] = int(clamp(s * env * 32767.0, -32767.0, 32767.0))

        mem = io.BytesIO()
        with wave.open(mem, "wb") as wf:
            wf.setnchannels(1)
            wf.setsampwidth(2)
            wf.setframerate(sr)
            wf.writeframes(samples.tobytes())

        try:
            fd, path = tempfile.mkstemp(prefix=f"basedef_{name}_", suffix=".wav")
            with os.fdopen(fd, "wb") as out:
                out.write(mem.getvalue())
            self._temp_files.append(path)
            snd = SoundLoader.load(path)
            if snd:
                self.sounds[name] = snd
        except Exception:
            pass

    def _build_sounds(self):
        self._make_wav_file("sniper", 0.12, 340, 70, "saw", 0.20, 1.5)
        self._make_wav_file("gatling", 0.05, 680, 340, "square", 0.10, 1.8)
        self._make_wav_file("mortar", 0.18, 190, 52, "saw", 0.23, 1.2)
        self._make_wav_file("merge", 0.28, 360, 920, "sine", 0.25, 0.8)
        self._make_wav_file("spawn", 0.14, 240, 520, "sine", 0.18, 1.1)
        self._make_wav_file("enemy_hit", 0.05, 420, 180, "sine", 0.08, 1.6)
        self._make_wav_file("enemy_die", 0.19, 310, 65, "saw", 0.20, 1.3)
        self._make_wav_file("base_hit", 0.32, 140, 42, "square", 0.30, 1.0)
        self._make_wav_file("boss_shell", 0.24, 155, 42, "saw", 0.28, 1.1)
        self._make_wav_file("heal", 0.14, 480, 780, "sine", 0.16, 1.2)

    def play(self, name: str):
        snd = self.sounds.get(name)
        if snd is not None:
            try:
                snd.stop()
                snd.play()
            except Exception:
                pass

    def cleanup(self):
        for p in self._temp_files:
            try:
                if os.path.exists(p):
                    os.remove(p)
            except Exception:
                pass


# ==============================================================================
# 5. VISUAL FX, IMPACT FLASHES, ALERTS & HEAVY SHELLS
# ==============================================================================

@dataclass
class Particle:
    x: float
    y: float
    vx: float
    vy: float
    color: Tuple[float, float, float, float]
    size: float
    life: float
    max_life: float

    def update(self, dt: float) -> bool:
        self.x += self.vx * dt
        self.y += self.vy * dt
        self.vx *= 0.93 ** (dt * 60)
        self.vy *= 0.93 ** (dt * 60)
        self.life -= dt
        return self.life > 0


@dataclass
class Shockwave:
    x: float
    y: float
    max_radius: float
    color: Tuple[float, float, float, float]
    width: float = 2.4
    life: float = 0.34
    max_life: float = 0.34

    def update(self, dt: float) -> bool:
        self.life -= dt
        return self.life > 0


@dataclass
class ImpactFlash:
    x: float
    y: float
    dx: float
    dy: float
    color: Tuple[float, float, float, float]
    length: float = 15.0
    width: float = 2.6
    life: float = 0.11
    max_life: float = 0.11

    def update(self, dt: float) -> bool:
        self.life -= dt
        return self.life > 0


@dataclass
class HealArcFX:
    x1: float
    y1: float
    x2: float
    y2: float
    color: Tuple[float, float, float, float]
    width: float = 2.8
    life: float = 0.22
    max_life: float = 0.22

    def update(self, dt: float) -> bool:
        self.life -= dt
        return self.life > 0


@dataclass
class BossShellFX:
    x: float
    y: float
    target_x: float
    target_y: float
    pad_idx: int
    damage: float
    speed: float = 420.0

    def update(self, dt: float) -> bool:
        dx = self.target_x - self.x
        dy = self.target_y - self.y
        d = math.hypot(dx, dy)
        step = self.speed * dt
        if d <= step or d == 0.0:
            self.x = self.target_x
            self.y = self.target_y
            return True
        self.x += (dx / d) * step
        self.y += (dy / d) * step
        return False


@dataclass
class FloatingPopup:
    x: float
    y: float
    text: str
    color: Tuple[float, float, float, float]
    life: float = 0.75
    vy: float = -40.0

    def update(self, dt: float) -> bool:
        self.y += self.vy * dt
        self.life -= dt
        return self.life > 0


@dataclass
class WaveWarningAlert:
    kind: str
    title: str
    subtitle: str
    color: Tuple[float, float, float, float]
    life: float = 3.2
    max_life: float = 3.2

    def update(self, dt: float) -> bool:
        self.life -= dt
        return self.life > 0


# ==============================================================================
# 6. 5 TANK TYPES (DRAMATIC SIZE CONTRAST 1->5) & WAVE GENERATOR
# ==============================================================================

TANK_ORDER: List[str] = ["scout", "light", "armored", "siege", "boss"]

# Enemy HP reduced by 20% across all 5 tank types
TANK_SPECS: Dict[str, Dict[str, object]] = {
    "scout": {
        "name": "SCOUT",
        "base_hp": 264.0,
        "speed_ratio": 0.082,
        "radius": 6.5,
        "sprite_mult": 1.80,
        "color": ORANGE,
        "score": 15,
    },
    "light": {
        "name": "LIGHT",
        "base_hp": 448.0,
        "speed_ratio": 0.068,
        "radius": 9.5,
        "sprite_mult": 1.95,
        "color": rgb(92, 145, 72),
        "score": 25,
    },
    "armored": {
        "name": "ARMORED",
        "base_hp": 768.0,
        "speed_ratio": 0.052,
        "radius": 13.5,
        "sprite_mult": 2.10,
        "color": BLUE,
        "score": 45,
    },
    "siege": {
        "name": "SIEGE",
        "base_hp": 1384.0,
        "speed_ratio": 0.040,
        "radius": 18.5,
        "sprite_mult": 2.25,
        "color": RED,
        "score": 80,
    },
    "boss": {
        "name": "BOSS",
        "base_hp": 2680.0,
        "speed_ratio": 0.025,
        "radius": 29.0,
        "sprite_mult": 2.50,
        "color": PURPLE,
        "score": 250,
    },
}


def is_big_boss_wave(wave_num: int) -> bool:
    return wave_num >= 15 and wave_num % 5 == 0


def get_boss_shell_damage(wave_num: int) -> float:
    """Starts at 20 on wave 15, +5 every 5 waves, capped at 40 on wave 35+."""
    if wave_num < 15:
        return 20.0
    capped_wave = min(wave_num, 35)
    five_wave_steps = max(0, (capped_wave - 15) // 5)
    return float(20 + five_wave_steps * 5)


def build_wave_sequence(wave_num: int) -> List[str]:
    if wave_num == 1:
        count = 2
    elif wave_num == 2:
        count = 2
    elif wave_num == 3:
        count = 3
    else:
        count = min(6, 3 + (wave_num + 1) // 2)

    pool: List[str] = ["scout"]
    if wave_num >= 2:
        pool.append("light")
    if wave_num >= 4:
        pool.append("armored")
    if wave_num >= 7:
        pool.append("siege")

    wave_list: List[str] = []
    for i in range(count):
        if wave_num == 1:
            t_type = "scout"
        elif wave_num == 2:
            t_type = "light" if i == count - 1 else "scout"
        elif wave_num == 3:
            t_type = ["scout", "light", "armored"][i % 3]
        elif wave_num < 6:
            weights = [0.35, 0.40, 0.25] if "armored" in pool else [0.50, 0.50]
            t_type = random.choices(pool, weights=weights)[0]
        elif wave_num < 10:
            weights = [0.22, 0.33, 0.28, 0.17] if "siege" in pool else [0.30, 0.40, 0.30]
            t_type = random.choices(pool, weights=weights)[0]
        else:
            t_type = random.choices(["scout", "light", "armored", "siege"], weights=[0.15, 0.25, 0.30, 0.30])[0]
        wave_list.append(t_type)

    if is_big_boss_wave(wave_num):
        wave_list.append("boss")

    return wave_list


def summarize_wave_counts(wave_list: List[str]) -> List[Tuple[str, int]]:
    counts = {k: 0 for k in TANK_ORDER}
    for t in wave_list:
        if t in counts:
            counts[t] += 1
    return [(k, counts[k]) for k in TANK_ORDER if counts[k] > 0]


@dataclass
class TankEnemy:
    kind: str
    max_hp: float
    hp: float
    speed_px: float
    radius: float
    sprite_mult: float
    color: Tuple[float, float, float, float]
    score_reward: int
    lane_sign: float
    seg_idx: int = 0
    progress_in_seg: float = 0.0
    x: float = LANE_POINTS[0][0]
    y: float = LANE_POINTS[0][1]
    facing_angle: float = 0.0
    hit_flash: float = 0.0
    slow_timer: float = 0.0
    slow_amount: float = 0.0
    boss_attack_cd: float = 0.0

    @classmethod
    def create(cls, kind: str, wave: int, lane_sign: float) -> "TankEnemy":
        cfg = get_difficulty_cfg()
        hp_mult = float(cfg["enemy_hp_mult"])
        spd_mult = float(cfg["enemy_speed_mult"])

        spec = TANK_SPECS[kind]
        wave_hp_mult = 1.0 + (wave - 1) * 0.24
        total_hp = float(spec["base_hp"]) * wave_hp_mult * hp_mult
        spd_px = float(spec["speed_ratio"]) * SCREEN_HEIGHT * spd_mult
        rad = float(spec["radius"])
        sp_mult = float(spec.get("sprite_mult", 2.15))
        col = spec["color"]  # type: ignore
        scr = int(spec["score"]) + (wave - 1) * 8

        bx, by, ang = get_lane_point_logical(0, 0.0, lane_sign)
        return cls(
            kind=kind,
            max_hp=total_hp,
            hp=total_hp,
            speed_px=spd_px,
            radius=rad,
            sprite_mult=sp_mult,
            color=col,
            score_reward=scr,
            lane_sign=lane_sign,
            x=bx,
            y=by,
            facing_angle=ang,
            boss_attack_cd=1.2 if kind == "boss" else 0.0,
        )

    def apply_slow(self, slow_pct: float, duration: float):
        if self.slow_timer <= 0.0 or slow_pct >= self.slow_amount:
            self.slow_amount = slow_pct
        self.slow_timer = max(self.slow_timer, duration)

    def update(self, dt: float) -> bool:
        self.hit_flash = max(0.0, self.hit_flash - dt)
        if self.slow_timer > 0.0:
            self.slow_timer = max(0.0, self.slow_timer - dt)
            if self.slow_timer <= 0.0:
                self.slow_amount = 0.0
        self.boss_attack_cd = max(0.0, self.boss_attack_cd - dt)
        if self.seg_idx >= len(LANE_POINTS) - 1:
            return True

        spd_mult = clamp(1.0 - self.slow_amount, 0.15, 1.0) if self.slow_timer > 0.0 else 1.0
        x1, y1 = LANE_POINTS[self.seg_idx]
        x2, y2 = LANE_POINTS[self.seg_idx + 1]
        seg_len = math.hypot(x2 - x1, y2 - y1) or 1.0
        self.progress_in_seg += (self.speed_px * spd_mult * dt) / seg_len

        while self.progress_in_seg >= 1.0 and self.seg_idx < len(LANE_POINTS) - 1:
            self.progress_in_seg -= 1.0
            self.seg_idx += 1

        if self.seg_idx >= len(LANE_POINTS) - 1:
            return True

        bx, by, ang = get_lane_point_logical(self.seg_idx, self.progress_in_seg, self.lane_sign)
        self.x, self.y, self.facing_angle = bx, by, ang
        return False


@dataclass
class LaneProjectile:
    x: float
    y: float
    vx: float
    vy: float
    damage: float
    color: Tuple[float, float, float, float]
    unit_type: str = "sniper"
    tier: int = 1
    length: float = 13.0
    thickness: float = 4.5
    radius: float = 5.5
    splash_radius: float = 0.0
    slow_pct: float = 0.0
    slow_duration: float = 0.0
    target: Optional[TankEnemy] = None
    last_tx: float = 0.0
    last_ty: float = 0.0
    life: float = 2.0

    def update(self, dt: float) -> bool:
        self.life -= dt
        if self.life <= 0:
            return False
        if self.target is not None and self.target.hp > 0:
            self.last_tx = self.target.x
            self.last_ty = self.target.y
        spd = math.hypot(self.vx, self.vy)
        nx, ny = norm(self.last_tx - self.x, self.last_ty - self.y)
        self.vx, self.vy = nx * spd, ny * spd
        self.x += self.vx * dt
        self.y += self.vy * dt
        return True


# ==============================================================================
# 7. DEFENSE UNITS (MAX L4, UNIFIED HP PER TIER) & SINGLE-TARGET HEALER
# ==============================================================================

UNIT_META: Dict[str, Dict[str, object]] = {
    "sniper": {
        "name": "SNIPER",
        "short": "SNIPER",
        "cost": 3,
        "color": CYAN,
        "base_dmg": 65.0,
        "fire_rate": 1.45,
        "range": SCREEN_WIDTH * 0.36,
        "splash": 0.0,
        "proj_spd": 750.0,
        "bullet_color": rgb(110, 225, 255),
        "recoil_kick": 3.4,
    },
    "gatling": {
        "name": "MG",
        "short": "MG",
        "cost": 5,
        "color": YELLOW,
        "base_dmg": 14.0,
        "fire_rate": 0.22,
        "range": SCREEN_WIDTH * 0.345,
        "splash": 0.0,
        "proj_spd": 850.0,
        "bullet_color": rgb(255, 225, 85),
        "recoil_kick": 1.7,
    },
    "mortar": {
        "name": "ARTILLERY",
        "short": "ARTILLERY",
        "cost": 7,
        "color": RED,
        "base_dmg": 48.0,
        "fire_rate": 1.85,
        "range": SCREEN_WIDTH * 0.34,
        "splash": SCREEN_WIDTH * 0.095,
        "proj_spd": 480.0,
        "bullet_color": rgb(255, 110, 45),
        "recoil_kick": 4.2,
    },
}


@dataclass
class DefenseUnit:
    unit_type: str
    tier: int = 1
    hp: float = 55.0
    max_hp: float = 55.0
    cooldown: float = 0.0
    aim_angle: float = 0.0
    recoil_px: float = 0.0

    def __post_init__(self):
        self.tier = int(clamp(self.tier, 1, MAX_TURRET_TIER))
        self.max_hp = TURRET_TIER_HP.get(self.tier, TURRET_TIER_HP[1])
        if self.hp <= 0:
            self.hp = self.max_hp
        else:
            self.hp = min(self.hp, self.max_hp)

    def get_refund_points(self) -> float:
        base_cost = int(UNIT_META[self.unit_type]["cost"])
        return float(max(1, (base_cost * self.tier) // 2))

    def upgrade_to_next_tier(self) -> bool:
        if self.tier >= MAX_TURRET_TIER:
            return False
        hp_ratio = clamp(self.hp / max(1.0, self.max_hp), 0.0, 1.0)
        self.tier += 1
        self.max_hp = TURRET_TIER_HP.get(self.tier, TURRET_TIER_HP[MAX_TURRET_TIER])
        self.hp = max(self.hp, self.max_hp * hp_ratio)
        return True

    @property
    def color(self) -> Tuple[float, float, float, float]:
        return UNIT_META[self.unit_type]["color"]  # type: ignore

    def get_damage(self) -> float:
        base = float(UNIT_META[self.unit_type]["base_dmg"])
        return base * (1.55 ** (self.tier - 1))

    def get_fire_rate(self) -> float:
        base_rate = float(UNIT_META[self.unit_type]["fire_rate"])
        return max(0.08, base_rate * (0.93 ** (self.tier - 1)))

    def get_range(self) -> float:
        base_rng = float(UNIT_META[self.unit_type]["range"])
        return base_rng * (1.0 + 0.08 * (self.tier - 1))

    def get_splash(self) -> float:
        base_spl = float(UNIT_META[self.unit_type]["splash"])
        return base_spl * (1.0 + 0.08 * (self.tier - 1))

    def get_slow_stats(self) -> Tuple[float, float]:
        """Doubled slow effect: 50% for 2.0s at L1, 70% for 3.0s at L2+."""
        if self.unit_type != "mortar":
            return 0.0, 0.0
        if self.tier <= 1:
            return 0.50, 2.0
        return 0.70, 3.0

    def update_and_fire(
        self,
        dt: float,
        pos: Tuple[float, float],
        enemies: List[TankEnemy],
        projectiles: List[LaneProjectile],
        audio: AudioEngine,
    ):
        if self.hp <= 0:
            return
        self.cooldown = max(0.0, self.cooldown - dt)
        self.recoil_px = max(0.0, self.recoil_px - dt * 16.0)

        rng = self.get_range()
        best_enemy: Optional[TankEnemy] = None
        best_progress = -1.0

        for e in enemies:
            if e.hp <= 0:
                continue
            if dist(pos[0], pos[1], e.x, e.y) <= rng:
                prog = e.seg_idx + e.progress_in_seg
                if prog > best_progress:
                    best_progress = prog
                    best_enemy = e

        if best_enemy is not None:
            self.aim_angle = math.atan2(best_enemy.y - pos[1], best_enemy.x - pos[0])
            if self.cooldown <= 0.0:
                self.cooldown = self.get_fire_rate()
                self.recoil_px = float(UNIT_META[self.unit_type]["recoil_kick"])
                dmg = self.get_damage()
                spd = float(UNIT_META[self.unit_type]["proj_spd"])
                spl = self.get_splash()
                slow_pct, slow_dur = self.get_slow_stats()
                bcol = UNIT_META[self.unit_type]["bullet_color"]  # type: ignore
                nx, ny = norm(best_enemy.x - pos[0], best_enemy.y - pos[1])

                if self.unit_type == "sniper":
                    slug_len = 16.0 + self.tier * 2.0
                    slug_thick = 3.8 + self.tier * 0.5
                elif self.unit_type == "gatling":
                    slug_len = 10.5 + self.tier * 1.2
                    slug_thick = 3.2 + self.tier * 0.4
                else:
                    slug_len = 12.0 + self.tier * 1.6
                    slug_thick = 5.4 + self.tier * 0.7

                audio.play(self.unit_type)
                projectiles.append(
                    LaneProjectile(
                        x=pos[0] + nx * 18.0,
                        y=pos[1] + ny * 18.0,
                        vx=nx * spd,
                        vy=ny * spd,
                        damage=dmg,
                        color=bcol,
                        unit_type=self.unit_type,
                        tier=self.tier,
                        length=slug_len,
                        thickness=slug_thick,
                        radius=max(4.5, slug_thick * 0.85),
                        splash_radius=spl,
                        slow_pct=slow_pct,
                        slow_duration=slow_dur,
                        target=best_enemy,
                        last_tx=best_enemy.x,
                        last_ty=best_enemy.y,
                    )
                )


@dataclass
class HealerUnit:
    level: int = 1
    heal_cd: float = 0.0

    @property
    def heal_amount(self) -> float:
        return HEALER_HEAL_PER_TICK.get(self.level, HEALER_HEAL_PER_TICK[1])

    def next_upgrade_cost(self) -> Optional[int]:
        if self.level >= HEALER_MAX_LEVEL:
            return None
        return HEALER_UPGRADE_COSTS.get(self.level)


# ==============================================================================
# 8. KIVY WIDGET & ENGINE
# ==============================================================================

@dataclass
class RectBox:
    x: float
    y: float
    w: float
    h: float

    @property
    def centerx(self) -> float:
        return self.x + self.w * 0.5

    @property
    def centery(self) -> float:
        return self.y + self.h * 0.5

    def collidepoint(self, px: float, py: float) -> bool:
        return self.x <= px <= self.x + self.w and self.y <= py <= self.y + self.h


class BaseDefenseWidget(Widget):
    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        self.size_hint = (None, None)
        self.pos = (0, 0)
        self.size = (Window.width, Window.height)

        self.state = "TITLE"
        self._state_before_guide = "TITLE"
        self._text_cache: Dict[Tuple[str, int, bool], Tuple[object, int, int]] = {}
        self.best_score, self.best_wave = load_best_stats()

        self.audio = AudioEngine()
        self.map_texture: Optional[object] = load_texture_by_candidates(["map.png"])
        self.info_texture: Optional[object] = load_texture_by_candidates(["info.png"])
        self.turret_textures: Dict[Tuple[str, int], object] = load_turret_textures()
        self.tank_textures: Dict[str, object] = load_tank_textures()

        self.btn_pause = RectBox(18, 26, 76, 28)
        self.btn_guide = RectBox(18, 62, 76, 28)
        self.btn_skip_wave = RectBox(SCREEN_WIDTH - 102, 108, 88, 28)
        self.btn_sell = RectBox(SCREEN_WIDTH * 0.5 - 86, SCREEN_HEIGHT * 0.52, 172, 34)

        self.difficulty_rects = [RectBox(44 + i * 156, 360, 140, 48) for i in range(3)]
        self.btn_start_game = RectBox(110, 445, 320, 64)
        self.btn_title_guide = RectBox(150, 530, 240, 46)

        self.btn_close_guide = RectBox(SCREEN_WIDTH * 0.5 - 105, SCREEN_HEIGHT - 82, 210, 46)

        self.dock_rects: List[RectBox] = []
        slot_w = SCREEN_WIDTH * 0.115
        slot_h = slot_w
        gap = SCREEN_WIDTH * 0.018
        total_w = DOCK_SLOTS_COUNT * slot_w + (DOCK_SLOTS_COUNT - 1) * gap
        start_x = (SCREEN_WIDTH - total_w) / 2.0
        dock_center_y = SCREEN_HEIGHT * (1.0 - 0.095)
        for i in range(DOCK_SLOTS_COUNT):
            sx = start_x + i * (slot_w + gap)
            sy = dock_center_y - slot_h / 2.0
            self.dock_rects.append(RectBox(sx, sy, slot_w, slot_h))

        sbtn_y = SCREEN_HEIGHT - 44
        self.spawn_btns: List[Tuple[str, RectBox]] = [
            ("sniper", RectBox(10, sbtn_y, 76, 36)),
            ("gatling", RectBox(90, sbtn_y, 66, 36)),
            ("mortar", RectBox(160, sbtn_y, 88, 36)),
        ]
        self.btn_buy_healer = RectBox(252, sbtn_y, 86, 36)
        self.points_box = RectBox(342, sbtn_y, 188, 36)

        self._active_touch_uid: Optional[int] = None
        self.reset_game()
        Window.bind(size=self._on_window_resize)
        Clock.schedule_interval(self.step, 1.0 / FPS)

    def _on_window_resize(self, instance, value):
        self.size = value

    def _apply_difficulty_regen(self):
        global POINTS_REGEN_PER_SEC
        cfg = get_difficulty_cfg()
        POINTS_REGEN_PER_SEC = float(cfg["points_regen"])

    def _sync_best_stats(self):
        updated = False
        if self.score > self.best_score:
            self.best_score = self.score
            updated = True
        if self.wave > self.best_wave:
            self.best_wave = self.wave
            updated = True
        if updated:
            save_best_stats(self.best_score, self.best_wave)

    def reset_game(self):
        self._apply_difficulty_regen()
        self.base_hp = BASE_MAX_HP
        self.base_max_hp = BASE_MAX_HP
        self.points = STARTING_POINTS
        self.score = 0
        self.wave = 1

        self.dock_units: List[Optional[DefenseUnit]] = [None] * DOCK_SLOTS_COUNT
        self.pad_units: List[Optional[DefenseUnit]] = [None] * DEFENSE_SLOTS_COUNT
        self.healer: Optional[HealerUnit] = None

        self.enemies: List[TankEnemy] = []
        self.projectiles: List[LaneProjectile] = []
        self.boss_shells: List[BossShellFX] = []
        self.particles: List[Particle] = []
        self.shockwaves: List[Shockwave] = []
        self.impact_flashes: List[ImpactFlash] = []
        self.heal_arcs: List[HealArcFX] = []
        self.popups: List[FloatingPopup] = []
        self.wave_alerts: List[WaveWarningAlert] = []

        self.wave_queue: List[Tuple[str, float]] = []
        self.next_wave_list: List[str] = build_wave_sequence(2)
        self.spawn_timer = 1.2

        self.dragging_unit: Optional[DefenseUnit] = None
        self.drag_origin: Optional[Tuple[str, int]] = None
        self.drag_pos: Tuple[float, float] = (0.0, 0.0)
        self.selected_pad: Optional[int] = None
        self.screen_shake = 0.0
        self.elapsed = 0.0

        self.prepare_wave(1)

    def _trigger_special_wave_alerts(self, seq: List[str], wave_num: int):
        if "boss" in seq or is_big_boss_wave(wave_num):
            shell_dmg = int(get_boss_shell_damage(wave_num))
            self.wave_alerts.append(
                WaveWarningAlert(
                    kind="boss",
                    title="BOSS INCOMING!",
                    subtitle=f"HEAVY SHELL {shell_dmg} DMG / 3s",
                    color=PURPLE,
                    life=3.2,
                    max_life=3.2,
                )
            )

    def prepare_wave(self, wave_num: int):
        seq = self.next_wave_list if self.next_wave_list else build_wave_sequence(wave_num)
        self.wave_queue = []
        for idx, t_type in enumerate(seq):
            lane_sign = -1.0 if idx % 2 == 0 else 1.0
            self.wave_queue.append((t_type, lane_sign))
        self.next_wave_list = build_wave_sequence(wave_num + 1)
        self.spawn_timer = 1.2
        self._trigger_special_wave_alerts(seq, wave_num)

    def skip_to_next_wave(self):
        self.wave += 1
        self._sync_best_stats()
        extra_seq = self.next_wave_list if self.next_wave_list else build_wave_sequence(self.wave)
        for idx, t_type in enumerate(extra_seq):
            lane_sign = -1.0 if idx % 2 == 0 else 1.0
            self.wave_queue.append((t_type, lane_sign))
        self.next_wave_list = build_wave_sequence(self.wave + 1)
        self.spawn_timer = min(self.spawn_timer, 0.25)
        self.points = min(MAX_POINTS, self.points + 1.5)
        self.audio.play("spawn")
        self._trigger_special_wave_alerts(extra_seq, self.wave)
        self.add_popup(SCREEN_WIDTH * 0.5, 195, f"SKIP > W{self.wave} (+1.5 PTS)", YELLOW)

    def emit_burst(self, x: float, y: float, color: Tuple[float, float, float, float], count: int = 12, speed: float = 135.0):
        for _ in range(count):
            ang = random.uniform(0, math.tau)
            spd = random.uniform(speed * 0.25, speed)
            life = random.uniform(0.22, 0.48)
            self.particles.append(
                Particle(
                    x=x,
                    y=y,
                    vx=math.cos(ang) * spd,
                    vy=math.sin(ang) * spd,
                    color=color,
                    size=random.uniform(2.5, 5.0),
                    life=life,
                    max_life=life,
                )
            )

    def _add_impact_flash(
        self,
        x: float,
        y: float,
        vx: float,
        vy: float,
        color: Tuple[float, float, float, float],
        length: float = 15.0,
        width: float = 2.6,
    ):
        nx, ny = norm(vx, vy)
        if nx == 0.0 and ny == 0.0:
            nx, ny = 1.0, 0.0
        self.impact_flashes.append(
            ImpactFlash(x=x, y=y, dx=nx, dy=ny, color=color, length=length, width=width)
        )
        for _ in range(4):
            spread = random.uniform(-0.85, 0.85)
            cos_s, sin_s = math.cos(spread), math.sin(spread)
            sdx = nx * cos_s - ny * sin_s
            sdy = nx * sin_s + ny * cos_s
            spd = random.uniform(90.0, 175.0)
            life = random.uniform(0.14, 0.26)
            self.particles.append(
                Particle(x, y, sdx * spd, sdy * spd, color, random.uniform(2.2, 4.2), life, life)
            )

    def emit_upgrade_effects(self, x: float, y: float, new_tier: int, color: Tuple[float, float, float, float]):
        is_max = (new_tier >= MAX_TURRET_TIER)
        aura_col = GOLD if is_max else color
        ring_rad = 84.0 if is_max else 54.0
        p_count = 28 if is_max else 16
        p_speed = 195.0 if is_max else 140.0

        self.audio.play("merge")
        self.shockwaves.append(
            Shockwave(
                x, y, ring_rad, aura_col,
                width=3.8 if is_max else 2.4,
                life=0.45 if is_max else 0.32,
                max_life=0.45 if is_max else 0.32,
            )
        )
        if is_max:
            self.shockwaves.append(Shockwave(x, y, ring_rad * 0.65, WHITE, width=2.2, life=0.35, max_life=0.35))
            self.screen_shake = max(self.screen_shake, 4.5)
        self.emit_burst(x, y, aura_col, count=p_count, speed=p_speed)
        label = f"MAX L{new_tier}!" if is_max else f"MERGED L{new_tier}!"
        self.add_popup(x, y - 18, label, aura_col)

    def add_popup(self, x: float, y: float, text: str, color: Tuple[float, float, float, float]):
        self.popups.append(FloatingPopup(x=x, y=y, text=text, color=color))

    def spawn_unit_to_dock(self, unit_type: str):
        cost = int(UNIT_META[unit_type]["cost"])
        if self.points < cost:
            self.add_popup(SCREEN_WIDTH * 0.5, SCREEN_HEIGHT - 72, "NOT ENOUGH PTS!", RED)
            return
        empty_idx = next((i for i, u in enumerate(self.dock_units) if u is None), None)
        if empty_idx is None:
            self.add_popup(SCREEN_WIDTH * 0.5, SCREEN_HEIGHT - 72, "STORAGE FULL!", ORANGE)
            return
        self.points -= cost
        self.dock_units[empty_idx] = DefenseUnit(unit_type=unit_type, tier=1)
        self.audio.play("spawn")
        r = self.dock_rects[empty_idx]
        self.emit_burst(r.centerx, r.centery, UNIT_META[unit_type]["color"], count=10, speed=95.0)  # type: ignore

    def build_or_upgrade_healer(self):
        hx, hy = HEALER_PAD
        if self.healer is None:
            if self.points < HEALER_BUILD_COST:
                self.add_popup(hx, hy - 22, "NEED 10 PTS!", RED)
                return
            self.points -= HEALER_BUILD_COST
            self.healer = HealerUnit(level=1)
            self.audio.play("spawn")
            self.shockwaves.append(Shockwave(hx, hy, 54.0, TEAL))
            self.emit_burst(hx, hy, TEAL, count=14, speed=120.0)
            self.add_popup(hx, hy - 22, "HEALER BUILT L1!", TEAL)
            return

        upg_cost = self.healer.next_upgrade_cost()
        if upg_cost is None:
            self.add_popup(hx, hy - 22, "MAX L5!", YELLOW)
            return
        if self.points < upg_cost:
            self.add_popup(hx, hy - 22, f"NEED {upg_cost} PTS!", RED)
            return

        self.points -= upg_cost
        self.healer.level += 1
        self.audio.play("merge")
        self.shockwaves.append(Shockwave(hx, hy, 62.0, TEAL))
        self.emit_burst(hx, hy, TEAL, count=18, speed=145.0)
        self.add_popup(hx, hy - 22, f"HEALER L{self.healer.level}!", GREEN)

    def try_begin_drag(self, px: float, py: float) -> bool:
        if dist(px, py, HEALER_PAD[0], HEALER_PAD[1]) <= 28.0:
            self.build_or_upgrade_healer()
            return False

        for i, (cx, cy) in enumerate(TOWER_PADS):
            if dist(px, py, cx, cy) <= 28.0:
                self.selected_pad = i
                if self.pad_units[i] is not None:
                    self.dragging_unit = self.pad_units[i]
                    self.pad_units[i] = None
                    self.drag_origin = ("pad", i)
                    self.drag_pos = (px, py)
                    return True
                return False

        for i, rect in enumerate(self.dock_rects):
            if rect.collidepoint(px, py):
                if self.dock_units[i] is not None:
                    self.dragging_unit = self.dock_units[i]
                    self.dock_units[i] = None
                    self.drag_origin = ("dock", i)
                    self.drag_pos = (px, py)
                    return True
                return False

        self.selected_pad = None
        return False

    def restore_drag_to_origin(self):
        if self.dragging_unit is None or self.drag_origin is None:
            return
        kind, idx = self.drag_origin
        if kind == "pad":
            self.pad_units[idx] = self.dragging_unit
        else:
            self.dock_units[idx] = self.dragging_unit
        self.dragging_unit = None
        self.drag_origin = None

    def sell_dragging_unit(self):
        if self.dragging_unit is None:
            return
        refund = self.dragging_unit.get_refund_points()
        self.points = min(MAX_POINTS, self.points + refund)
        self.audio.play("spawn")
        self.emit_burst(self.btn_sell.centerx, self.btn_sell.centery, GREEN, count=12, speed=110.0)
        self.add_popup(self.btn_sell.centerx, self.btn_sell.centery - 18, f"SOLD +{refund:.0f} PTS", GREEN)
        self.dragging_unit = None
        self.drag_origin = None

    def finish_drag(self, px: float, py: float):
        if self.dragging_unit is None or self.drag_origin is None:
            return
        if self.btn_sell.collidepoint(px, py):
            self.sell_dragging_unit()
            return

        unit = self.dragging_unit
        origin_kind, origin_idx = self.drag_origin

        def place_into(target_list: List[Optional[DefenseUnit]], target_idx: int, drop_pos: Tuple[float, float]):
            existing = target_list[target_idx]
            if existing is None:
                target_list[target_idx] = unit
            elif (
                existing.unit_type == unit.unit_type
                and existing.tier == unit.tier
                and existing.tier < MAX_TURRET_TIER
            ):
                if existing.upgrade_to_next_tier():
                    self.emit_upgrade_effects(drop_pos[0], drop_pos[1], existing.tier, existing.color)
            else:
                target_list[target_idx] = unit
                if origin_kind == "pad":
                    self.pad_units[origin_idx] = existing
                else:
                    self.dock_units[origin_idx] = existing

        for i, (cx, cy) in enumerate(TOWER_PADS):
            if dist(px, py, cx, cy) <= 32.0:
                place_into(self.pad_units, i, (cx, cy))
                self.selected_pad = i
                self.dragging_unit = None
                self.drag_origin = None
                return

        for i, rect in enumerate(self.dock_rects):
            if rect.collidepoint(px, py):
                place_into(self.dock_units, i, (rect.centerx, rect.centery))
                self.dragging_unit = None
                self.drag_origin = None
                return

        self.restore_drag_to_origin()

    def _screen_to_logical(self, sx: float, sy: float) -> Tuple[float, float]:
        w = max(1.0, float(self.width))
        h = max(1.0, float(self.height))
        lx = (sx - self.x) * (SCREEN_WIDTH / w)
        ly = SCREEN_HEIGHT - ((sy - self.y) * (SCREEN_HEIGHT / h))
        return lx, ly

    def on_touch_down(self, touch):
        if self._active_touch_uid is not None:
            return True
        self._active_touch_uid = touch.uid
        px, py = self._screen_to_logical(touch.x, touch.y)

        if self.state == "GUIDE":
            if self.btn_close_guide.collidepoint(px, py):
                self.state = self._state_before_guide
            return True

        if self.state == "TITLE":
            for idx, rect in enumerate(self.difficulty_rects):
                if rect.collidepoint(px, py):
                    global CURRENT_DIFFICULTY
                    CURRENT_DIFFICULTY = DIFFICULTY_ORDER[idx]
                    self._apply_difficulty_regen()
                    return True
            if self.btn_title_guide.collidepoint(px, py):
                self._state_before_guide = "TITLE"
                self.info_texture = load_texture_by_candidates(["info.png"])
                self.state = "GUIDE"
                return True
            if self.btn_start_game.collidepoint(px, py):
                self.reset_game()
                self.state = "PLAYING"
                return True
            return True

        if self.state == "GAMEOVER":
            self.reset_game()
            self.state = "PLAYING"
            return True

        if self.btn_guide.collidepoint(px, py):
            self._state_before_guide = self.state
            self.info_texture = load_texture_by_candidates(["info.png"])
            self.state = "GUIDE"
            return True

        if self.btn_pause.collidepoint(px, py):
            self.state = "PAUSED" if self.state == "PLAYING" else "PLAYING"
            return True

        if self.state == "PAUSED":
            self.state = "PLAYING"
            return True

        if self.btn_skip_wave.collidepoint(px, py):
            self.skip_to_next_wave()
            return True

        if self.btn_buy_healer.collidepoint(px, py):
            self.build_or_upgrade_healer()
            return True

        for unit_type, rect in self.spawn_btns:
            if rect.collidepoint(px, py):
                self.spawn_unit_to_dock(unit_type)
                return True

        self.try_begin_drag(px, py)
        return True

    def on_touch_move(self, touch):
        if touch.uid != self._active_touch_uid:
            return False
        if self.state == "PLAYING" and self.dragging_unit is not None:
            self.drag_pos = self._screen_to_logical(touch.x, touch.y)
        return True

    def on_touch_up(self, touch):
        if touch.uid != self._active_touch_uid:
            return False
        self._active_touch_uid = None
        if self.state == "PLAYING" and self.dragging_unit is not None:
            px, py = self._screen_to_logical(touch.x, touch.y)
            self.finish_drag(px, py)
        return True

    def step(self, dt: float):
        dt = min(dt, 0.05)
        self.elapsed += dt
        if self.screen_shake > 0:
            self.screen_shake = max(0.0, self.screen_shake - dt * 28.0)

        if self.state == "PLAYING":
            if self.points < MAX_POINTS:
                self.points = min(MAX_POINTS, self.points + POINTS_REGEN_PER_SEC * dt)

            if self.wave_queue:
                self.spawn_timer -= dt
                if self.spawn_timer <= 0:
                    t_type, lane_sign = self.wave_queue.pop(0)
                    self.enemies.append(TankEnemy.create(t_type, self.wave, lane_sign))
                    self.spawn_timer = 1.65
            elif not self.enemies:
                self.wave += 1
                self._sync_best_stats()
                self.prepare_wave(self.wave)

            surviving: List[TankEnemy] = []
            for e in self.enemies:
                reached = e.update(dt)
                if reached:
                    self.base_hp = max(0, self.base_hp - 1)
                    self.screen_shake = 7.0
                    self.audio.play("base_hit")
                    self.shockwaves.append(Shockwave(e.x, e.y, 60.0, RED))
                    self.emit_burst(e.x, e.y, RED, count=14, speed=140.0)
                    self.add_popup(e.x, e.y - 14, "-1 BASE HP", RED)
                    if self.base_hp <= 0:
                        self._sync_best_stats()
                        self.state = "GAMEOVER"
                else:
                    surviving.append(e)
            self.enemies = surviving

            # Boss fires heavy shells at active defense pads every 3.0 seconds
            boss_dmg = get_boss_shell_damage(self.wave)
            for e in self.enemies:
                if e.kind == "boss" and e.hp > 0 and e.boss_attack_cd <= 0.0:
                    active_pads = [(idx, u) for idx, u in enumerate(self.pad_units) if u is not None and u.hp > 0]
                    if active_pads:
                        target_idx, _ = min(active_pads, key=lambda pair: dist(e.x, e.y, *TOWER_PADS[pair[0]]))
                        tx, ty = TOWER_PADS[target_idx]
                        e.boss_attack_cd = BOSS_ATTACK_INTERVAL_SEC
                        self.audio.play("boss_shell")
                        self.shockwaves.append(Shockwave(e.x, e.y, 34.0, RED, width=2.4, life=0.22, max_life=0.22))
                        self.boss_shells.append(
                            BossShellFX(
                                x=e.x,
                                y=e.y,
                                target_x=tx,
                                target_y=ty,
                                pad_idx=target_idx,
                                damage=boss_dmg,
                                speed=410.0,
                            )
                        )

            # Resolve heavy boss shells impacting defense turrets
            remaining_shells: List[BossShellFX] = []
            for sh in self.boss_shells:
                hit_pad = sh.update(dt)
                if not hit_pad:
                    remaining_shells.append(sh)
                    continue

                self.screen_shake = max(self.screen_shake, 13.5)
                self.audio.play("mortar")
                self.shockwaves.append(Shockwave(sh.target_x, sh.target_y, 58.0, RED, width=3.6, life=0.34, max_life=0.34))
                self.shockwaves.append(Shockwave(sh.target_x, sh.target_y, 34.0, ORANGE, width=2.5, life=0.24, max_life=0.24))
                self._add_impact_flash(sh.target_x, sh.target_y, sh.target_x - sh.x, sh.target_y - sh.y, RED, length=24.0, width=4.0)
                self.emit_burst(sh.target_x, sh.target_y, RED, count=18, speed=180.0)
                self.emit_burst(sh.target_x, sh.target_y, YELLOW, count=10, speed=140.0)

                target_unit = self.pad_units[sh.pad_idx]
                if target_unit is not None and target_unit.hp > 0:
                    target_unit.hp -= sh.damage
                    self.add_popup(sh.target_x, sh.target_y - 20, f"-{int(sh.damage)} SHELL!", RED)
                    if target_unit.hp <= 0:
                        self.pad_units[sh.pad_idx] = None
                        self.screen_shake = max(self.screen_shake, 16.0)
                        self.shockwaves.append(Shockwave(sh.target_x, sh.target_y, 72.0, RED, width=4.0, life=0.42, max_life=0.42))
                        self.add_popup(sh.target_x, sh.target_y - 34, "TURRET DESTROYED!", RED)
            self.boss_shells = remaining_shells

            # Healer heals ONE damaged turret every 3.0 seconds across the full map
            if self.healer is not None:
                self.healer.heal_cd = max(0.0, self.healer.heal_cd - dt)
                if self.healer.heal_cd <= 0.0:
                    damaged_pads = [
                        (idx, u) for idx, u in enumerate(self.pad_units)
                        if u is not None and 0 < u.hp < u.max_hp
                    ]
                    if damaged_pads:
                        target_idx, target_unit = min(damaged_pads, key=lambda item: item[1].hp / max(1.0, item[1].max_hp))
                        target_unit.hp = min(target_unit.max_hp, target_unit.hp + self.healer.heal_amount)
                        self.healer.heal_cd = HEALER_INTERVAL_SEC
                        hx, hy = HEALER_PAD
                        px, py = TOWER_PADS[target_idx]
                        self.audio.play("heal")
                        self.heal_arcs.append(HealArcFX(hx, hy, px, py, GREEN, width=2.8, life=0.22, max_life=0.22))
                        self.emit_burst(px, py, GREEN, count=10, speed=95.0)
                        self.add_popup(px, py - 24, f"+{int(self.healer.heal_amount)} HP", GREEN)

            for i, unit in enumerate(self.pad_units):
                if unit is not None and unit.hp > 0:
                    unit.update_and_fire(dt, TOWER_PADS[i], self.enemies, self.projectiles, self.audio)

            active_projs: List[LaneProjectile] = []
            for p in self.projectiles:
                if not p.update(dt):
                    continue
                hit_enemy: Optional[TankEnemy] = None
                for e in self.enemies:
                    if e.hp > 0 and dist(p.x, p.y, e.x, e.y) <= (p.radius + e.radius):
                        hit_enemy = e
                        break

                if hit_enemy is not None:
                    self._add_impact_flash(
                        p.x,
                        p.y,
                        p.vx,
                        p.vy,
                        p.color,
                        length=18.0 if p.splash_radius > 0 else 13.0,
                        width=3.2 if p.splash_radius > 0 else 2.3,
                    )
                    if p.splash_radius > 0:
                        self.shockwaves.append(Shockwave(p.last_tx, p.last_ty, p.splash_radius, p.color))
                        self.emit_burst(p.last_tx, p.last_ty, p.color, count=14, speed=140.0)
                        for e in self.enemies:
                            if e.hp > 0 and dist(e.x, e.y, p.last_tx, p.last_ty) <= p.splash_radius:
                                if p.slow_pct > 0.0 and p.slow_duration > 0.0:
                                    e.apply_slow(p.slow_pct, p.slow_duration)
                                self._damage_enemy(e, p.damage)
                    else:
                        if p.slow_pct > 0.0 and p.slow_duration > 0.0:
                            hit_enemy.apply_slow(p.slow_pct, p.slow_duration)
                        self.emit_burst(p.x, p.y, p.color, count=6, speed=85.0)
                        self._damage_enemy(hit_enemy, p.damage)
                else:
                    active_projs.append(p)
            self.projectiles = active_projs
            self.enemies = [e for e in self.enemies if e.hp > 0]

        self.particles = [pt for pt in self.particles if pt.update(dt)]
        self.shockwaves = [sw for sw in self.shockwaves if sw.update(dt)]
        self.impact_flashes = [fl for fl in self.impact_flashes if fl.update(dt)]
        self.heal_arcs = [arc for arc in self.heal_arcs if arc.update(dt)]
        self.popups = [pp for pp in self.popups if pp.update(dt)]
        self.wave_alerts = [al for al in self.wave_alerts if al.update(dt)]

        self.render()

    def _damage_enemy(self, enemy: TankEnemy, dmg: float):
        enemy.hp -= dmg
        enemy.hit_flash = 0.08
        if enemy.hp <= 0:
            self.score += enemy.score_reward
            self._sync_best_stats()
            self.audio.play("enemy_die")
            self.shockwaves.append(Shockwave(enemy.x, enemy.y, enemy.radius * 2.0, enemy.color))
            self.emit_burst(enemy.x, enemy.y, enemy.color, count=14, speed=145.0)
            self.add_popup(enemy.x, enemy.y - 12, f"+{enemy.score_reward}", YELLOW)
        else:
            self.audio.play("enemy_hit")

    # --------------------------------------------------------------------------
    # Drawing Helpers
    # --------------------------------------------------------------------------
    def _draw_rect(self, x: float, y: float, w: float, h: float, color: Tuple[float, float, float, float]):
        Color(*color)
        Rectangle(pos=(x, to_ky(y + h)), size=(w, h))

    def _draw_rect_outline(self, x: float, y: float, w: float, h: float, color: Tuple[float, float, float, float], width: float = 1.5):
        Color(*color)
        Line(rectangle=(x, to_ky(y + h), w, h), width=width)

    def _draw_circle(self, cx: float, cy: float, r: float, color: Tuple[float, float, float, float]):
        Color(*color)
        Ellipse(pos=(cx - r, to_ky(cy) - r), size=(r * 2.0, r * 2.0))

    def _draw_circle_outline(self, cx: float, cy: float, r: float, color: Tuple[float, float, float, float], width: float = 1.5):
        Color(*color)
        Line(circle=(cx, to_ky(cy), r), width=width)

    def _draw_line(self, x1: float, y1: float, x2: float, y2: float, color: Tuple[float, float, float, float], width: float = 2.0):
        Color(*color)
        Line(points=[x1, to_ky(y1), x2, to_ky(y2)], width=width)

    def _draw_oriented_rect(self, cx: float, cy: float, length: float, thickness: float, angle_rad: float, color: Tuple[float, float, float, float]):
        Color(*color)
        PushMatrix()
        Translate(cx, to_ky(cy), 0)
        Rotate(angle=-math.degrees(angle_rad), axis=(0, 0, 1))
        Rectangle(pos=(-length * 0.5, -thickness * 0.5), size=(length, thickness))
        PopMatrix()

    def _draw_projectile_visual(self, p: LaneProjectile):
        ang = math.atan2(p.vy, p.vx)
        glow_mult = 1.0 + (p.tier - 1) * 0.45
        pulse = 1.0 + 0.12 * math.sin(self.elapsed * 22.0)
        glow_alpha = clamp((0.16 + (p.tier - 1) * 0.10) * pulse, 0.12, 0.55)
        aura_col = GOLD if p.tier >= MAX_TURRET_TIER else p.color

        self._draw_oriented_rect(
            p.x,
            p.y,
            p.length + (p.tier * 2.5) * glow_mult,
            p.thickness * (1.45 + (p.tier - 1) * 0.35),
            ang,
            (aura_col[0], aura_col[1], aura_col[2], glow_alpha),
        )
        self._draw_oriented_rect(p.x, p.y, p.length, p.thickness, ang, p.color)
        self._draw_oriented_rect(p.x, p.y, p.length * 0.55, p.thickness * 0.45, ang, WHITE)

    def _draw_boss_shell_visual(self, sh: BossShellFX):
        ang = math.atan2(sh.target_y - sh.y, sh.target_x - sh.x)
        self._draw_oriented_rect(sh.x, sh.y, 26.0, 13.0, ang, (1.0, 0.35, 0.10, 0.38))
        self._draw_oriented_rect(sh.x, sh.y, 19.0, 8.5, ang, RED)
        self._draw_oriented_rect(sh.x, sh.y, 11.0, 4.5, ang, YELLOW)
        self._draw_circle(sh.x, sh.y, 5.5, WHITE)

    def _draw_texture(
        self,
        texture,
        cx: float,
        cy: float,
        w: float,
        h: float,
        angle_deg: float = 0.0,
        tint: Tuple[float, float, float, float] = WHITE,
        pivot_offset_x: float = 0.0,
    ):
        Color(*tint)
        PushMatrix()
        Translate(cx, to_ky(cy), 0)
        if angle_deg != 0.0:
            Rotate(angle=angle_deg, axis=(0, 0, 1))
        Rectangle(texture=texture, pos=(-w * 0.5 + pivot_offset_x, -h * 0.5), size=(w, h))
        PopMatrix()

    def _draw_text(self, text: str, cx: float, cy: float, color: Tuple[float, float, float, float], font_size: int = 15, bold: bool = True, align: str = "center"):
        key = (text, font_size, bold)
        cached = self._text_cache.get(key)
        if cached is None:
            lbl = CoreLabel(text=text, font_size=font_size, bold=bold)
            lbl.refresh()
            cached = (lbl.texture, lbl.texture.size[0], lbl.texture.size[1])
            if len(self._text_cache) > 400:
                self._text_cache.clear()
            self._text_cache[key] = cached

        tex, tw, th = cached
        Color(*color)
        if align == "center":
            dx = cx - tw * 0.5
        elif align == "left":
            dx = cx
        else:
            dx = cx - tw
        Rectangle(texture=tex, pos=(dx, to_ky(cy) - th * 0.5), size=(tw, th))

    def _draw_turret_visual(self, unit: DefenseUnit, cx: float, cy: float, radius: float, show_range: bool = False, show_hp: bool = True):
        if show_range:
            rng = unit.get_range()
            self._draw_circle(cx, cy, rng, (1, 1, 1, 0.14))
            self._draw_circle_outline(cx, cy, rng, (1, 1, 1, 0.45), 1.2)

        is_max = (unit.tier >= MAX_TURRET_TIER)
        pulse = 1.0 + 0.10 * math.sin(self.elapsed * (10.0 if is_max else 5.0))
        aura_col = GOLD if is_max else unit.color
        if unit.tier >= 2:
            aura_rad = radius * (1.15 + (unit.tier - 2) * 0.18) * pulse
            aura_a = (0.14 + (unit.tier - 2) * 0.10) * (1.15 if is_max else 1.0)
            self._draw_circle(cx, cy, aura_rad, (aura_col[0], aura_col[1], aura_col[2], clamp(aura_a, 0.1, 0.52)))
        if is_max:
            self._draw_circle_outline(cx, cy, radius * 1.38 * pulse, (1.0, 0.85, 0.25, 0.78), 2.2)

        rx = cx - math.cos(unit.aim_angle) * unit.recoil_px
        ry = cy - math.sin(unit.aim_angle) * unit.recoil_px

        tex = self.turret_textures.get((unit.unit_type, unit.tier))
        if tex is not None:
            sprite_size = radius * 2.55
            if unit.unit_type == "sniper":
                barrel_forward_shift = radius * 0.54
                angle_trim_deg = 6.0
            else:
                barrel_forward_shift = radius * 0.34
                angle_trim_deg = 0.0

            self._draw_texture(
                tex,
                rx,
                ry,
                sprite_size,
                sprite_size,
                angle_deg=-(math.degrees(unit.aim_angle) + angle_trim_deg),
                tint=WHITE,
                pivot_offset_x=barrel_forward_shift,
            )
        else:
            col = unit.color
            if unit.unit_type == "sniper":
                self._draw_rect(rx - radius * 0.72, ry - radius * 0.72, radius * 1.44, radius * 1.44, col)
                self._draw_line(rx, ry, rx + math.cos(unit.aim_angle) * radius * 1.45, ry + math.sin(unit.aim_angle) * radius * 1.45, BLACK, 3.0)
            elif unit.unit_type == "gatling":
                self._draw_circle(rx, ry, radius * 0.78, col)
                px = -math.sin(unit.aim_angle) * 3.0
                py = math.cos(unit.aim_angle) * 3.0
                bx = math.cos(unit.aim_angle) * radius * 1.30
                by = math.sin(unit.aim_angle) * radius * 1.30
                self._draw_line(rx + px, ry + py, rx + px + bx, ry + py + by, BLACK, 2.2)
                self._draw_line(rx - px, ry - py, rx - px + bx, ry - py + by, BLACK, 2.2)
            else:
                self._draw_rect(rx - radius * 0.78, ry - radius * 0.78, radius * 1.56, radius * 1.56, col)
                self._draw_line(rx, ry, rx + math.cos(unit.aim_angle) * radius * 1.35, ry + math.sin(unit.aim_angle) * radius * 1.35, BLACK, 5.0)

        self._draw_circle(cx + radius * 0.65, cy + radius * 0.65, 9.0, BLACK)
        self._draw_text(f"L{unit.tier}", cx + radius * 0.65, cy + radius * 0.65, GOLD if is_max else YELLOW, 10)

        if show_hp:
            bw = radius * 1.9
            bh = 4.0
            ratio = clamp(unit.hp / max(1.0, unit.max_hp), 0.0, 1.0)
            self._draw_rect(cx - bw * 0.5, cy + radius + 4.0, bw, bh, BLACK)
            self._draw_rect(cx - bw * 0.5, cy + radius + 4.0, bw * ratio, bh, GREEN if ratio > 0.45 else (YELLOW if ratio > 0.22 else RED))

    def _draw_healer_visual(self):
        hx, hy = HEALER_PAD
        r = 21.0
        self._draw_circle(hx, hy, r, (10, 34, 30, 0.78))
        self._draw_circle_outline(hx, hy, r, TEAL, 2.0)

        if self.healer is not None:
            self._draw_rect(hx - 3.0, hy - 10.0, 6.0, 20.0, GREEN)
            self._draw_rect(hx - 10.0, hy - 3.0, 20.0, 6.0, GREEN)
            self._draw_circle(hx + r * 0.65, hy + r * 0.65, 9.0, BLACK)
            self._draw_text(f"L{self.healer.level}", hx + r * 0.65, hy + r * 0.65, TEAL, 10)
            upg_cost = self.healer.next_upgrade_cost()
            label = f"HEAL L{self.healer.level} ({upg_cost})" if upg_cost else f"HEAL L{self.healer.level} MAX"
            self._draw_text(label, hx, hy + r + 11.0, WHITE, 10)
        else:
            self._draw_text("HEAL (10)", hx, hy, TEAL, 10)

    def _draw_tank_visual(self, e: TankEnemy):
        tex = self.tank_textures.get(e.kind)
        r = e.radius
        sp_size = r * e.sprite_mult
        tint = WHITE if e.hit_flash > 0 else (1.0, 1.0, 1.0, 1.0)
        if tex is not None:
            self._draw_texture(tex, e.x, e.y, sp_size, sp_size, angle_deg=-e.facing_angle, tint=tint)
        else:
            col = WHITE if e.hit_flash > 0 else e.color
            self._draw_circle(e.x + 1.5, e.y + 2.0, r * 1.02, (0, 0, 0, 0.30))
            self._draw_rect(e.x - r, e.y - r * 0.78, r * 2.0, r * 1.56, col)
            self._draw_rect_outline(e.x - r, e.y - r * 0.78, r * 2.0, r * 1.56, BLACK, 1.1)
            self._draw_circle(e.x, e.y, r * 0.50, (e.color[0] * 0.75, e.color[1] * 0.75, e.color[2] * 0.75, 1.0))
            rad = math.radians(e.facing_angle)
            self._draw_line(e.x, e.y, e.x + math.cos(rad) * r * 1.3, e.y + math.sin(rad) * r * 1.3, BLACK, 3.0)

        if e.slow_timer > 0.0:
            self._draw_circle_outline(e.x, e.y, r + 3.5, CYAN, 1.8)

        bw = max(22.0, r * 2.1)
        bh = 4.0
        ratio = clamp(e.hp / max(1.0, e.max_hp), 0.0, 1.0)
        self._draw_rect(e.x - bw * 0.5, e.y - r - 8.0, bw, bh, BLACK)
        self._draw_rect(e.x - bw * 0.5, e.y - r - 8.0, bw * ratio, bh, PURPLE if e.kind == "boss" else (GREEN if ratio > 0.4 else RED))

    def _draw_mini_tank_icon(self, kind: str, cx: float, cy: float, r: float = 6.5):
        tex = self.tank_textures.get(kind)
        if tex is not None:
            self._draw_texture(tex, cx, cy, r * 2.1, r * 2.1)
        else:
            col = TANK_SPECS[kind]["color"]  # type: ignore
            self._draw_rect(cx - r, cy - r * 0.75, r * 2.0, r * 1.5, col)
            self._draw_rect_outline(cx - r, cy - r * 0.75, r * 2.0, r * 1.5, BLACK, 1.0)
            self._draw_line(cx, cy, cx + r * 1.25, cy, BLACK, 1.6)

    def _draw_wave_alerts(self):
        active_alerts = [al for al in self.wave_alerts if al.life <= al.max_life]
        if not active_alerts:
            return
        alert = active_alerts[0]
        fade_in = clamp((alert.max_life - alert.life) / 0.25, 0.0, 1.0)
        fade_out = clamp(alert.life / 0.45, 0.0, 1.0)
        alpha = min(fade_in, fade_out)
        pulse = 0.75 + 0.25 * math.sin(alert.life * 14.0)

        bx = 122.0
        by = 96.0
        bw = SCREEN_WIDTH - 234.0
        bh = 52.0

        self._draw_rect(bx, by, bw, bh, (0.06, 0.08, 0.14, 0.90 * alpha))
        self._draw_rect_outline(
            bx,
            by,
            bw,
            bh,
            (alert.color[0], alert.color[1], alert.color[2], (0.65 + 0.35 * pulse) * alpha),
            2.0,
        )

        icon_cx = bx + 26.0
        icon_cy = by + bh * 0.5
        self._draw_circle(icon_cx, icon_cy, 17.0, (alert.color[0], alert.color[1], alert.color[2], 0.22 * alpha))
        self._draw_mini_tank_icon(alert.kind, icon_cx, icon_cy, 11.5)

        self._draw_text(
            alert.title,
            bx + 52.0,
            by + 16.0,
            (alert.color[0], alert.color[1], alert.color[2], alpha),
            12,
            align="left",
        )
        self._draw_text(
            alert.subtitle,
            bx + 52.0,
            by + 35.0,
            (WHITE[0], WHITE[1], WHITE[2], alpha),
            10,
            align="left",
        )

    def render(self):
        self.canvas.clear()
        with self.canvas:
            PushMatrix()
            Scale(self.width / float(SCREEN_WIDTH), self.height / float(SCREEN_HEIGHT), 1.0)
            if self.screen_shake > 0:
                Translate(
                    random.uniform(-self.screen_shake, self.screen_shake),
                    random.uniform(-self.screen_shake, self.screen_shake),
                    0,
                )

            if self.map_texture is not None:
                Color(1, 1, 1, 1)
                Rectangle(texture=self.map_texture, pos=(0, 0), size=(SCREEN_WIDTH, SCREEN_HEIGHT))
            else:
                self._draw_rect(0, 0, SCREEN_WIDTH, SCREEN_HEIGHT, rgb(70, 132, 42))
                pts = []
                for lx, ly in LANE_POINTS:
                    pts.extend([lx, to_ky(ly)])
                Color(*rgb(192, 148, 92))
                Line(points=pts, width=34, cap="round", joint="round")

            for i, (px, py) in enumerate(TOWER_PADS):
                self._draw_circle(px, py, 22.0, (18, 26, 18, 0.62))
                self._draw_circle_outline(px, py, 22.0, (0.85, 0.92, 0.75, 0.80), 1.6)
                unit = self.pad_units[i]
                if unit is not None:
                    self._draw_turret_visual(unit, px, py, 19.5, show_range=(self.selected_pad == i), show_hp=True)

            self._draw_healer_visual()

            for e in self.enemies:
                self._draw_tank_visual(e)

            for arc in self.heal_arcs:
                alpha = clamp(arc.life / arc.max_life, 0.0, 1.0)
                self._draw_line(arc.x1, arc.y1, arc.x2, arc.y2, (arc.color[0], arc.color[1], arc.color[2], alpha), arc.width)

            for sh in self.boss_shells:
                self._draw_boss_shell_visual(sh)

            for p in self.projectiles:
                self._draw_projectile_visual(p)

            for fl in self.impact_flashes:
                alpha = clamp(fl.life / max(0.01, fl.max_life), 0.0, 1.0)
                hx_d = fl.dx * fl.length * 0.5
                hy_d = fl.dy * fl.length * 0.5
                self._draw_line(fl.x - hx_d, fl.y - hy_d, fl.x + hx_d, fl.y + hy_d, (fl.color[0], fl.color[1], fl.color[2], alpha), fl.width)
                self._draw_line(fl.x - hx_d, fl.y - hy_d, fl.x + hx_d, fl.y + hy_d, (1.0, 1.0, 1.0, alpha * 0.9), max(1.0, fl.width * 0.45))

            for sw in self.shockwaves:
                prog = 1.0 - (sw.life / max(0.01, sw.max_life))
                self._draw_circle_outline(
                    sw.x, sw.y, max(4.0, sw.max_radius * prog), (sw.color[0], sw.color[1], sw.color[2], clamp(1.0 - prog, 0.0, 1.0)), sw.width
                )

            for pt in self.particles:
                alpha = clamp(pt.life / max(0.01, pt.max_life), 0.0, 1.0)
                self._draw_circle(pt.x, pt.y, pt.size * alpha, (pt.color[0], pt.color[1], pt.color[2], alpha))

            for i, rect in enumerate(self.dock_rects):
                self._draw_rect(rect.x, rect.y, rect.w, rect.h, SLOT_BG)
                self._draw_rect_outline(rect.x, rect.y, rect.w, rect.h, SLOT_BORDER, 1.4)
                unit = self.dock_units[i]
                if unit is not None:
                    self._draw_turret_visual(unit, rect.centerx, rect.centery, rect.w * 0.36, show_range=False, show_hp=False)

            # Top HUD buttons & centered stats inside the top white cloud
            self._draw_rect(self.btn_pause.x, self.btn_pause.y, self.btn_pause.w, self.btn_pause.h, rgb(52, 85, 130))
            self._draw_rect_outline(self.btn_pause.x, self.btn_pause.y, self.btn_pause.w, self.btn_pause.h, WHITE, 1.1)
            self._draw_text("RESUME" if self.state == "PAUSED" else "PAUSE", self.btn_pause.centerx, self.btn_pause.centery, WHITE, 11)

            self._draw_rect(self.btn_guide.x, self.btn_guide.y, self.btn_guide.w, self.btn_guide.h, rgb(55, 125, 78))
            self._draw_rect_outline(self.btn_guide.x, self.btn_guide.y, self.btn_guide.w, self.btn_guide.h, WHITE, 1.1)
            self._draw_text("GUIDE", self.btn_guide.centerx, self.btn_guide.centery, WHITE, 11)

            remaining = len(self.enemies) + len(self.wave_queue)
            self._draw_text(f"BASE: {self.base_hp}/{self.base_max_hp}", 224, 42, BLACK, 13)
            self._draw_text(f"SCORE: {self.score} | BEST: {self.best_score}", 412, 42, BLACK, 12)
            self._draw_text(f"W{self.wave} ({CURRENT_DIFFICULTY[0]}) | LEFT:{remaining}", 224, 74, BLACK, 12)

            self._draw_text("NEXT:", 324, 74, BLACK, 11)
            nx_cursor = 354.0
            for t_kind, t_cnt in summarize_wave_counts(self.next_wave_list):
                if nx_cursor + 32.0 > 522.0:
                    break
                self._draw_mini_tank_icon(t_kind, nx_cursor, 74, 6.2)
                self._draw_text(f"x{t_cnt}", nx_cursor + 14, 74, BLACK, 11)
                nx_cursor += 34.0

            self._draw_rect(self.btn_skip_wave.x, self.btn_skip_wave.y, self.btn_skip_wave.w, self.btn_skip_wave.h, SLOT_BG)
            self._draw_rect_outline(self.btn_skip_wave.x, self.btn_skip_wave.y, self.btn_skip_wave.w, self.btn_skip_wave.h, YELLOW, 1.4)
            self._draw_text(f"SKIP >W{self.wave + 1}", self.btn_skip_wave.centerx, self.btn_skip_wave.centery, YELLOW, 10)

            self._draw_wave_alerts()

            for unit_type, rect in self.spawn_btns:
                meta = UNIT_META[unit_type]
                cost = int(meta["cost"])
                self._draw_rect(rect.x, rect.y, rect.w, rect.h, meta["color"])  # type: ignore
                self._draw_rect_outline(rect.x, rect.y, rect.w, rect.h, WHITE, 1.2)
                self._draw_text(f"{meta['short']} ({cost})", rect.centerx, rect.centery, BLACK, 10)

            hb = self.btn_buy_healer
            if self.healer is None:
                h_label = f"HEAL ({HEALER_BUILD_COST})"
            else:
                uc = self.healer.next_upgrade_cost()
                h_label = f"H-UP ({uc})" if uc else "HEAL MAX"
            self._draw_rect(hb.x, hb.y, hb.w, hb.h, TEAL)
            self._draw_rect_outline(hb.x, hb.y, hb.w, hb.h, WHITE, 1.2)
            self._draw_text(h_label, hb.centerx, hb.centery, BLACK, 10)

            pb = self.points_box
            self._draw_rect(pb.x, pb.y, pb.w, pb.h, rgb(25, 65, 35))
            self._draw_rect_outline(pb.x, pb.y, pb.w, pb.h, GREEN, 1.3)
            self._draw_text(f"PTS: {self.points:.1f}/15 (+{BASE_POINTS_REGEN_PER_SEC:.2f}/s)", pb.centerx, pb.centery, WHITE, 11)

            if self.dragging_unit is not None:
                refund = self.dragging_unit.get_refund_points()
                self._draw_rect(self.btn_sell.x, self.btn_sell.y, self.btn_sell.w, self.btn_sell.h, SLOT_BG)
                self._draw_rect_outline(self.btn_sell.x, self.btn_sell.y, self.btn_sell.w, self.btn_sell.h, RED, 2.0)
                self._draw_text(f"SELL +{refund:.0f} PTS", self.btn_sell.centerx, self.btn_sell.centery, RED, 12)

                dx, dy = self.drag_pos
                self._draw_turret_visual(self.dragging_unit, dx, dy, 22.0, show_range=True, show_hp=False)

            for pp in self.popups:
                self._draw_text(pp.text, pp.x, pp.y, pp.color, 12)

            if self.state == "TITLE":
                self._draw_rect(0, 0, SCREEN_WIDTH, SCREEN_HEIGHT, (0, 0, 0, 0.74))
                self._draw_text("BASE DEFENSE", SCREEN_WIDTH * 0.5, 215, GREEN, 34)
                self._draw_text("5 TANKS (1->5)  |  L1-L4 MERGE  |  BOSS #5 (W15+)", SCREEN_WIDTH * 0.5, 258, WHITE, 12)
                self._draw_text(f"BEST SCORE: {self.best_score}   |   BEST WAVE: {self.best_wave}", SCREEN_WIDTH * 0.5, 302, YELLOW, 14)

                for idx, rect in enumerate(self.difficulty_rects):
                    diff_key = DIFFICULTY_ORDER[idx]
                    cfg = DIFFICULTY_CONFIGS[diff_key]
                    selected = (CURRENT_DIFFICULTY == diff_key)
                    self._draw_rect(rect.x, rect.y, rect.w, rect.h, cfg["color"] if selected else SLOT_BG)  # type: ignore
                    self._draw_rect_outline(rect.x, rect.y, rect.w, rect.h, WHITE if selected else GRAY, 1.8)
                    self._draw_text(str(cfg["label"]), rect.centerx, rect.centery, BLACK if selected else WHITE, 15)

                self._draw_rect(self.btn_start_game.x, self.btn_start_game.y, self.btn_start_game.w, self.btn_start_game.h, GREEN)
                self._draw_rect_outline(self.btn_start_game.x, self.btn_start_game.y, self.btn_start_game.w, self.btn_start_game.h, WHITE, 2.0)
                self._draw_text("START BATTLE", self.btn_start_game.centerx, self.btn_start_game.centery, BLACK, 22)

                self._draw_rect(self.btn_title_guide.x, self.btn_title_guide.y, self.btn_title_guide.w, self.btn_title_guide.h, SLOT_BG)
                self._draw_rect_outline(self.btn_title_guide.x, self.btn_title_guide.y, self.btn_title_guide.w, self.btn_title_guide.h, CYAN, 1.5)
                self._draw_text("HOW TO PLAY", self.btn_title_guide.centerx, self.btn_title_guide.centery, CYAN, 15)

            elif self.state == "PAUSED":
                self._draw_rect(0, 0, SCREEN_WIDTH, SCREEN_HEIGHT, (0, 0, 0, 0.60))
                self._draw_text("PAUSED", SCREEN_WIDTH * 0.5, SCREEN_HEIGHT * 0.45, YELLOW, 32)
                self._draw_text("TAP ANYWHERE TO RESUME", SCREEN_WIDTH * 0.5, SCREEN_HEIGHT * 0.51, WHITE, 15)

            elif self.state == "GAMEOVER":
                self._draw_rect(0, 0, SCREEN_WIDTH, SCREEN_HEIGHT, (0, 0, 0, 0.74))
                self._draw_text("GAME OVER", SCREEN_WIDTH * 0.5, SCREEN_HEIGHT * 0.37, RED, 32)
                self._draw_text(f"WAVE {self.wave}  |  DIFFICULTY: {CURRENT_DIFFICULTY}", SCREEN_WIDTH * 0.5, SCREEN_HEIGHT * 0.43, WHITE, 16)
                self._draw_text(f"SCORE: {self.score}  |  BEST: {self.best_score}", SCREEN_WIDTH * 0.5, SCREEN_HEIGHT * 0.49, YELLOW, 17)
                self._draw_text("TAP ANYWHERE TO PLAY AGAIN", SCREEN_WIDTH * 0.5, SCREEN_HEIGHT * 0.56, GREEN, 15)

            elif self.state == "GUIDE":
                self._draw_rect(0, 0, SCREEN_WIDTH, SCREEN_HEIGHT, (10, 16, 12, 0.96))
                if self.info_texture is not None:
                    img_w = SCREEN_WIDTH - 24
                    img_h = SCREEN_HEIGHT - 120
                    self._draw_texture(self.info_texture, SCREEN_WIDTH * 0.5, 20 + img_h * 0.5, img_w, img_h)
                else:
                    self._draw_text("PUT info.png IN assets/ FOLDER", SCREEN_WIDTH * 0.5, SCREEN_HEIGHT * 0.45, YELLOW, 16)

                self._draw_rect(self.btn_close_guide.x, self.btn_close_guide.y, self.btn_close_guide.w, self.btn_close_guide.h, GREEN)
                self._draw_rect_outline(self.btn_close_guide.x, self.btn_close_guide.y, self.btn_close_guide.w, self.btn_close_guide.h, WHITE, 1.5)
                self._draw_text("CLOSE", self.btn_close_guide.centerx, self.btn_close_guide.centery, BLACK, 16)

            PopMatrix()


class BaseDefenseApp(App):
    def build(self):
        self.title = TITLE
        if platform not in ("android", "ios"):
            Window.size = (SCREEN_WIDTH, SCREEN_HEIGHT)
        self.game_widget = BaseDefenseWidget()
        return self.game_widget

    def on_stop(self):
        if hasattr(self, "game_widget") and self.game_widget.audio:
            self.game_widget.audio.cleanup()


if __name__ == "__main__":
    try:
        BaseDefenseApp().run()
    except Exception:
        traceback.print_exc()
