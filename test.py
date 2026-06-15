"""
Telemetry CSV Viewer
====================
Upload a CSV, validate its structure, browse all records in a table,
and inspect any selected row in a detail panel.

Run:    python telemetry_viewer.py
Deps:   pandas  (pip install pandas)
"""

import os
import platform
import subprocess
import threading
import tkinter as tk
from tkinter import ttk, filedialog, messagebox, simpledialog

import pandas as pd
import tksheet

import matplotlib
matplotlib.use("TkAgg")
from matplotlib.figure import Figure
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg, NavigationToolbar2Tk


# ─── Theme — Light Engineering Dashboard ──────────────────────────────────────
# Edit only this block to retheme the entire application.

BG          = "#F4F6F8"   # App background (light grey)
PANEL       = "#FFFFFF"   # Card / panel background
BORDER      = "#D0D7DE"   # Dividers, input borders, subtle separators
TOPBAR_BG   = "#1E3A5F"   # Navy top bar (strong visual anchor)
TOPBAR_FG   = "#FFFFFF"   # Top bar text and icons
META_BG     = "#EBF0F7"   # Metadata strip — slightly tinted
ACCENT      = "#2563EB"   # Primary accent — buttons, headings, links
ACCENT_HOVER= "#1D4ED8"   # Primary accent hover state
ACCENT2     = "#7C3AED"   # Secondary accent — bit analysis, selection
ROW_ALT     = "#F0F4FA"   # Alternating table row (very light blue-grey)
SUCCESS     = "#16A34A"   # Success states and valid results
SUCCESS_BG  = "#DCFCE7"   # Success badge background
WARN        = "#D97706"   # Warnings, folder nodes
WARN_BG     = "#FEF3C7"   # Warning badge background
ERROR       = "#DC2626"   # Error states
ERROR_BG    = "#FEE2E2"   # Error badge background
TEXT        = "#111827"   # Primary text — near black
MUTED       = "#6B7280"   # Secondary / label text
MONO        = "Consolas"  # Monospace font for hex/binary data
SANS        = "Segoe UI"  # UI font

# Derived semantic aliases — keep usage sites readable
BTN_FG          = "#FFFFFF"   # Text on filled accent buttons
BTN_SECONDARY   = "#F3F4F6"   # Secondary button background
BTN_SECONDARY_FG= "#374151"   # Secondary button text
CARD_HEADER_FG  = ACCENT      # Section card titles
RESULT_BG       = "#F8FAFC"   # Result text box background
RESULT_FG       = "#0F4C81"   # Result text (readable dark-blue mono)
BADGE_CSV_BG    = SUCCESS_BG
BADGE_CSV_FG    = SUCCESS
BADGE_EXP_BG    = "#DBEAFE"   # Light blue badge
BADGE_EXP_FG    = ACCENT
BADGE_HEX_BG    = "#EDE9FE"   # Light purple badge
BADGE_HEX_FG    = ACCENT2

# Highlight overrides inside the table
TBL_TX_BG   = "#FEF9C3"   # Tx_cmd filter cell highlight background
TBL_TX_FG   = "#92400E"   # Tx_cmd filter cell highlight text
TBL_HEX_BG  = "#DCFCE7"   # Hex search match cell background
TBL_HEX_FG  = "#166534"   # Hex search match cell text

# Columns that are always present for validation
REQUIRED_COLUMNS = {
    "DateTime", "DeltaT", "BlockStatus", "MessageType",
    "Bus", "Rx_cmd", "Tx_cmd", "Tx_status", "Rx_status",
}

# Maps the column names found in the real telemetry export to the canonical
# names used throughout the rest of this application. Tx_cmd is included
# here purely as a *name* mapping — its filtering behaviour (4-char prefix
# match) is completely unchanged.
COLUMN_ALIASES = {
    "Time":     "DateTime",
    "Rx_Cmd":   "Rx_cmd",
    "Tx_Cmd":   "Tx_cmd",
    "Tx_Status": "Tx_status",
    "Rx_Status": "Rx_status",
}

# Name of the column in the raw CSV that holds the 32 space-separated
# 16-bit hex words (one row = one 1553 message).
DATA_COLUMN = "Data"
WORD_COUNT = 32


# ─── Data Layer ───────────────────────────────────────────────────────────────

class DataManager:
    """Owns all CSV loading and validation. Zero tkinter dependency."""

    def __init__(self):
        self.df: pd.DataFrame | None = None
        self.file_path: str = ""

    # ── Public API ────────────────────────────────────────────────────────────

    def load(self, path: str) -> None:
        """Load and validate a CSV file. Raises ValueError on bad structure."""
        df = pd.read_csv(path)
        df = self._normalize_columns(df)
        self._validate(df)
        self.df = df
        self.file_path = path

    def get_metadata(self) -> dict:
        """Return display-ready metadata about the loaded file."""
        if self.df is None:
            return {}
        size_bytes = os.path.getsize(self.file_path)
        return {
            "name":    os.path.basename(self.file_path),
            "size":    self._human_size(size_bytes),
            "rows":    len(self.df),
            "columns": len(self.df.columns),
            "path":    self.file_path,
        }

    def get_row(self, index: int) -> dict:
        """Return a single row as a column→value dict."""
        if self.df is None:
            return {}
        return self.df.iloc[index].to_dict()

    def get_columns(self) -> list[str]:
        return list(self.df.columns) if self.df is not None else []

    def get_display_rows(self, df: pd.DataFrame | None = None) -> list[tuple]:
        """Return rows as (original_index, value_tuple) pairs."""
        source = df if df is not None else self.df
        if source is None:
            return []
        return [(idx, tuple(str(v) for v in row))
                for idx, row in zip(source.index, source.itertuples(index=False))]

    # ── Private helpers ───────────────────────────────────────────────────────

    @staticmethod
    def _normalize_columns(df: pd.DataFrame) -> pd.DataFrame:
        """Make the raw export compatible with the rest of the application.

        - Renames the raw export's column names to the canonical names this
          application already expects (Tx_cmd filtering behaviour is
          unaffected — only the column *label* changes, e.g. "Tx_Cmd" ->
          "Tx_cmd").
        - Splits the single "Data" column (32 space-separated 16-bit hex
          words per row, e.g. "0X0  0X67bc  0Xb22e ...") into individual
          word0..word31 columns, which is the layout the table, hex search,
          and bit-analysis features all operate on.
        """
        df = df.rename(columns={k: v for k, v in COLUMN_ALIASES.items() if k in df.columns})

        if DATA_COLUMN in df.columns:
            split_words = df[DATA_COLUMN].fillna("").astype(str).str.split()

            for i in range(WORD_COUNT):
                df[f"word{i}"] = split_words.apply(
                    lambda toks, i=i: toks[i] if i < len(toks) else ""
                )

            # Drop the raw combined column now that it has been expanded —
            # word0..word31 carry the same information in the format every
            # other feature (hex search, bit analysis, highlighting) expects.
            df = df.drop(columns=[DATA_COLUMN])

        return df

    def _validate(self, df: pd.DataFrame) -> None:
        missing = REQUIRED_COLUMNS - set(df.columns)
        if missing:
            raise ValueError(
                f"Invalid file structure.\n"
                f"Missing required columns: {', '.join(sorted(missing))}"
            )
        if df.empty:
            raise ValueError("The CSV file contains no data rows.")

    @staticmethod
    def _human_size(n: int) -> str:
        for unit in ("B", "KB", "MB", "GB"):
            if n < 1024:
                return f"{n:.1f} {unit}"
            n /= 1024
        return f"{n:.1f} TB"


# ─── Hex Normalization Helpers ────────────────────────────────────────────────
# Accepts any of: 0xA12B, 0XA12B, A12B, a12b, ffff, FFFF
# and normalizes to a bare, uppercase hex-digit string (no "0x" prefix).
# All hex-related features (Hex Search, Bit Analysis, Value Conversion,
# Word Parsing, Highlighting, Validation) route through these helpers so
# hex handling is fully case-insensitive and prefix-insensitive.

def normalize_hex(raw) -> str:
    """Strip optional 0x/0X prefix + whitespace, return uppercase hex digits.

    Returns "" for empty / non-hex input (caller decides how to handle that).
    """
    if raw is None:
        return ""
    s = str(raw).strip()
    if not s:
        return ""
    if s[:2].lower() == "0x":
        s = s[2:]
    s = s.strip()
    if not s:
        return ""
    try:
        int(s, 16)
    except ValueError:
        return ""
    return s.upper()


def is_valid_hex_word(raw) -> bool:
    """True if `raw` normalizes to a non-empty 16-bit hex value."""
    digits = normalize_hex(raw)
    if not digits:
        return False
    return 0 <= int(digits, 16) <= 0xFFFF


# ─── Word Model & Bit Logic ───────────────────────────────────────────────────

class Word:
    """Represents a single 16-bit word parsed from a hex string.

    Accepts any hex representation (0xA12B, 0XA12B, A12B, a12b, ffff, FFFF, ...)
    via normalize_hex().
    """

    def __init__(self, raw: str):
        digits = normalize_hex(raw)
        if not digits:
            raise ValueError(f"'{raw}' is not a valid hexadecimal value")
        self.value = int(digits, 16)
        if not 0 <= self.value <= 65535:
            raise ValueError(f"'{raw}' = {self.value} is out of 16-bit range [0, 65535]")
        self.binary  = bin(self.value)[2:].zfill(16)
        self.hex     = f"0x{self.value:04X}"
        self.octal   = oct(self.value)
        self.decimal = self.value

    def as_fmt(self, fmt: str) -> str:
        return {
            "binary":      f"0b{self.binary}",
            "hexadecimal": self.hex,
            "octal":       self.octal,
            "decimal":     str(self.decimal),
        }[fmt]


def query_bit(word: Word, bit_idx: int) -> int:
    """Return the bit at bit_idx (1=MSB, 16=LSB)."""
    return int(word.binary[bit_idx - 1])


def query_bits_combined(
    word: Word, bit_indices: list, fmt: str
) -> tuple:
    """Return (formatted_result, combined_binary_str, decimal_value)."""
    combined = "".join(word.binary[i - 1] for i in bit_indices)
    value = int(combined, 2)
    result = {
        "binary":      f"0b{combined}",
        "hexadecimal": f"0x{value:X}",
        "octal":       oct(value),
        "decimal":     str(value),
    }
    return result[fmt], combined, value


# ─── GUI: Widget Helpers (mixin) ──────────────────────────────────────────────

class StyleMixin:
    """Reusable widget factory methods. Keeps frame-builders clean."""

    def _btn(self, parent, text: str, cmd, accent: bool = False, small: bool = False) -> tk.Button:
        if accent:
            bg, fg, hover_bg = ACCENT, BTN_FG, ACCENT_HOVER
        else:
            bg, fg, hover_bg = BTN_SECONDARY, BTN_SECONDARY_FG, BORDER
        font_size = 9 if small else 10
        btn = tk.Button(
            parent, text=text, command=cmd,
            font=(SANS, font_size, "bold"), bg=bg, fg=fg,
            activebackground=hover_bg, activeforeground=fg,
            relief="flat", bd=0, padx=12, pady=5, cursor="hand2",
        )
        btn.bind("<Enter>", lambda e: btn.config(bg=hover_bg))
        btn.bind("<Leave>", lambda e: btn.config(bg=bg))
        return btn

    def _label(self, parent, text: str, size: int = 10,
               fg: str = TEXT, bold: bool = False, mono: bool = False) -> tk.Label:
        font = (MONO if mono else SANS, size, "bold" if bold else "normal")
        return tk.Label(parent, text=text, font=font, bg=PANEL, fg=fg)

    def _status_set(self, msg: str, ok: bool = True) -> None:
        icon = "✓" if ok else "✗"
        color = SUCCESS if ok else ERROR
        self._status_var.set(f"{icon}  {msg}")
        self._status_label.config(fg=color)

    @staticmethod
    def _set_badge(label: tk.Label, text: str, bg: str, fg: str) -> None:
        """Update a status badge label's text and colors."""
        label.config(text=text, bg=bg, fg=fg)


# ─── GUI: Detail Panel ────────────────────────────────────────────────────────

class DetailPanel(tk.Frame, StyleMixin):
    """Right-side panel showing field:value pairs for the selected row."""

    def __init__(self, parent, **kwargs):
        super().__init__(parent, bg=PANEL, **kwargs)
        self._build()

    def _build(self) -> None:
        # Accent bar at top
        tk.Frame(self, bg=ACCENT, height=3).pack(fill="x")

        header = tk.Frame(self, bg=PANEL)
        header.pack(fill="x", padx=12, pady=(10, 6))

        tk.Label(header, text="ROW DETAILS", font=(SANS, 10, "bold"),
                 bg=PANEL, fg=ACCENT).pack(side="left")

        self._row_num_var = tk.StringVar(value="")
        tk.Label(header, textvariable=self._row_num_var, font=(SANS, 9),
                 bg=PANEL, fg=MUTED).pack(side="right")

        # Hairline separator
        tk.Frame(self, bg=BORDER, height=1).pack(fill="x", padx=8)

        # Scrollable canvas for field/value pairs
        outer = tk.Frame(self, bg=PANEL)
        outer.pack(fill="both", expand=True, padx=4)

        self._canvas = tk.Canvas(outer, bg=PANEL, highlightthickness=0)
        vsb = ttk.Scrollbar(outer, orient="vertical", command=self._canvas.yview)
        self._canvas.configure(yscrollcommand=vsb.set)

        vsb.pack(side="right", fill="y")
        self._canvas.pack(side="left", fill="both", expand=True)

        self._inner = tk.Frame(self._canvas, bg=PANEL)
        self._canvas_window = self._canvas.create_window(
            (0, 0), window=self._inner, anchor="nw"
        )

        self._inner.bind("<Configure>", self._on_inner_configure)
        self._canvas.bind("<Configure>", self._on_canvas_configure)

        # Placeholder
        self._placeholder = tk.Label(
            self._inner, text="Select a row\nto view details",
            font=(SANS, 11), bg=PANEL, fg=MUTED, justify="center"
        )
        self._placeholder.pack(pady=60)

        self._field_widgets: list[tk.Widget] = []

    def _on_inner_configure(self, _event=None) -> None:
        self._canvas.configure(scrollregion=self._canvas.bbox("all"))

    def _on_canvas_configure(self, event) -> None:
        self._canvas.itemconfig(self._canvas_window, width=event.width)

    def populate(self, row_data: dict, row_num: int) -> None:
        """Render all field:value pairs for the given row."""
        for w in self._field_widgets:
            w.destroy()
        self._field_widgets.clear()
        if self._placeholder:
            self._placeholder.destroy()
            self._placeholder = None

        self._row_num_var.set(f"Row {row_num + 1}")

        for i, (col, val) in enumerate(row_data.items()):
            bg = PANEL if i % 2 == 0 else ROW_ALT
            row_frame = tk.Frame(self._inner, bg=bg)
            row_frame.pack(fill="x", padx=4, pady=0)

            tk.Label(row_frame, text=col, font=(SANS, 8, "bold"),
                     bg=bg, fg=MUTED, anchor="w", width=14,
                     wraplength=110).pack(side="left", padx=(8, 4), pady=4)

            val_str = str(val) if val is not None else "—"
            is_hex = isinstance(val_str, str) and val_str.startswith("0x")
            fg = ACCENT if is_hex else TEXT
            tk.Label(row_frame, text=val_str, font=(MONO if is_hex else SANS, 9),
                     bg=bg, fg=fg, anchor="w",
                     wraplength=130).pack(side="left", padx=(0, 8), pady=4)

            self._field_widgets.append(row_frame)

    def clear(self) -> None:
        for w in self._field_widgets:
            w.destroy()
        self._field_widgets.clear()
        self._row_num_var.set("")
        if not self._placeholder:
            self._placeholder = tk.Label(
                self._inner, text="Select a row\nto view details",
                font=(SANS, 11), bg=PANEL, fg=MUTED, justify="center"
            )
            self._placeholder.pack(pady=60)


# ─── GUI: Main Table Frame ────────────────────────────────────────────────────

class TableFrame(tk.Frame):
    """Hosts a tksheet.Sheet — supports per-cell highlight for Tx_cmd prefix."""

    def __init__(self, parent, on_select_cb, **kwargs):
        super().__init__(parent, bg=BG, **kwargs)
        self._on_select_cb = on_select_cb
        self._columns: list[str] = []
        self._orig_indices: list[int] = []
        self._sheet: tksheet.Sheet | None = None
        self._build()

    def _build(self) -> None:
        self._container = tk.Frame(self, bg=BG)
        self._container.pack(fill="both", expand=True)

        self._placeholder_lbl = tk.Label(
            self._container,
            text="No file loaded.\nUse the button above to upload a CSV.",
            font=(SANS, 12), bg=BG, fg=MUTED, justify="center"
        )
        self._placeholder_lbl.pack(expand=True)

    def build_table(self, columns: list[str]) -> None:
        """Destroy existing sheet and rebuild for the given column set."""
        for w in self._container.winfo_children():
            w.destroy()

        self._columns = columns
        self._orig_indices = []

        word_cols = {f"word{i}" for i in range(32)}

        self._sheet = tksheet.Sheet(
            self._container,
            headers=columns,
            data=[],
            outline_color=BORDER,
            frame_bg=BG,
            table_bg=PANEL,
            table_fg=TEXT,
            table_grid_fg=BORDER,
            header_bg=META_BG,
            header_fg=ACCENT,
            header_font=(SANS, 9, "bold"),
            font=(MONO, 9, "normal"),
            row_index_bg=PANEL,
            row_index_fg=MUTED,
            selected_rows_border_fg=ACCENT2,
            selected_rows_bg="#EDE9FE",
            selected_rows_fg=ACCENT2,
            row_height=26,
            show_row_index=False,
            show_x_scrollbar=True,
            show_y_scrollbar=True,
        )
        self._sheet.pack(fill="both", expand=True)

        for i, col in enumerate(columns):
            w = 68 if col in word_cols else 110
            self._sheet.column_width(column=i, width=w)

        self._sheet.enable_bindings(
            "single_select", "row_select", "column_width_resize",
            "arrowkeys", "right_click_popup_menu", "rc_select",
        )
        self._sheet.bind("<<SheetSelect>>", self._on_select)

    def populate(self, rows: list[tuple], tx_filter: str | None = None,
                 hex_highlights: set[tuple] | None = None) -> None:
        """Load all rows and apply Tx_cmd cell prefix highlight if filter is set.
        hex_highlights is a set of (row_i, col_i) tuples to highlight in light green."""
        if self._sheet is None:
            return

        self._orig_indices = [orig_idx for orig_idx, _ in rows]
        data = [list(row) for _, row in rows]
        self._sheet.set_sheet_data(data, redraw=False)

        for i in range(len(data)):
            bg = PANEL if i % 2 == 0 else ROW_ALT
            self._sheet.highlight_rows(rows=[i], bg=bg, fg=TEXT, redraw=False)

        if tx_filter and "Tx_cmd" in self._columns:
            col_idx = self._columns.index("Tx_cmd")
            prefix_len = len(tx_filter)
            for row_i, row_vals in enumerate(data):
                cell_val = str(row_vals[col_idx])
                if cell_val.strip()[:prefix_len].upper() == tx_filter.upper():
                    self._sheet.highlight_cells(
                        row=row_i, column=col_idx,
                        bg=TBL_TX_BG, fg=TBL_TX_FG,
                        redraw=False,
                    )

        if hex_highlights:
            for (row_i, col_i) in hex_highlights:
                self._sheet.highlight_cells(
                    row=row_i, column=col_i,
                    bg=TBL_HEX_BG, fg=TBL_HEX_FG,
                    redraw=False,
                )

        self._sheet.redraw()

    def current_columns(self) -> list[str]:
        return list(self._columns)

    def _on_select(self, _event=None) -> None:
        sel = self._sheet.get_currently_selected()
        if sel and self._orig_indices:
            row_i = sel[0] if isinstance(sel[0], int) else sel.row
            if 0 <= row_i < len(self._orig_indices):
                self._on_select_cb(self._orig_indices[row_i])

    @property
    def _tree(self):
        return None


# ─── GUI: Metadata Bar ────────────────────────────────────────────────────────

class MetadataBar(tk.Frame):
    """Horizontal strip below the top bar showing file stats."""

    _FIELDS = ("name", "size", "rows", "columns")

    def __init__(self, parent, **kwargs):
        super().__init__(parent, bg=META_BG, **kwargs)
        self._vars: dict[str, tk.StringVar] = {}
        self._build()

    def _build(self) -> None:
        labels = {"name": "File", "size": "Size", "rows": "Rows", "columns": "Columns"}

        # Left-side stat cells
        cells_frame = tk.Frame(self, bg=META_BG)
        cells_frame.pack(side="left", fill="y")

        for key in self._FIELDS:
            # Vertical divider between cells
            if key != "name":
                tk.Frame(cells_frame, bg=BORDER, width=1).pack(side="left", fill="y", pady=6)
            cell = tk.Frame(cells_frame, bg=META_BG)
            cell.pack(side="left", padx=20, pady=8)
            tk.Label(cell, text=labels[key].upper(), font=(SANS, 7, "bold"),
                     bg=META_BG, fg=MUTED).pack(anchor="w")
            var = tk.StringVar(value="—")
            tk.Label(cell, textvariable=var, font=(MONO, 10, "bold"),
                     bg=META_BG, fg=TEXT).pack(anchor="w")
            self._vars[key] = var

    def update_meta(self, meta: dict) -> None:
        for key in self._FIELDS:
            val = meta.get(key, "—")
            self._vars[key].set(str(val))

    def reset(self) -> None:
        for var in self._vars.values():
            var.set("—")


# ─── GUI: Bit Analysis Panel ─────────────────────────────────────────────────

class BitAnalysisPanel(tk.Frame, StyleMixin):
    """
    Collapsible panel shown below the table after a successful Hex Search.
    Provides:
      • Value Conversion  – hex/bin/oct/dec of the selected word
      • Get Bit           – extract single bit (1=MSB, 16=LSB)
      • Combine Bits      – multi-bit picker with format selector
    """

    def __init__(self, parent, **kwargs):
        super().__init__(parent, bg=BG, **kwargs)
        self._word: Word | None = None          # currently analysed word
        self._word_label: str  = ""             # e.g. "word3"
        self._ba_bit_selected: list = []
        self._ba_bit_buttons: dict  = {}
        self._build()

    # ── Construction ──────────────────────────────────────────────────────────

    def _build(self) -> None:
        # ── Header row ──────────────────────────────────────────────────────
        hdr = tk.Frame(self, bg=PANEL, pady=6, padx=12,
                       highlightbackground=BORDER, highlightthickness=1)
        hdr.pack(fill="x")

        # Accent bar on left edge
        tk.Frame(hdr, bg=ACCENT2, width=4).pack(side="left", fill="y", padx=(0, 8))

        tk.Label(hdr, text="⚙  BIT ANALYSIS", font=(SANS, 10, "bold"),
                 bg=PANEL, fg=ACCENT2).pack(side="left")

        self._ba_word_var = tk.StringVar(value="— select a row after Hex Search —")
        tk.Label(hdr, textvariable=self._ba_word_var,
                 font=(MONO, 9), bg=PANEL, fg=MUTED).pack(side="left", padx=16)

        # ── Three-column body ────────────────────────────────────────────────
        body = tk.Frame(self, bg=BG)
        body.pack(fill="x", padx=0, pady=0)
        body.columnconfigure(0, weight=1)
        body.columnconfigure(1, weight=1)
        body.columnconfigure(2, weight=2)

        self._build_conversion_col(body)
        self._build_get_bit_col(body)
        self._build_combine_col(body)

    def _card(self, parent, col: int) -> tk.Frame:
        f = tk.Frame(parent, bg=PANEL,
                     highlightbackground=BORDER, highlightthickness=1)
        f.grid(row=0, column=col, sticky="nsew", padx=4, pady=4)
        return f

    def _result_box(self, parent, height: int = 4) -> tk.Text:
        box = tk.Text(parent, height=height, font=(MONO, 9),
                      bg=RESULT_BG, fg=RESULT_FG,
                      insertbackground=TEXT, relief="flat", bd=0,
                      highlightbackground=BORDER, highlightthickness=1,
                      wrap="word", state="disabled")
        box.pack(fill="x", padx=8, pady=(0, 8))
        return box

    def _write_result(self, box: tk.Text, text: str) -> None:
        box.config(state="normal")
        box.delete("1.0", "end")
        box.insert("end", text)
        box.config(state="disabled")

    # ── Column 1: Value Conversion ────────────────────────────────────────────

    def _build_conversion_col(self, body) -> None:
        card = self._card(body, col=0)
        tk.Label(card, text="VALUE CONVERSION", font=(SANS, 9, "bold"),
                 bg=PANEL, fg=ACCENT, pady=6).pack(anchor="w", padx=8)

        self._conv_result = self._result_box(card, height=5)

    def _refresh_conversion(self) -> None:
        if self._word is None:
            return
        w = self._word
        text = (
            f"Word     : {self._word_label}\n"
            f"Hex      : {w.hex}\n"
            f"Binary   : 0b{w.binary}\n"
            f"Octal    : {w.octal}\n"
            f"Decimal  : {w.decimal}"
        )
        self._write_result(self._conv_result, text)

    # ── Column 2: Get Bit ─────────────────────────────────────────────────────

    def _build_get_bit_col(self, body) -> None:
        card = self._card(body, col=1)
        tk.Label(card, text="GET BIT", font=(SANS, 9, "bold"),
                 bg=PANEL, fg=ACCENT, pady=6).pack(anchor="w", padx=8)

        inner = tk.Frame(card, bg=PANEL)
        inner.pack(fill="x", padx=8, pady=(0, 6))

        tk.Label(inner, text="Bit position (1=MSB, 16=LSB):",
                 font=(SANS, 9), bg=PANEL, fg=TEXT).pack(anchor="w")

        self._ba_bit_idx = tk.IntVar(value=1)
        tk.Spinbox(inner, from_=1, to=16, textvariable=self._ba_bit_idx,
                   width=5, font=(MONO, 10), bg=BORDER, fg=TEXT,
                   buttonbackground=BORDER, insertbackground=TEXT,
                   relief="flat", bd=2).pack(anchor="w", pady=4)

        self._btn(card, "Get Bit", self._do_get_bit, small=True).pack(
            anchor="w", padx=8, pady=(0, 4))

        self._bit_result_box = self._result_box(card, height=4)

    def _do_get_bit(self) -> None:
        if not self._require_word():
            return
        bit_idx = self._ba_bit_idx.get()
        try:
            bit_val = query_bit(self._word, bit_idx)
            pointer = " " * (bit_idx - 1) + "^"
            text = (
                f"{self._word_label}, Bit {bit_idx} -> {bit_val}\n"
                f"Binary  : {self._word.binary}\n"
                f"          {pointer} bit {bit_idx}"
            )
            self._write_result(self._bit_result_box, text)
        except Exception as exc:
            self._write_result(self._bit_result_box, f"Error: {exc}")

    # ── Column 3: Combine Bits ────────────────────────────────────────────────

    def _build_combine_col(self, body) -> None:
        card = self._card(body, col=2)
        tk.Label(card, text="COMBINE BITS", font=(SANS, 9, "bold"),
                 bg=PANEL, fg=ACCENT, pady=6).pack(anchor="w", padx=8)

        # Bit toggle buttons (1–16)
        tk.Label(card, text="Click bit positions to select (order preserved):",
                 font=(SANS, 8), bg=PANEL, fg=MUTED).pack(anchor="w", padx=8)

        bit_grid = tk.Frame(card, bg=PANEL)
        bit_grid.pack(padx=8, pady=(2, 0))

        self._ba_bit_buttons = {}
        self._ba_bit_selected = []

        for idx in range(1, 17):
            btn = tk.Button(
                bit_grid, text=str(idx), width=3, height=1,
                font=(MONO, 9), bg=BTN_SECONDARY, fg=BTN_SECONDARY_FG,
                activebackground=ACCENT, activeforeground=BTN_FG,
                relief="flat", bd=0, cursor="hand2",
                command=lambda pos=idx: self._toggle_ba_bit(pos),
            )
            btn.grid(row=0, column=idx - 1, padx=2, pady=2)
            self._ba_bit_buttons[idx] = btn

        self._ba_order_var = tk.StringVar(value="Selected: (none)")
        tk.Label(card, textvariable=self._ba_order_var,
                 font=(MONO, 8), bg=PANEL, fg=MUTED).pack(anchor="w", padx=8)

        btn_row = tk.Frame(card, bg=PANEL)
        btn_row.pack(anchor="w", padx=8, pady=(2, 4))

        # Output format
        fmt_row = tk.Frame(card, bg=PANEL)
        fmt_row.pack(fill="x", padx=8, pady=(0, 4))
        tk.Label(fmt_row, text="Format:", font=(SANS, 9), bg=PANEL, fg=TEXT).pack(side="left")
        self._ba_comb_fmt = tk.StringVar(value="binary")
        om = tk.OptionMenu(fmt_row, self._ba_comb_fmt,
                           "binary", "hexadecimal", "octal", "decimal")
        om.config(font=(SANS, 9), bg=BTN_SECONDARY, fg=BTN_SECONDARY_FG,
                  activebackground=ACCENT2, activeforeground=BTN_FG,
                  relief="flat", bd=0, highlightthickness=0, width=10)
        om["menu"].config(font=(SANS, 9), bg=PANEL, fg=TEXT,
                          activebackground=ACCENT2, activeforeground=BTN_FG)
        om.pack(side="left", padx=6)

        ctrl_row = tk.Frame(card, bg=PANEL)
        ctrl_row.pack(anchor="w", padx=8, pady=(0, 4))
        self._btn(ctrl_row, "Combine", self._do_combine_ba_bits, small=True).pack(side="left", padx=(0, 4))
        tk.Button(ctrl_row, text="Clear", font=(SANS, 9), bg=BTN_SECONDARY, fg=MUTED,
                  activebackground=BORDER, relief="flat", bd=0, cursor="hand2",
                  command=self._clear_ba_bits).pack(side="left")

        self._comb_result_box = self._result_box(card, height=6)

    def _toggle_ba_bit(self, position: int) -> None:
        if position in self._ba_bit_selected:
            self._ba_bit_selected.remove(position)
            self._ba_bit_buttons[position].config(bg=BTN_SECONDARY, fg=BTN_SECONDARY_FG)
        else:
            self._ba_bit_selected.append(position)
            self._ba_bit_buttons[position].config(bg=ACCENT, fg=BTN_FG)
        if self._ba_bit_selected:
            self._ba_order_var.set("Selected: " + ", ".join(str(b) for b in self._ba_bit_selected))
        else:
            self._ba_order_var.set("Selected: (none)")

    def _clear_ba_bits(self) -> None:
        self._ba_bit_selected.clear()
        for btn in self._ba_bit_buttons.values():
            btn.config(bg=BTN_SECONDARY, fg=BTN_SECONDARY_FG)
        self._ba_order_var.set("Selected: (none)")

    def _do_combine_ba_bits(self) -> None:
        if not self._require_word():
            return
        if not self._ba_bit_selected:
            self._write_result(self._comb_result_box, "Select at least one bit position.")
            return
        fmt = self._ba_comb_fmt.get()
        try:
            result, combined, value = query_bits_combined(
                self._word, self._ba_bit_selected, fmt
            )
            positions = ", ".join(str(b) for b in self._ba_bit_selected)
            picked = " ".join(
                f"b{b}={self._word.binary[b - 1]}" for b in self._ba_bit_selected
            )
            text = (
                f"{self._word_label}  : {self._word.binary}\n"
                f"Positions : {positions}\n"
                f"Picked    : {picked}\n"
                f"Combined  : {combined}\n"
                f"Result    : {result}  (decimal: {value})"
            )
            self._write_result(self._comb_result_box, text)
        except Exception as exc:
            self._write_result(self._comb_result_box, f"Error: {exc}")

    # ── Public API ────────────────────────────────────────────────────────────

    def load_word(self, col_name: str, raw_value: str) -> bool:
        """
        Parse raw_value as a 16-bit hex word and update all sub-panels.
        Returns True on success, False if the value is invalid.
        """
        try:
            self._word = Word(raw_value)
            self._word_label = col_name
            self._ba_word_var.set(f"{col_name}  =  {raw_value.strip()}")
            self._refresh_conversion()
            self._write_result(self._bit_result_box, "")
            self._write_result(self._comb_result_box, "")
            self._clear_ba_bits()
            return True
        except Exception:
            self._word = None
            self._word_label = ""
            self._ba_word_var.set(f"⚠  '{raw_value.strip()}' is not a valid 16-bit hex value")
            return False

    def reset(self) -> None:
        """Clear state; called when CSV is re-loaded or search is cleared."""
        self._word = None
        self._word_label = ""
        self._ba_bit_selected.clear()
        for btn in self._ba_bit_buttons.values():
            btn.config(bg=BTN_SECONDARY, fg=BTN_SECONDARY_FG)
        self._ba_order_var.set("Selected: (none)")
        self._ba_word_var.set("— select a row after Hex Search —")
        self._write_result(self._conv_result, "")
        self._write_result(self._bit_result_box, "")
        self._write_result(self._comb_result_box, "")

    def _require_word(self) -> bool:
        if self._word is None:
            return False
        return True


# ─── GUI: Filter Output Panel ────────────────────────────────────────────────

class FilterOutputPanel(tk.Frame, StyleMixin):
    """
    Collapsible panel showing the SubSys_comWordFiltered folder hierarchy.
    Always present in the layout; collapses/expands via the header chevron.
    Refreshed from the background export thread via the public `refresh` method
    (must be called on the Tkinter main thread via `app.after(0, ...)`).
    """

    _COLLAPSED_H = 32   # px — header-only height when collapsed
    _EXPANDED_H  = 180  # px — default expanded height

    def __init__(self, parent, **kwargs):
        super().__init__(parent, bg=BG, **kwargs)
        self._expanded  = True
        self._root_path: str = ""
        # Maps tree iid → absolute filesystem path for click handlers
        self._iid_to_path: dict[str, str] = {}
        self._build()

    # ── Construction ──────────────────────────────────────────────────────────

    def _build(self) -> None:
        self._build_header()
        self._build_body()

    def _build_header(self) -> None:
        hdr = tk.Frame(self, bg=PANEL, pady=5, padx=12,
                       highlightbackground=BORDER, highlightthickness=1)
        hdr.pack(fill="x")

        # Chevron toggle
        self._chevron_var = tk.StringVar(value="▾")
        tk.Button(
            hdr, textvariable=self._chevron_var,
            font=(SANS, 11), bg=PANEL, fg=ACCENT2,
            activebackground=META_BG, activeforeground=ACCENT,
            relief="flat", bd=0, cursor="hand2",
            command=self._toggle_collapse,
        ).pack(side="left", padx=(0, 6))

        tk.Label(hdr, text="📁  SUBSYSTEM FILTERED OUTPUT",
                 font=(SANS, 10, "bold"), bg=PANEL, fg=ACCENT2).pack(side="left")

        # Stats strip (right side of header)
        self._stats_var = tk.StringVar(value="— no export yet —")
        tk.Label(hdr, textvariable=self._stats_var,
                 font=(MONO, 8), bg=PANEL, fg=MUTED).pack(side="left", padx=16)

        # Open Export Directory button
        self._open_btn = tk.Button(
            hdr, text="📂  Open Export Directory",
            font=(SANS, 9, "bold"), bg=BTN_SECONDARY, fg=BTN_SECONDARY_FG,
            activebackground=ACCENT, activeforeground=BTN_FG,
            relief="flat", bd=0, padx=10, pady=3, cursor="hand2",
            command=self._open_root_dir,
            state="disabled",
        )
        self._open_btn.pack(side="right", padx=(4, 0))

    def _build_body(self) -> None:
        self._body = tk.Frame(self, bg=BG)
        self._body.pack(fill="both", expand=True)

        # ttk.Treeview styled for light engineering dashboard theme
        style = ttk.Style()
        style.theme_use("default")
        style.configure(
            "FilterTree.Treeview",
            background=PANEL, foreground=TEXT,
            fieldbackground=PANEL,
            borderwidth=0, rowheight=22,
            font=(MONO, 9),
        )
        style.configure(
            "FilterTree.Treeview.Heading",
            background=META_BG, foreground=ACCENT,
            font=(SANS, 9, "bold"), relief="flat",
        )
        style.map(
            "FilterTree.Treeview",
            background=[("selected", "#DBEAFE")],
            foreground=[("selected", ACCENT)],
        )

        tree_frame = tk.Frame(self._body, bg=PANEL,
                              highlightbackground=BORDER, highlightthickness=1)
        tree_frame.pack(fill="both", expand=True, padx=6, pady=4)

        self._tree = ttk.Treeview(
            tree_frame,
            style="FilterTree.Treeview",
            columns=("rows",),
            show="tree headings",
            selectmode="browse",
        )
        self._tree.heading("#0",    text="Structure",  anchor="w")
        self._tree.heading("rows",  text="Rows",       anchor="e")
        self._tree.column("#0",    stretch=True,  minwidth=260)
        self._tree.column("rows",  width=70, stretch=False, anchor="e")

        vsb = ttk.Scrollbar(tree_frame, orient="vertical",
                             command=self._tree.yview)
        self._tree.configure(yscrollcommand=vsb.set)
        vsb.pack(side="right", fill="y")
        self._tree.pack(fill="both", expand=True)

        # Bind interactions
        self._tree.bind("<ButtonRelease-1>",  self._on_single_click)
        self._tree.bind("<Double-Button-1>",  self._on_double_click)

        # Placeholder label shown before first export
        self._placeholder = tk.Label(
            self._body,
            text="Upload a CSV to generate subsystem folders.",
            font=(SANS, 9), bg=BG, fg=MUTED,
        )
        self._placeholder.pack(pady=8)

    # ── Collapse / Expand ─────────────────────────────────────────────────────

    def _toggle_collapse(self) -> None:
        if self._expanded:
            self._body.pack_forget()
            self._chevron_var.set("▸")
            self.configure(height=self._COLLAPSED_H)
        else:
            self._body.pack(fill="both", expand=True)
            self._chevron_var.set("▾")
        self._expanded = not self._expanded

    # ── Public API (called from main thread via after()) ──────────────────────

    def refresh(self, root_path: str, identifiers: list[str]) -> None:
        """
        Rebuild the tree from the export results.
        `identifiers` — list of valid 4-char subsystem IDs that were written
        (already sorted alphabetically by the export thread).
        Must be called on the Tkinter main thread.
        """
        self._root_path = root_path
        self._iid_to_path.clear()

        # Clear tree
        for item in self._tree.get_children():
            self._tree.delete(item)

        # Hide placeholder once we have real data
        if self._placeholder:
            self._placeholder.pack_forget()

        total_files = len(identifiers)

        # Root node
        root_iid = self._tree.insert(
            "", "end",
            text=f"  📁  SubSys_comWordFiltered",
            values=("",),
            open=True,
            tags=("root",),
        )
        self._iid_to_path[root_iid] = root_path
        self._tree.tag_configure("root", foreground=ACCENT)

        # identifiers already sorted alphabetically by the export thread;
        # map them to SS1, SS2, SS3, ... in that same order.
        sorted_ids = sorted(identifiers)
        for i, ident in enumerate(sorted_ids):
            ss_name  = f"SS{i + 1}"
            is_last  = (i == len(sorted_ids) - 1)
            branch   = "└──" if is_last else "├──"
            sub_dir  = os.path.join(root_path, ss_name)
            csv_file = os.path.join(sub_dir, f"filtered_{ss_name}.csv")

            # Count rows (header excluded)
            row_count = self._count_rows(csv_file)
            row_label = str(row_count) if row_count >= 0 else "?"

            # Subsystem folder node
            folder_iid = self._tree.insert(
                root_iid, "end",
                text=f"  {branch} 📂  {ss_name}",
                values=("",),
                open=True,
                tags=("folder",),
            )
            self._iid_to_path[folder_iid] = sub_dir
            self._tree.tag_configure("folder", foreground=WARN)

            # CSV file node
            sub_branch = "    └──" if is_last else "│   └──"
            file_iid = self._tree.insert(
                folder_iid, "end",
                text=f"  {sub_branch} 🗒  filtered_{ss_name}.csv",
                values=(row_label,),
                tags=("csvfile",),
            )
            self._iid_to_path[file_iid] = csv_file
            self._tree.tag_configure("csvfile", foreground=SUCCESS)

        # Update header stats
        self._stats_var.set(
            f"{len(identifiers)} subsystems  ·  {total_files} file(s)  ·  {root_path}"
        )
        self._open_btn.config(state="normal")

        # Auto-expand if collapsed
        if not self._expanded:
            self._toggle_collapse()

    # ── Interaction Handlers ──────────────────────────────────────────────────

    def _on_single_click(self, _event=None) -> None:
        """Single-click on a folder node → open that folder."""
        iid = self._tree.focus()
        if not iid:
            return
        tags = self._tree.item(iid, "tags")
        if "folder" in tags or "root" in tags:
            path = self._iid_to_path.get(iid, "")
            if path and os.path.isdir(path):
                self._open_in_explorer(path)

    def _on_double_click(self, _event=None) -> None:
        """Double-click on a CSV file node → open its containing folder."""
        iid = self._tree.focus()
        if not iid:
            return
        tags = self._tree.item(iid, "tags")
        if "csvfile" in tags:
            path = self._iid_to_path.get(iid, "")
            if path and os.path.isfile(path):
                self._open_in_explorer(os.path.dirname(path))

    def _open_root_dir(self) -> None:
        if self._root_path and os.path.isdir(self._root_path):
            self._open_in_explorer(self._root_path)

    # ── Helpers ───────────────────────────────────────────────────────────────

    @staticmethod
    def _open_in_explorer(path: str) -> None:
        """Open `path` in the OS file manager (Windows / macOS / Linux)."""
        try:
            system = platform.system()
            if system == "Windows":
                os.startfile(path)                          # noqa: S606
            elif system == "Darwin":
                subprocess.Popen(["open", path])
            else:
                subprocess.Popen(["xdg-open", path])
        except Exception:
            pass  # Silent fail — non-critical UI action

    @staticmethod
    def _count_rows(csv_path: str) -> int:
        """Fast line count minus the header; returns -1 on error."""
        try:
            with open(csv_path, "r", encoding="utf-8", errors="replace") as fh:
                total = sum(1 for _ in fh)
            return max(0, total - 1)   # exclude header line
        except OSError:
            return -1


# ─── GUI: Telemetry Plot Window ───────────────────────────────────────────────

class PlotWindow(tk.Toplevel):
    """Separate window plotting word0..word31 as integer traces over time.

    - X-axis: 'Serial Number' / 'SerialNumber' / 'SerialNo' column if present
      in the loaded data, otherwise the DataFrame row index.
    - Y-axis: integer value of each word column (hex -> int via
      normalize_hex / Word, case- and prefix-insensitive).
    - Each word column is an independent trace with its own color and a
      legend. Pan/zoom is provided by matplotlib's standard navigation
      toolbar (embedded below the plot).
    - Missing / invalid / blank word values are skipped (not plotted as 0),
      so gaps simply break that word's line.
    """

    WORD_COLS = [f"word{i}" for i in range(32)]

    # X-axis column candidates, in priority order
    _X_CANDIDATES = ["Serial Number", "SerialNumber", "Serial_Number", "SerialNo"]

    def __init__(self, parent: tk.Tk, df: pd.DataFrame, **kwargs):
        super().__init__(parent, **kwargs)
        self.title("Telemetry Plot — word0 .. word31")
        self.configure(bg=BG)
        self.geometry("1100x700")

        self._df = df
        self._build()

    def _build(self) -> None:
        toolbar_frame = tk.Frame(self, bg=PANEL)
        toolbar_frame.pack(side="bottom", fill="x")

        fig = Figure(figsize=(10, 6), dpi=100)
        ax = fig.add_subplot(111)

        present_word_cols = [c for c in self.WORD_COLS if c in self._df.columns]

        if not present_word_cols:
            ax.text(0.5, 0.5, "No word0..word31 columns available to plot.",
                    ha="center", va="center", transform=ax.transAxes)
        else:
            # Determine X-axis source
            x_col = next((c for c in self._X_CANDIDATES if c in self._df.columns), None)
            if x_col is not None:
                x_values = pd.to_numeric(self._df[x_col], errors="coerce")
                x_label = x_col
            else:
                x_values = pd.Series(self._df.index, index=self._df.index)
                x_label = "Row Index"

            # Distinct colors across the full word range via a continuous colormap
            cmap = matplotlib.colormaps["tab20"] if hasattr(matplotlib, "colormaps") \
                else matplotlib.cm.get_cmap("tab20")

            plotted_any = False
            for i, col in enumerate(present_word_cols):
                int_values = self._df[col].apply(self._hex_to_int)

                valid = int_values.notna()
                if not valid.any():
                    continue  # entire column is invalid/missing — skip gracefully

                xs = x_values[valid]
                ys = int_values[valid]

                color = cmap(i / max(1, len(present_word_cols) - 1))
                ax.plot(xs, ys, label=col, color=color, linewidth=1.0, marker="")
                plotted_any = True

            if not plotted_any:
                ax.text(0.5, 0.5, "No valid hex values found in word0..word31.",
                        ha="center", va="center", transform=ax.transAxes)
            else:
                ax.set_xlabel(x_label)
                ax.set_ylabel("Word Value (decimal)")
                ax.set_title("Telemetry Words — word0 .. word31")
                ax.grid(True, linestyle="--", linewidth=0.5, alpha=0.6)
                ax.legend(loc="upper right", fontsize=7, ncol=4)

        fig.tight_layout()

        canvas = FigureCanvasTkAgg(fig, master=self)
        canvas.draw()
        canvas.get_tk_widget().pack(side="top", fill="both", expand=True)

        # Standard matplotlib navigation toolbar — provides pan + zoom + reset
        toolbar = NavigationToolbar2Tk(canvas, toolbar_frame)
        toolbar.update()

        # ── FUTURE ANALYTICS (DISABLED) ─────────────────────────────────────
        # The blocks below are placeholders for future analytics features.
        # They are intentionally inert (commented out) and must not be
        # activated as part of this change. Each can be wired up later by
        # uncommenting and adding the relevant UI controls (e.g. a
        # checkbox/menu in PlotWindow to toggle each overlay on `ax`).
        #
        # --- Moving Average -------------------------------------------------
        # FUTURE ANALYTICS (DISABLED)
        # window = 5
        # for i, col in enumerate(present_word_cols):
        #     int_values = self._df[col].apply(self._hex_to_int)
        #     ma = int_values.rolling(window=window, min_periods=1).mean()
        #     ax.plot(x_values, ma, linestyle="--", linewidth=0.8,
        #             label=f"{col} (MA{window})")
        #
        # --- Anomaly Detection ----------------------------------------------
        # FUTURE ANALYTICS (DISABLED)
        # from scipy import stats  # or a simple z-score implementation
        # for i, col in enumerate(present_word_cols):
        #     int_values = self._df[col].apply(self._hex_to_int)
        #     z = (int_values - int_values.mean()) / int_values.std(ddof=0)
        #     anomalies = int_values[z.abs() > 3]
        #     ax.scatter(x_values.loc[anomalies.index], anomalies,
        #                color="red", marker="x", s=20,
        #                label=f"{col} anomalies")
        #
        # --- Threshold Bands -------------------------------------------------
        # FUTURE ANALYTICS (DISABLED)
        # lower_threshold, upper_threshold = 1000, 60000
        # ax.axhspan(lower_threshold, upper_threshold,
        #            color="green", alpha=0.05, label="Normal band")
        # ax.axhline(lower_threshold, color="orange", linestyle=":", linewidth=0.8)
        # ax.axhline(upper_threshold, color="orange", linestyle=":", linewidth=0.8)
        #
        # --- Min/Max Highlighting --------------------------------------------
        # FUTURE ANALYTICS (DISABLED)
        # for i, col in enumerate(present_word_cols):
        #     int_values = self._df[col].apply(self._hex_to_int)
        #     if int_values.notna().any():
        #         idx_max = int_values.idxmax()
        #         idx_min = int_values.idxmin()
        #         ax.annotate("max", (x_values[idx_max], int_values[idx_max]),
        #                      color="darkred")
        #         ax.annotate("min", (x_values[idx_min], int_values[idx_min]),
        #                      color="darkblue")
        #
        # --- Word Correlation Analysis ---------------------------------------
        # FUTURE ANALYTICS (DISABLED)
        # int_df = pd.DataFrame({
        #     col: self._df[col].apply(self._hex_to_int) for col in present_word_cols
        # })
        # corr_matrix = int_df.corr()
        # # e.g. render corr_matrix as a heatmap in a separate tab/figure:
        # # fig2 = Figure(figsize=(8, 8)); ax2 = fig2.add_subplot(111)
        # # ax2.imshow(corr_matrix, cmap="coolwarm", vmin=-1, vmax=1)
        # ────────────────────────────────────────────────────────────────────

    @staticmethod
    def _hex_to_int(raw) -> float:
        """Convert a word cell to an int value, or NaN if missing/invalid.

        Uses the same case-/prefix-insensitive normalization as every other
        hex feature in this application (normalize_hex / Word).
        """
        digits = normalize_hex(raw)
        if not digits:
            return float("nan")
        value = int(digits, 16)
        if not 0 <= value <= 0xFFFF:
            return float("nan")
        return float(value)


# ─── GUI: Main Application ────────────────────────────────────────────────────

class App(tk.Tk, StyleMixin):

    def __init__(self):
        super().__init__()
        self.title("Telemetry CSV Viewer")
        self.configure(bg=BG)
        self.minsize(1100, 640)
        self.resizable(True, True)

        self._data = DataManager()
        self._tx_filter: str | None = None
        self._selected_word_cols: list[str] | None = None
        self._hex_search: str | None = None
        self._display_df: pd.DataFrame | None = None
        self._last_selected_word_col: str | None = None   # word col of last selected row
        self._display_format = tk.StringVar(value="Hexadecimal")
        self._build_ui()

    # ── Display Format Helper ─────────────────────────────────────────────────

    def _format_word_display(self, value) -> str:
        """Convert a raw word cell value to the currently selected display format.

        Only called at display time — never modifies self._data.df.
        Falls back to the original string on any parse failure.
        """
        fmt = self._display_format.get().lower()
        if fmt == "hexadecimal":
            return str(value)   # already stored as hex; no conversion needed
        digits = normalize_hex(value)
        if not digits:
            return str(value)   # invalid / empty — show original unchanged
        try:
            w = Word(value)
        except Exception:
            return str(value)
        if fmt == "binary":
            return f"0b{w.binary}"
        if fmt == "integer":
            return str(w.decimal)
        if fmt == "octal":
            return w.octal
        return str(value)

    # ── UI Construction ───────────────────────────────────────────────────────

    def _build_ui(self) -> None:
        self._build_topbar()
        self._build_metadata_bar()
        self._build_word_selector_bar()
        self._build_main_area()
        self._build_bit_analysis_bar()
        self._build_filter_output_panel()
        self._build_statusbar()

    def _build_topbar(self) -> None:
        bar = tk.Frame(self, bg=TOPBAR_BG, pady=10, padx=16)
        bar.pack(fill="x")

        # Title block (left)
        title_block = tk.Frame(bar, bg=TOPBAR_BG)
        title_block.pack(side="left")

        tk.Label(title_block, text="TELEMETRY CSV VIEWER",
                 font=(SANS, 13, "bold"), bg=TOPBAR_BG, fg=TOPBAR_FG).pack(anchor="w")
        tk.Label(title_block, text="Telemetry Analysis & Subsystem Filtering Tool",
                 font=(SANS, 8), bg=TOPBAR_BG, fg="#93B8E0").pack(anchor="w")

        # Button row (right) — primary action first
        right = tk.Frame(bar, bg=TOPBAR_BG)
        right.pack(side="right")

        def _topbar_btn(text, cmd, primary=False):
            if primary:
                bg, fg, hover = ACCENT, BTN_FG, ACCENT_HOVER
            else:
                bg, fg, hover = "#2D4E6F", TOPBAR_FG, "#3A6080"
            btn = tk.Button(
                right, text=text, command=cmd,
                font=(SANS, 9, "bold"), bg=bg, fg=fg,
                activebackground=hover, activeforeground=fg,
                relief="flat", bd=0, padx=11, pady=5, cursor="hand2",
            )
            btn.bind("<Enter>", lambda e: btn.config(bg=hover))
            btn.bind("<Leave>", lambda e: btn.config(bg=bg))
            return btn

        _topbar_btn("📂  Upload CSV",       self._upload_file,       primary=True).pack(side="right", padx=(4, 0))
        _topbar_btn("📈  Plot Telemetry",   self._open_plot_window               ).pack(side="right", padx=(4, 0))
        _topbar_btn("💾  Download Display", self._download_display               ).pack(side="right", padx=(4, 0))
        _topbar_btn("✕  Clear Filter",      self._clear_tx_filter               ).pack(side="right", padx=(4, 0))
        _topbar_btn("🔍  Filter Tx_cmd",    self._apply_tx_filter               ).pack(side="right", padx=(4, 0))
        _topbar_btn("✕  Clear Search",      self._clear_hex_search              ).pack(side="right", padx=(4, 0))
        _topbar_btn("🔎  Search Hex",       self._apply_hex_search              ).pack(side="right", padx=(4, 0))

    def _build_metadata_bar(self) -> None:
        self._meta_bar = MetadataBar(self)
        self._meta_bar.pack(fill="x")

    def _build_word_selector_bar(self) -> None:
        bar = tk.Frame(self, bg=PANEL, pady=6, padx=16,
                       highlightbackground=BORDER, highlightthickness=1)
        bar.pack(fill="x")

        tk.Label(bar, text="WORD COLUMNS:", font=(SANS, 8, "bold"),
                 bg=PANEL, fg=MUTED).pack(side="left", padx=(0, 8))

        lb_frame = tk.Frame(bar, bg=BORDER, bd=0,
                            highlightbackground=BORDER, highlightthickness=1)
        lb_frame.pack(side="left")

        self._word_listbox = tk.Listbox(
            lb_frame,
            selectmode="multiple",
            exportselection=False,
            font=(MONO, 8),
            bg=PANEL, fg=TEXT,
            selectbackground=ACCENT2, selectforeground=BTN_FG,
            highlightthickness=0, bd=0,
            height=2,
            width=52,
        )
        hsb = tk.Scrollbar(lb_frame, orient="horizontal",
                           command=self._word_listbox.xview)
        self._word_listbox.configure(xscrollcommand=hsb.set)
        self._word_listbox.pack(side="top")
        hsb.pack(side="top", fill="x")

        for i in range(32):
            self._word_listbox.insert("end", f"word{i}")

        self._btn(bar, "Apply Columns", self._apply_word_cols, small=True).pack(side="left", padx=(8, 4))
        self._btn(bar, "Reset Columns", self._reset_word_cols, small=True).pack(side="left", padx=(0, 4))

        # ── Display Format dropdown ──────────────────────────────────────────
        tk.Frame(bar, bg=BORDER, width=1).pack(side="left", fill="y", padx=(10, 8), pady=2)

        tk.Label(bar, text="DISPLAY FORMAT:", font=(SANS, 8, "bold"),
                 bg=PANEL, fg=MUTED).pack(side="left", padx=(0, 4))

        fmt_om = tk.OptionMenu(
            bar, self._display_format,
            "Hexadecimal", "Binary", "Integer", "Octal",
            command=lambda _: self._refresh_table(),
        )
        fmt_om.config(
            font=(MONO, 8), bg=BTN_SECONDARY, fg=BTN_SECONDARY_FG,
            activebackground=ACCENT2, activeforeground=BTN_FG,
            relief="flat", bd=0, highlightthickness=0, width=11,
        )
        fmt_om["menu"].config(
            font=(MONO, 8), bg=PANEL, fg=TEXT,
            activebackground=ACCENT2, activeforeground=BTN_FG,
        )
        fmt_om.pack(side="left")

    def _build_main_area(self) -> None:
        """Horizontal pane: table (left, expandable) + detail panel (right, fixed)."""
        pane = tk.PanedWindow(self, orient="horizontal", bg=BORDER,
                              sashwidth=5, sashrelief="flat")
        pane.pack(fill="both", expand=True, padx=0, pady=0)

        # Left: table
        table_container = tk.Frame(pane, bg=BG)
        self._table = TableFrame(table_container, on_select_cb=self._on_row_select)
        self._table.pack(fill="both", expand=True, padx=8, pady=8)
        pane.add(table_container, stretch="always", minsize=600)

        # Right: detail panel — border left side via highlightbackground
        detail_container = tk.Frame(pane, bg=PANEL,
                                    highlightbackground=BORDER, highlightthickness=1)
        self._detail = DetailPanel(detail_container)
        self._detail.pack(fill="both", expand=True)
        pane.add(detail_container, stretch="never", minsize=260, width=300)

    def _build_bit_analysis_bar(self) -> None:
        """Bit analysis panel — shown only after a successful Hex Search."""
        self._bit_analysis = BitAnalysisPanel(self)
        # Hidden until hex search finds matches
        # (pack is called dynamically in _show_bit_analysis / _hide_bit_analysis)

    def _build_filter_output_panel(self) -> None:
        """Filter output panel — always present, refreshed after each export."""
        self._filter_output = FilterOutputPanel(self)
        self._filter_output.pack(fill="x")

    def _show_bit_analysis(self) -> None:
        if not self._bit_analysis.winfo_ismapped():
            # Insert between main area and filter output panel
            self._bit_analysis.pack(fill="x", before=self._filter_output)
        self._set_badge(self._badge_hex, "● HEX SEARCH", BADGE_HEX_BG, BADGE_HEX_FG)

    def _hide_bit_analysis(self) -> None:
        if self._bit_analysis.winfo_ismapped():
            self._bit_analysis.pack_forget()
        self._bit_analysis.reset()
        self._set_badge(self._badge_hex, "○ HEX SEARCH", BTN_SECONDARY, MUTED)

    def _build_statusbar(self) -> None:
        bar = tk.Frame(self, bg=PANEL, pady=0,
                       highlightbackground=BORDER, highlightthickness=1)
        bar.pack(fill="x", side="bottom")
        self._status_frame = bar

        # Left: status message
        msg_frame = tk.Frame(bar, bg=PANEL)
        msg_frame.pack(side="left", fill="y")
        self._status_var = tk.StringVar(value="Upload a CSV file to begin.")
        self._status_label = tk.Label(
            msg_frame, textvariable=self._status_var,
            font=(SANS, 9), bg=PANEL, fg=MUTED, padx=14, pady=6,
        )
        self._status_label.pack(side="left")

        # Right: badge cluster
        badge_frame = tk.Frame(bar, bg=PANEL)
        badge_frame.pack(side="right", padx=10, pady=4)

        def _badge(parent, text, bg, fg):
            lbl = tk.Label(parent, text=text, font=(SANS, 8, "bold"),
                           bg=bg, fg=fg, padx=8, pady=3,
                           relief="flat", bd=0)
            lbl.pack(side="right", padx=3)
            return lbl

        self._badge_hex = _badge(badge_frame, "○ HEX SEARCH",  BTN_SECONDARY, MUTED)
        self._badge_exp = _badge(badge_frame, "○ EXPORT DONE", BTN_SECONDARY, MUTED)
        self._badge_csv = _badge(badge_frame, "○ CSV LOADED",  BTN_SECONDARY, MUTED)

        # Search result label (kept for internal logic — visually replaces hex badge text)
        self._search_result_var = tk.StringVar(value="")
        self._search_result_label = tk.Label(
            bar, textvariable=self._search_result_var,
            font=(SANS, 9, "bold"), bg=PANEL, fg=SUCCESS, padx=8
        )
        self._search_result_label.pack(side="right")

    # ── Event Handlers ────────────────────────────────────────────────────────

    def _upload_file(self) -> None:
        path = filedialog.askopenfilename(
            title="Select CSV file",
            filetypes=[("CSV files", "*.csv"), ("All files", "*.*")]
        )
        if not path:
            return

        try:
            self._data.load(path)
        except Exception as exc:
            messagebox.showerror("Validation Error", str(exc))
            self._status_set(f"Failed to load: {exc}", ok=False)
            return

        # Success — update all panels
        meta = self._data.get_metadata()
        self._meta_bar.update_meta(meta)

        self._tx_filter = None
        self._selected_word_cols = None
        self._hex_search = None
        self._search_result_var.set("")
        self._word_listbox.selection_clear(0, "end")
        self._hide_bit_analysis()

        columns = self._data.get_columns()
        self._table.build_table(columns)
        self._refresh_table()

        self._detail.clear()

        self._status_set(
            f"Loaded '{meta['name']}' — {meta['rows']} rows × {meta['columns']} columns.", ok=True
        )
        # Update CSV badge; reset export badge until new export completes
        self._set_badge(self._badge_csv, "● CSV LOADED",  BADGE_CSV_BG, BADGE_CSV_FG)
        self._set_badge(self._badge_exp, "○ EXPORT DONE", BTN_SECONDARY, MUTED)

        # Launch background export (non-blocking)
        t = threading.Thread(
            target=self._export_filtered_by_subsystem,
            args=(path, self._data.df.copy()),
            daemon=True,
        )
        t.start()

    def _export_filtered_by_subsystem(self, csv_path: str, df: pd.DataFrame) -> None:
        """
        Background thread: create SubSys_comWordFiltered/SSn/filtered_SSn.csv
        for each unique 4-character Tx_cmd prefix found in the loaded CSV.
        Subsystem identifiers are sorted alphabetically; the first maps to SS1,
        the second to SS2, and so on (deterministic, stable ordering).
        Safe to run off the main thread — only touches the filesystem.
        """
        try:
            out_root = os.path.join(os.path.dirname(csv_path), "SubSys_comWordFiltered")
            os.makedirs(out_root, exist_ok=True)

            # Extract valid 4-char identifiers (skip null / short values)
            tx_series = df["Tx_cmd"].astype(str).str.strip()
            identifiers = (
                tx_series[tx_series.str.len() >= 4]
                .str[:4]
                .str.upper()
                .unique()
            )

            # Sort alphabetically for deterministic SS1/SS2/... mapping
            sorted_ids = sorted(
                ident for ident in identifiers
                if ident and ident.upper() != "NAN"
            )

            valid_ids: list[str] = []
            for i, ident in enumerate(sorted_ids):
                ss_name = f"SS{i + 1}"

                sub_dir = os.path.join(out_root, ss_name)
                os.makedirs(sub_dir, exist_ok=True)

                mask = tx_series.str[:4].str.upper() == ident
                filtered = df.loc[mask]

                out_file = os.path.join(sub_dir, f"filtered_{ss_name}.csv")
                filtered.to_csv(out_file, index=False)
                valid_ids.append(ident)

            # Report back on the main thread via `after`
            n = len(valid_ids)
            self.after(
                0,
                lambda r=out_root, ids=valid_ids, count=n: (
                    self._status_set(
                        f"SubSys_comWordFiltered: {count} subsystem folder(s) written alongside the CSV.", ok=True
                    ),
                    self._filter_output.refresh(r, ids),
                    self._set_badge(self._badge_exp, "● EXPORT DONE", BADGE_EXP_BG, BADGE_EXP_FG),
                ),
            )

        except Exception as exc:
            self.after(
                0,
                lambda e=exc: self._status_set(
                    f"SubSys_comWordFiltered export failed: {e}", ok=False
                ),
            )

    def _on_row_select(self, row_index: int) -> None:
        row_data = self._data.get_row(row_index)
        self._detail.populate(row_data, row_index)
        self._status_set(f"Viewing row {row_index + 1}.", ok=True)

        # If a hex search is active, try to populate bit analysis with the
        # first matched word column that has a valid hex value in this row.
        if self._hex_search and self._bit_analysis.winfo_ismapped():
            target = self._hex_search
            word_set = {f"word{i}" for i in range(32)}
            # Find the first word column whose value matches the search target
            matched_col = None
            matched_val = None
            for col, val in row_data.items():
                if col in word_set:
                    val_str = str(val).strip()
                    if normalize_hex(val_str) == target:
                        matched_col = col
                        matched_val = val_str
                        break
            # If no exact match in this row, try the first word column with a valid hex value
            if matched_col is None:
                for col, val in row_data.items():
                    if col in word_set:
                        val_str = str(val).strip()
                        if is_valid_hex_word(val_str):
                            matched_col = col
                            matched_val = val_str
                            break
            if matched_col and matched_val:
                self._bit_analysis.load_word(matched_col, matched_val)

    def _apply_tx_filter(self) -> None:
        if self._data.df is None:
            self._status_set("Load a CSV file first.", ok=False)
            return
        value = simpledialog.askstring(
            "Filter Tx_cmd", "Enter 4-char Tx_cmd prefix (e.g. 5BC0):",
            parent=self
        )
        if value is None:
            return
        self._tx_filter = value.strip().upper()
        self._refresh_table()
        self._status_set(f"Tx_cmd filter '{self._tx_filter}' applied.", ok=True)

    def _clear_tx_filter(self) -> None:
        if self._data.df is None:
            return
        self._tx_filter = None
        self._refresh_table()
        self._status_set("Tx_cmd filter cleared.", ok=True)

    def _refresh_table(self) -> None:
        if self._data.df is None:
            return

        if self._tx_filter:
            mask = self._data.df["Tx_cmd"].apply(
                lambda x: str(x).strip()[:4].upper() == self._tx_filter
            )
            source_df = self._data.df.loc[mask]
        else:
            source_df = self._data.df

        if self._selected_word_cols is not None:
            all_cols = self._data.get_columns()
            word_set = {f"word{i}" for i in range(32)}
            visible_cols = [c for c in all_cols if c not in word_set or c in self._selected_word_cols]
            display_df = source_df[visible_cols]
        else:
            display_df = source_df

        visible_cols_now = list(display_df.columns)
        if self._table.current_columns() != visible_cols_now:
            self._table.build_table(visible_cols_now)

        rows = self._data.get_display_rows(display_df)

        # Compute hex highlights
        hex_highlights: set[tuple] | None = None
        if self._hex_search:
            target = self._hex_search
            word_set = {f"word{i}" for i in range(32)}
            searchable_cols = [
                (ci, col) for ci, col in enumerate(visible_cols_now) if col in word_set
            ]
            hex_highlights = set()
            matched_rows = set()
            for row_i, (_, row_vals) in enumerate(rows):
                for ci, col in searchable_cols:
                    if normalize_hex(row_vals[ci]) == target:
                        hex_highlights.add((row_i, ci))
                        matched_rows.add(row_i)
            # Update search result label
            if hex_highlights:
                self._search_result_var.set(
                    f"Search '0x{self._hex_search}': {len(hex_highlights)} cell(s) in {len(matched_rows)} row(s)"
                )
                self._search_result_label.config(fg=SUCCESS)
                self._show_bit_analysis()
            else:
                self._search_result_var.set(f"No matches found for 0x{self._hex_search}")
                self._search_result_label.config(fg=ERROR)
                self._hide_bit_analysis()

        self._display_df = display_df

        # Apply word-column display formatting (display layer only — df untouched)
        word_set = {f"word{i}" for i in range(32)}
        fmt = self._display_format.get().lower()
        if fmt != "hexadecimal":
            word_col_indices = {
                ci for ci, col in enumerate(visible_cols_now) if col in word_set
            }
            formatted_rows = []
            for orig_idx, row_vals in rows:
                row_list = list(row_vals)
                for ci in word_col_indices:
                    row_list[ci] = self._format_word_display(row_list[ci])
                formatted_rows.append((orig_idx, tuple(row_list)))
            rows = formatted_rows

        self._table.populate(rows, tx_filter=self._tx_filter, hex_highlights=hex_highlights)

        self._detail.clear()

    def _apply_hex_search(self) -> None:
        if self._data.df is None:
            self._status_set("Load a CSV file first.", ok=False)
            return
        value = simpledialog.askstring(
            "Search Hex Value", "Enter hex value to search (e.g. 0xA12B):",
            parent=self
        )
        if value is None:
            return
        value = value.strip()
        if not value:
            return
        normalized = normalize_hex(value)
        if not normalized:
            self._status_set(f"'{value}' is not a valid hexadecimal value.", ok=False)
            return
        self._hex_search = normalized
        self._refresh_table()
        self._status_set(f"Hex search for '0x{self._hex_search}' applied.", ok=True)

    def _clear_hex_search(self) -> None:
        if self._hex_search is None:
            return
        self._hex_search = None
        self._search_result_var.set("")
        self._hide_bit_analysis()
        self._refresh_table()
        self._status_set("Hex search cleared.", ok=True)

    def _download_display(self) -> None:
        if self._display_df is None or self._display_df.empty:
            self._status_set("Nothing to export — load a file first.", ok=False)
            return
        path = filedialog.asksaveasfilename(
            title="Save displayed data as CSV",
            defaultextension=".csv",
            filetypes=[("CSV files", "*.csv"), ("All files", "*.*")],
        )
        if not path:
            return
        try:
            self._display_df.to_csv(path, index=False)
            self._status_set(f"Exported {len(self._display_df)} rows → '{os.path.basename(path)}'.", ok=True)
        except Exception as exc:
            self._status_set(f"Export failed: {exc}", ok=False)

    def _open_plot_window(self) -> None:
        """Open the matplotlib telemetry plot window for word0..word31.

        Plots the full loaded dataset (independent of the current Tx_cmd
        filter / hex search / word-column visibility selections), so the
        existing table-centric workflows are left untouched.
        """
        if self._data.df is None:
            self._status_set("Load a CSV file first.", ok=False)
            return
        PlotWindow(self, self._data.df)
        self._status_set("Opened telemetry plot window.", ok=True)

    def _apply_word_cols(self) -> None:
        if self._data.df is None:
            self._status_set("Load a CSV file first.", ok=False)
            return
        selected = [self._word_listbox.get(i) for i in self._word_listbox.curselection()]
        self._selected_word_cols = selected if selected else []
        self._refresh_table()
        shown = ", ".join(selected) if selected else "none"
        self._status_set(f"Word columns visible: {shown}.", ok=True)

    def _reset_word_cols(self) -> None:
        if self._data.df is None:
            return
        self._word_listbox.selection_clear(0, "end")
        self._selected_word_cols = None
        self._refresh_table()
        self._status_set("Word columns reset — showing all.", ok=True)



# ─── Entry Point ──────────────────────────────────────────────────────────────

if __name__ == "__main__":
    app = App()
    app.mainloop()
