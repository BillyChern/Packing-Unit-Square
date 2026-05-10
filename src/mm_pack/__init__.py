"""Calibrated Slack-Pack package for the Meir-Moser problem.

Implements the calibrated scheduler proposed in the project research notes,
with typed free-region decomposition (LRP / normal / endpoint / absorber),
two-backtrack anti-sliver, and exact-rational verification.
"""

from .geometry import Rect, PlacedRect, FreeBox, FreeBoxKind
from .rect_sequence import D_dims, D_area, tail_area
from .cellification import cellify_strip
from .two_backtrack import two_backtrack
from .calibrated_scheduler import State, CalibratedScheduler
from .metrics import Metrics
from .certificate import Certificate, write_certificate, read_certificate, write_lean_certificate
from .checker import check_certificate, CheckReport

__all__ = [
    "Rect",
    "PlacedRect",
    "FreeBox",
    "FreeBoxKind",
    "D_dims",
    "D_area",
    "tail_area",
    "cellify_strip",
    "two_backtrack",
    "State",
    "CalibratedScheduler",
    "Metrics",
    "Certificate",
    "write_certificate",
    "read_certificate",
    "write_lean_certificate",
    "check_certificate",
    "CheckReport",
]
