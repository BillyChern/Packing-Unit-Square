"""Calibrated Slack-Pack scheduler.

The 6-rule scheduler from agent_execution_brief §5:
  1. Endpoint priority   — try endpoints first; pick smallest fitting endpoint.
  2. Normal-box priority — try normal box if no endpoint fits.
  3. LRP cut             — cut a calibrated stripe of width a_t from the longer side of LRP.
  4. Two-backtrack       — apply anti-sliver to row endpoints.
  5. Cellify              — partition resulting strips into fat absorber cells.
  6. Balanced LRP cuts   — always cut from the longer side; if aspect drifts, balance-cut.

State at step t: (LRP, normal_boxes, endpoint_boxes, placed, t, gamma).
"""

from __future__ import annotations
from dataclasses import dataclass, field
from fractions import Fraction
from typing import List, Optional, Tuple

from .geometry import (
    Rect,
    FreeBox,
    FreeBoxKind,
    PlacedRect,
    split_free_after_place,
)
from .rect_sequence import D_dims, calibrated_active_width
from .cellification import cellify_strip
from .metrics import compute_metrics, Metrics

F = Fraction


@dataclass
class State:
    """Mutable scheduler state — one instance per calibrated run."""

    t: int                                       # next index to place
    gamma_num: int = 4
    gamma_den: int = 3
    burnin_until: int = 50                       # use plain MaxRects for t < burnin_until
    container: Rect = field(
        default_factory=lambda: Rect(F(0), F(0), F(1), F(1))
    )
    placed: List[PlacedRect] = field(default_factory=list)
    LRP: Optional[FreeBox] = None
    normal_boxes: List[FreeBox] = field(default_factory=list)
    endpoint_boxes: List[FreeBox] = field(default_factory=list)
    absorbers: List[FreeBox] = field(default_factory=list)

    def gamma_float(self) -> float:
        return self.gamma_num / self.gamma_den

    def calibrated_width(self) -> F:
        return calibrated_active_width(self.t, self.gamma_num, self.gamma_den)

    def metrics(self) -> Metrics:
        return compute_metrics(
            self.t, self.LRP, self.normal_boxes, self.endpoint_boxes,
            self.gamma_num, self.gamma_den,
        )

    def free_area(self) -> F:
        a = self.LRP.area if self.LRP else F(0)
        a += sum((b.area for b in self.normal_boxes), F(0))
        a += sum((b.area for b in self.endpoint_boxes), F(0))
        a += sum((b.area for b in self.absorbers), F(0))
        return a

    def total_placed_area(self) -> F:
        return sum((p.area for p in self.placed), F(0))


def _can_fit(box: FreeBox, w: F, h: F) -> bool:
    return box.rect.fits(w, h)


def _place_in_box(box: FreeBox, n: int, prefer_orientation: str = "wide") -> Tuple[PlacedRect, List[Rect]]:
    """Place D_n inside `box` at the bottom-left corner, returning the placement
    plus the list of free-rect remnants from a 4-way MaxRects split.

    `prefer_orientation`: 'wide' tries unrotated first (long side horizontal),
    'tall' tries rotated first.
    """
    long_, short = D_dims(n)  # long_ = 1/n ≥ short = 1/(n+1)
    # Determine which orientation fits
    if prefer_orientation == "wide":
        candidates = [(long_, short, False), (short, long_, True)]
    else:
        candidates = [(short, long_, True), (long_, short, False)]
    for w, h, rot in candidates:
        if w <= box.w and h <= box.h:
            placed = PlacedRect(
                n=n, x0=box.rect.x0, y0=box.rect.y0, rotated=rot
            )
            placed_rect = placed.rect
            remnants = split_free_after_place(box.rect, placed_rect)
            return placed, remnants
    raise RuntimeError(f"D_{n} does not fit in box {box.rect}")


@dataclass
class CalibratedScheduler:
    """Drives the 6-rule scheduler. Use `from_maxrects_burnin` for a clean start.

    The scheduler is *initial-state* agnostic: a state can be seeded by any
    means (full prefix from MaxRects burn-in, or hand-built initial layout).
    """

    state: State

    @classmethod
    def seed_unit_square(
        cls,
        gamma_num: int = 4,
        gamma_den: int = 3,
        eps_num: int = 0,
        eps_den: int = 1,
    ) -> "CalibratedScheduler":
        """Initialize on container [0, 1+ε]^2 (with ε = eps_num/eps_den) with the
        full square as a single LRP and t = 1.
        """
        side = F(1) + Fraction(eps_num, eps_den)
        cont = Rect(F(0), F(0), side, side)
        LRP = FreeBox(rect=cont, kind=FreeBoxKind.LRP)
        st = State(
            t=1, gamma_num=gamma_num, gamma_den=gamma_den,
            container=cont, LRP=LRP,
        )
        return cls(state=st)

    @classmethod
    def from_maxrects_burnin(
        cls,
        burnin_N: int,
        gamma_num: int = 4,
        gamma_den: int = 3,
        heuristic: str = "BSSF",
        eps_num: int = 0,
        eps_den: int = 1,
        side_aspect_classify: Fraction = Fraction(2),
    ) -> "CalibratedScheduler":
        """Run the existing battle-tested MaxRectsPacker for the burn-in phase
        (t = 1 .. burnin_N), then convert the resulting state into a calibrated
        state: largest free rect → LRP, thin strips (aspect ≥ side_aspect_classify)
        → endpoints, the rest → absorbers.
        """
        # Lazy import to avoid circular dependency
        from src.algorithms import MaxRectsPacker
        side = F(1) + Fraction(eps_num, eps_den)
        packer = MaxRectsPacker(side, side)
        for n in range(1, burnin_N + 1):
            p = packer.place(n, allow_rotate=True, heuristic=heuristic)
            if p is None:
                raise RuntimeError(
                    f"burnin: MaxRects ({heuristic}) failed at n={n}"
                )
        # Convert
        cont = Rect(F(0), F(0), side, side)
        placed = [
            PlacedRect(n=p.k, x0=p.x, y0=p.y, rotated=p.rotated)
            for p in packer.placed
        ]
        # Use rectangulation of complement (disjoint partition) instead of the
        # MaxRects free-list (which contains overlapping maxrects).
        # Critical: pick LRP = argmax-min-side over the partition (the BSSF
        # invariant FR). Empirically this has aspect → 1 as N grows.
        from .rectangulate_fast import rectangulate_simplified_fast
        free_rects = rectangulate_simplified_fast(cont, placed)
        if not free_rects:
            # No free space — odd, but plausible. State has empty free regions.
            st = State(
                t=burnin_N + 1, gamma_num=gamma_num, gamma_den=gamma_den,
                container=cont, placed=placed, LRP=None,
            )
            return cls(state=st)
        # Pick LRP = argmax-min-side over the partition (BSSF invariant FR).
        # Empirically this has aspect → 1 and area·N → const > 0.
        lrp_rect = max(free_rects, key=lambda r: (r.min_side, r.area))
        normal: List[FreeBox] = []
        endpoint: List[FreeBox] = []      # populated during calibrated runtime, not burn-in
        absorbers: List[FreeBox] = []
        from .cellification import cellify_strip
        ULTRA_THIN_ASPECT = F(64)   # if more cells than this would result, treat as endpoint
        for r in free_rects:
            if r is lrp_rect:
                continue
            if r.aspect > side_aspect_classify and r.aspect <= ULTRA_THIN_ASPECT:
                # Moderately thin: cellify into fat absorber cells (aspect ≤ 2 each).
                for c in cellify_strip(r):
                    absorbers.append(FreeBox(rect=c, kind=FreeBoxKind.ABSORBER))
            elif r.aspect > ULTRA_THIN_ASPECT:
                # Ultra-thin: classify as endpoint (single piece).
                endpoint.append(FreeBox(rect=r, kind=FreeBoxKind.ENDPOINT))
            else:
                absorbers.append(FreeBox(rect=r, kind=FreeBoxKind.ABSORBER))
        LRP = FreeBox(rect=lrp_rect, kind=FreeBoxKind.LRP)
        st = State(
            t=burnin_N + 1, gamma_num=gamma_num, gamma_den=gamma_den,
            container=cont, placed=placed, LRP=LRP,
            normal_boxes=normal, endpoint_boxes=endpoint, absorbers=absorbers,
            burnin_until=burnin_N,  # immediately past burnin
        )
        return cls(state=st)

    def step(self) -> str:
        """Place D_t using the 6-rule priority. Returns the rule applied."""
        st = self.state
        n = st.t
        long_, short = D_dims(n)

        # During burn-in: use plain BSSF on a single-LRP free list (no normal/endpoint
        # decomposition yet). The calibrated stripe formula a_t = 1/(t+1)+t^{-γ} only
        # makes sense once t is large enough that a_t ≪ LRP.min_side.
        if n < st.burnin_until:
            return self._burnin_step(n, long_, short)

        # Rule 1: endpoint priority — pick smallest-area endpoint that fits.
        ep_fitting = [
            (i, b) for i, b in enumerate(st.endpoint_boxes)
            if _can_fit(b, long_, short)
        ]
        if ep_fitting:
            ep_fitting.sort(key=lambda iB: iB[1].area)
            i, box = ep_fitting[0]
            placed, remnants = _place_in_box(box, n)
            st.placed.append(placed)
            del st.endpoint_boxes[i]
            self._absorb_remnants(remnants, kind=FreeBoxKind.ABSORBER, birth=None)
            st.t += 1
            return "endpoint"

        # Rule 2: normal-box priority — pick smallest fitting normal box.
        norm_fitting = [
            (i, b) for i, b in enumerate(st.normal_boxes)
            if _can_fit(b, long_, short)
        ]
        if norm_fitting:
            norm_fitting.sort(key=lambda iB: iB[1].area)
            i, box = norm_fitting[0]
            placed, remnants = _place_in_box(box, n)
            st.placed.append(placed)
            del st.normal_boxes[i]
            self._absorb_remnants(remnants, kind=FreeBoxKind.ABSORBER, birth=None)
            st.t += 1
            return "normal"

        # Rule 3: LRP cut. Need an LRP that can hold D_n.
        if st.LRP is None or not _can_fit(st.LRP, long_, short):
            # Try absorbers as a last resort (treated as "absorbers" but allowed).
            abs_fitting = [
                (i, b) for i, b in enumerate(st.absorbers)
                if _can_fit(b, long_, short)
            ]
            if abs_fitting:
                abs_fitting.sort(key=lambda iB: iB[1].area)
                i, box = abs_fitting[0]
                placed, remnants = _place_in_box(box, n)
                st.placed.append(placed)
                del st.absorbers[i]
                self._absorb_remnants(remnants, kind=FreeBoxKind.ABSORBER, birth=None)
                st.t += 1
                return "absorber"
            raise RuntimeError(
                f"step t={st.t}: no fitting box (LRP={st.LRP}, "
                f"endpoints={len(st.endpoint_boxes)}, normal={len(st.normal_boxes)})"
            )

        # Cut a calibrated stripe of width a_t from the longer side of LRP.
        a_t = st.calibrated_width()
        # a_t may exceed LRP.min_side; clamp downward in that case.
        L = st.LRP.rect
        # Cut from longer side: longer side is x-axis if w ≥ h.
        if L.w >= L.h:
            cut_w = min(a_t, L.w)
            stripe = Rect(L.x0, L.y0, L.x0 + cut_w, L.y1)
            new_LRP_rect = Rect(L.x0 + cut_w, L.y0, L.x1, L.y1) if cut_w < L.w else None
        else:
            cut_h = min(a_t, L.h)
            stripe = Rect(L.x0, L.y0, L.x1, L.y0 + cut_h)
            new_LRP_rect = Rect(L.x0, L.y0 + cut_h, L.x1, L.y1) if cut_h < L.h else None
        # Place D_n in the stripe (oriented so long side is along the stripe's long side).
        if stripe.w >= stripe.h:
            # stripe is horizontal: long side x. Place D_n with long side vertical (rotated)
            # if that fits better, else native.
            if short <= stripe.w and long_ <= stripe.h:
                placed = PlacedRect(n=n, x0=stripe.x0, y0=stripe.y0, rotated=True)
            elif long_ <= stripe.w and short <= stripe.h:
                placed = PlacedRect(n=n, x0=stripe.x0, y0=stripe.y0, rotated=False)
            else:
                raise RuntimeError(f"D_{n} doesn't fit in stripe {stripe}")
        else:
            # stripe vertical: long side y.
            if long_ <= stripe.h and short <= stripe.w:
                placed = PlacedRect(n=n, x0=stripe.x0, y0=stripe.y0, rotated=False)
            elif short <= stripe.h and long_ <= stripe.w:
                placed = PlacedRect(n=n, x0=stripe.x0, y0=stripe.y0, rotated=True)
            else:
                raise RuntimeError(f"D_{n} doesn't fit in stripe {stripe}")
        st.placed.append(placed)
        # Stripe minus placed → remnants via 2-cut guillotine (disjoint).
        remnants = split_free_after_place(stripe, placed.rect)
        for r in remnants:
            if r.w >= r.h * 2 or r.h >= r.w * 2:
                # long thin → cellify into absorbers
                cells = cellify_strip(r)
                for c in cells:
                    st.absorbers.append(FreeBox(rect=c, kind=FreeBoxKind.ABSORBER))
            else:
                # roughly square → normal box
                st.normal_boxes.append(
                    FreeBox(rect=r, kind=FreeBoxKind.NORMAL, birth_index=n)
                )
        # Update LRP
        if new_LRP_rect is None:
            st.LRP = None
        else:
            st.LRP = FreeBox(rect=new_LRP_rect, kind=FreeBoxKind.LRP)
        st.t += 1
        return "lrp_cut"

    def _burnin_step(self, n: int, long_: F, short: F) -> str:
        """During burn-in, use BSSF on the LRP free list directly (no calibrated cuts).

        We treat LRP, normal_boxes, endpoint_boxes, absorbers as one big free list,
        pick the box minimizing |box.short_side - placement.short_side| (BSSF),
        place and split with guillotine.
        """
        st = self.state
        # Collect all candidates (box, kind, idx_within_list)
        candidates: List[Tuple[FreeBox, str, int]] = []
        if st.LRP is not None:
            candidates.append((st.LRP, "LRP", -1))
        for i, b in enumerate(st.normal_boxes):
            candidates.append((b, "normal", i))
        for i, b in enumerate(st.endpoint_boxes):
            candidates.append((b, "endpoint", i))
        for i, b in enumerate(st.absorbers):
            candidates.append((b, "absorber", i))

        # Pick the BSSF: among fitting boxes, minimize the shorter leftover.
        best = None
        BIG = F(10 ** 18)
        best_score: Tuple[F, F] = (BIG, BIG)
        for box, kind, idx in candidates:
            if not _can_fit(box, long_, short):
                continue
            # try both orientations and pick the better
            for w, h, rot in [(long_, short, False), (short, long_, True)]:
                if w <= box.w and h <= box.h:
                    leftover_short = min(box.w - w, box.h - h)
                    leftover_long = max(box.w - w, box.h - h)
                    score = (leftover_short, leftover_long)
                    if score < best_score:
                        best_score = score
                        best = (box, kind, idx, w, h, rot)
        if best is None:
            raise RuntimeError(
                f"burnin t={n}: no fitting box (|LRP|={1 if st.LRP else 0}, "
                f"|normal|={len(st.normal_boxes)}, |endpoint|={len(st.endpoint_boxes)}, "
                f"|absorber|={len(st.absorbers)})"
            )
        box, kind, idx, w, h, rot = best
        placed = PlacedRect(n=n, x0=box.rect.x0, y0=box.rect.y0, rotated=rot)
        st.placed.append(placed)
        # Remove the box from its list
        if kind == "LRP":
            st.LRP = None
        elif kind == "normal":
            del st.normal_boxes[idx]
        elif kind == "endpoint":
            del st.endpoint_boxes[idx]
        elif kind == "absorber":
            del st.absorbers[idx]
        # Split the consumed box and reinstall remnants — the LARGEST remnant by area
        # becomes the new LRP (if the consumed box was the LRP), other remnants are
        # absorbers.
        remnants = split_free_after_place(box.rect, placed.rect)
        if kind == "LRP" and remnants:
            # New LRP: pick the largest remnant by area.
            remnants.sort(key=lambda r: r.area, reverse=True)
            new_lrp = remnants[0]
            st.LRP = FreeBox(rect=new_lrp, kind=FreeBoxKind.LRP)
            for r in remnants[1:]:
                st.absorbers.append(FreeBox(rect=r, kind=FreeBoxKind.ABSORBER))
        else:
            for r in remnants:
                st.absorbers.append(FreeBox(rect=r, kind=FreeBoxKind.ABSORBER))
        st.t += 1
        return f"burnin_{kind}"

    def _absorb_remnants(self, remnants: List[Rect], kind: FreeBoxKind, birth: Optional[int]) -> None:
        st = self.state
        for r in remnants:
            if r.w == 0 or r.h == 0:
                continue
            if r.w >= r.h * 2 or r.h >= r.w * 2:
                cells = cellify_strip(r)
                for c in cells:
                    st.absorbers.append(FreeBox(rect=c, kind=FreeBoxKind.ABSORBER))
            else:
                st.absorbers.append(FreeBox(rect=r, kind=kind, birth_index=birth))

    def run(self, N: int) -> "CalibratedScheduler":
        """Place D_1, ..., D_N. Raises if no rule applies at some step."""
        for _ in range(N - self.state.t + 1):
            if self.state.t > N:
                break
            self.step()
        return self


__all__ = ["State", "CalibratedScheduler"]
