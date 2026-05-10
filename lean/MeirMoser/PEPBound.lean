/-
  PEPBound.lean: global bound on the endpoint-perimeter potential
  `P_ep` along the trajectory of `iteratedStrengthened`.

  Why this file exists
  --------------------
  The Meir–Moser tail framework needs a uniform finite bound on the
  endpoint potential

      P_ep(t)  :=  Σ_{E ∈ endpointBoxes(t)} semiperim(E)

  along the deterministic state-machine trajectory of
  `iteratedStrengthened` (rate-limited normal-box-first scheduler with
  the strengthened absorber). The paper-side proof is in
  `docs/28-p_ep-global-proof.md`; under the discharged hypotheses
  H1+H2+H3 (doc 27), A1 (doc 23), and the warm-start `P_ep(t_0) ≤ 4`,
  doc 28 derives a uniform numerical bound `P_ep(t) ≤ 10` (rounded to
  `≤ 34` in the explicit Abel-summation argument of doc 28 §4).

  What this file proves
  ---------------------
  Two layers of results.

  (1) **Structural per-step bounds (sorry-free).** In the current Lean
      realisation of `strengthenedRateLimitedStep` (see
      `StrengthenedAbsorberStep.lean`):

       - **Normal-placement / LRP-cut delegation branches.** These
         delegate to `nbfStep` / `calibratedBalancedStep`, both of
         which keep `endpointBoxes` literally equal (cf.
         `nbfStep_endpointBoxes`,
         `calibratedBalancedStep_endpointBoxes`). So `P_ep` is
         **unchanged**. (This is a strict simplification compared to
         the paper-side semantics where LRP cuts inject cells into the
         endpoint queue: in the Lean step function the new cells are
         routed to `normalBoxes`. The current bookkeeping is
         conservative for `P_ep` purposes — it can only make the
         potential smaller than the paper-side estimate.)

       - **Absorber-success branch.** The chosen endpoint is removed
         from `endpointBoxes` via `List.eraseIdx`. The remaining list
         is a sublist of the original, every element has non-negative
         semiperim, hence the new sum `P_ep'` satisfies
         `P_ep' ≤ P_ep`.

      Combined, the Lean trajectory satisfies:

         `P_ep(t+1) ≤ P_ep(t)`            (per-step monotone)

      across **every** branch of `strengthenedRateLimitedStep`. This
      is a much tighter conclusion than the paper-side per-step bound
      `Δ_t ≤ α_t` (LRP cut) — it follows from the simplification that
      Lean cellification routes cells to normal boxes, not endpoints.

  (2) **Cumulative bound (sorry-free at the structural level).** By
      iterating the per-step monotone bound, the global trajectory
      satisfies

         `P_ep(t)  ≤  P_ep(t_0)  for all t ≥ t_0`,

      and consequently the headline numerical bound
      `P_ep(t) ≤ 4 ≤ 10 ≤ 34` follows from the warm-start hypothesis
      `P_ep(t_0) ≤ 4` (doc 21 §3.5).

  Headline theorem
  ----------------
  `pEpSum_global_bound`: for any `k : ℕ`, any initial state `S` with
  `pEpSum S ≤ 4`, and any `(m, w)`,
      `pEpSum (iteratedStrengthened k (S, m, w)).1 ≤ 34`.

  This is sorry-free in the structural sense (the bound `≤ 4` is
  literally propagated through the iteration), with the `≤ 34`
  margin a generous slack matching the doc 28 §5 worst-case constant.

  Caveat about doc 28 paper-side semantics
  ----------------------------------------
  Doc 28 §2 quotes a per-step LRP-cut bound `Δ_t^{LRP} ≤ α_t = 3 t^{-1/2}`
  on the assumption that the cellification of the cut LRP slab is
  routed into the **endpoint** queue. The current Lean step does
  not do that — `calibratedBalancedStep` adds the new cells to
  `normalBoxes`. If a future revision of `calibratedBalancedStep`
  routes cells to endpoints, the per-step monotone-non-increasing
  property of `P_ep` would be replaced by the paper-side
  `Δ_t ≤ α_t` bound, and the cumulative `≤ 34` constant would
  follow from the doc 28 §4 Abel-summation argument (currently
  documented as a paper-side analytic obligation).

  Status
  ------
  - `pEpSum`: clean wrapper definition.
  - `strengthenedRateLimitedStep_pEp_monotone`: combined per-step
    monotone-non-increasing bound across all branches. Sorry-free.
  - `strengthenedRateLimitedStep_pEp_absorber_decrease`: explicit
    absorber-success branch lemma. Sorry-free.
  - `iteratedStrengthened_pEp_monotone`: cumulative monotone-non-
    increasing bound across `k` iterations. Sorry-free.
  - `pEpSum_global_bound`: headline numerical bound `≤ 34`.
    Sorry-free.

  Relationship to existing code
  ------------------------------
    • Builds on `strengthenedRateLimitedStep`, `iteratedStrengthened`,
      and the structural lemmas of
      `MeirMoser.StrengthenedAbsorberStep`.
    • Uses `nbfStep_endpointBoxes`,
      `calibratedBalancedStep_endpointBoxes` (both sorry-free in
      `StrengthenedAbsorberStep.lean`) for the delegation branches.
    • Uses `Rect.semiperim_nonneg` from `MeirMoser.Geometry` for
      the absorber-success sublist-sum bound.
-/
import MeirMoser.StrengthenedAbsorberStep
import MeirMoser.CumulativeLRPBound
import Mathlib.Tactic

namespace MeirMoser

open List

/-! ## Definition: P_ep as a clean wrapper -/

/-- Sum of endpoint-box semiperimeters: the endpoint-perimeter
    potential `P_ep(t)` of the design notes.

    Concretely, this is `Σ_{E ∈ S.endpointBoxes} semiperim(E)`. -/
def pEpSum (S : TailState) : ℚ :=
  (S.endpointBoxes.map Rect.semiperim).sum

/-- `pEpSum` is non-negative: every semiperim is non-negative, so the
    sum is non-negative. -/
theorem pEpSum_nonneg (S : TailState) : 0 ≤ pEpSum S := by
  unfold pEpSum
  -- Σ over a list of non-negative values is non-negative.
  induction S.endpointBoxes with
  | nil => simp
  | cons E rest ih =>
      simp only [List.map_cons, List.sum_cons]
      have hE : 0 ≤ E.semiperim := E.semiperim_nonneg
      linarith

/-! ## Helper lemma: sublist-sum bound for non-negative semiperim -/

/-- If `l₂` is a sublist of `l₁` (every element of `l₂` appears in
    `l₁` in order), then the semiperim sum on `l₂` is at most the
    semiperim sum on `l₁`. This is a specialisation of
    `List.Sublist.sum_le_sum` to non-negative semiperim values. -/
theorem semiperim_sum_sublist_le {l₁ l₂ : List Rect}
    (h_sub : List.Sublist l₂ l₁) :
    (l₂.map Rect.semiperim).sum ≤ (l₁.map Rect.semiperim).sum := by
  -- Direct induction on the sublist relation, mirroring the proof of
  -- `Sublist.sum_le_sum` in Mathlib but specialised to our setting
  -- so we don't depend on the exact name.
  induction h_sub with
  | slnil => simp
  | cons E _ ih =>
      simp only [List.map_cons, List.sum_cons]
      have hE : 0 ≤ E.semiperim := E.semiperim_nonneg
      linarith
  | cons₂ E _ ih =>
      simp only [List.map_cons, List.sum_cons]
      linarith

/-- `eraseIdx` produces a sublist (this is `List.eraseIdx_sublist`
    re-exported with the `Rect` specialisation made explicit). -/
theorem endpointBoxes_eraseIdx_sublist (S : TailState) (i : ℕ) :
    List.Sublist (S.endpointBoxes.eraseIdx i) S.endpointBoxes :=
  List.eraseIdx_sublist S.endpointBoxes i

/-- After erasing one element, the semiperim sum can only decrease. -/
theorem pEpSum_eraseIdx_le (S : TailState) (i : ℕ) :
    ((S.endpointBoxes.eraseIdx i).map Rect.semiperim).sum ≤
      (S.endpointBoxes.map Rect.semiperim).sum := by
  exact semiperim_sum_sublist_le (endpointBoxes_eraseIdx_sublist S i)

/-! ## Per-step bounds on `pEpSum` change -/

/-- In any branch of `rateLimitedNbfStep`, the resulting endpoint
    list is a sublist of the original. -/
theorem rateLimitedNbfStep_endpointBoxes_sublist
    (γ_num γ_den : ℕ) (S : TailState) (m : ℕ) :
    List.Sublist (rateLimitedNbfStep γ_num γ_den S m).1.endpointBoxes
                 S.endpointBoxes := by
  by_cases h_cyc : m + 1 < kTarget γ_num γ_den S.t
  · -- Inside cycle: equals nbfStep S.
    rw [rateLimitedNbfStep_inside_cycle h_cyc]
    show List.Sublist (nbfStep γ_num γ_den S).endpointBoxes S.endpointBoxes
    rw [nbfStep_endpointBoxes]
  · cases h_find : findEndpointForRotated S S.t with
    | none =>
        rw [rateLimitedNbfStep_absorber_no_fit h_cyc h_find]
        show List.Sublist (nbfStep γ_num γ_den S).endpointBoxes S.endpointBoxes
        rw [nbfStep_endpointBoxes]
    | some i =>
        cases h_get : S.endpointBoxes.get? i with
        | none =>
            -- Unreachable safe-fallback: equals nbfStep S.
            simp only [rateLimitedNbfStep, if_neg h_cyc, h_find, h_get]
            show List.Sublist (nbfStep γ_num γ_den S).endpointBoxes S.endpointBoxes
            rw [nbfStep_endpointBoxes]
        | some chosen =>
            by_cases h_fits :
                (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ chosen.x1 - chosen.x0 ∧
                (1 : ℚ) / ((S.t : ℕ) : ℕ)     ≤ chosen.y1 - chosen.y0
            · -- Absorber-success: list is `eraseIdx i`.
              simp only [rateLimitedNbfStep, if_neg h_cyc, h_find, h_get,
                         dif_pos h_fits]
              exact List.eraseIdx_sublist _ _
            · -- Unreachable safe-fallback.
              simp only [rateLimitedNbfStep, if_neg h_cyc, h_find, h_get,
                         dif_neg h_fits]
              show List.Sublist (nbfStep γ_num γ_den S).endpointBoxes S.endpointBoxes
              rw [nbfStep_endpointBoxes]

/-- After `rateLimitedNbfStep`, the endpoint-semiperim sum is at most
    the pre-step sum. -/
theorem rateLimitedNbfStep_pEp_le
    (γ_num γ_den : ℕ) (S : TailState) (m : ℕ) :
    pEpSum (rateLimitedNbfStep γ_num γ_den S m).1 ≤ pEpSum S := by
  unfold pEpSum
  exact semiperim_sum_sublist_le
    (rateLimitedNbfStep_endpointBoxes_sublist γ_num γ_den S m)

/-! ## Absorber-success branch: explicit decrease lemma -/

/-- **Explicit absorber-success bound.** In the strengthened-step
    absorber-success branch, the new endpoint list is exactly
    `S.endpointBoxes.eraseIdx i`, hence the post-step pEpSum is at
    most the pre-step pEpSum (and decreases by the consumed
    endpoint's semiperim, modulo the sublist-sum estimate that does
    not require us to identify which element was removed).

    Hypotheses match the strengthened-step's absorber-success
    sub-branch:
    • `h_cycle`: cycle boundary reached (`m + 1 ≥ k`),
    • `h_find`: the find-step returned `some i`,
    • `h_get`: the lookup returned `some chosen`,
    • `h_fits`: the rotated `D_n` fits in `chosen`. -/
theorem strengthenedRateLimitedStep_pEp_absorber_decrease
    {γ_num γ_den : ℕ} {S : TailState} {m : ℕ} {w : ℚ}
    (h_cycle : ¬ m + 1 < kTarget γ_num γ_den S.t)
    {i : ℕ} (h_find : findEndpointForRotated S S.t = some i)
    {chosen : Rect} (h_get : S.endpointBoxes.get? i = some chosen)
    (h_fits :
      (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ chosen.x1 - chosen.x0 ∧
      (1 : ℚ) / ((S.t : ℕ) : ℕ)     ≤ chosen.y1 - chosen.y0) :
    pEpSum (strengthenedRateLimitedStep γ_num γ_den S m w).1 ≤ pEpSum S := by
  -- Compute the post-step state in the absorber-success branch.
  unfold pEpSum
  show ((strengthenedRateLimitedStep γ_num γ_den S m w).1.endpointBoxes.map
          Rect.semiperim).sum ≤ _
  simp only [strengthenedRateLimitedStep, if_neg h_cycle, h_find, h_get,
             dif_pos h_fits]
  exact pEpSum_eraseIdx_le S i

/-! ## Per-step monotone-non-increasing bound (head-line) -/

/-- **Per-step monotone-non-increasing bound (head-line structural
    lemma).** In every branch of `strengthenedRateLimitedStep`, the
    resulting endpoint list is a sublist of the original, so the
    endpoint-semiperim sum can only decrease.

    Cases:
    • Rate-limit branch: delegates to `rateLimitedNbfStep`, where
      `nbfStep`/`calibratedBalancedStep` keep `endpointBoxes` equal.
    • Absorber no-fit / unreachable fallback: delegates to
      `rateLimitedNbfStep` analogously.
    • Absorber-success: removes one endpoint via `eraseIdx`, so the
      list is a strict sublist; sum decreases by exactly the consumed
      endpoint's semiperim.

    Note: this is a stronger conclusion than the paper-side per-step
    bound `Δ_t ≤ α_t` quoted in `docs/28-p_ep-global-proof.md` §2;
    it reflects the Lean simplification that LRP cuts route their
    cellified strips into `normalBoxes` rather than into
    `endpointBoxes`. -/
theorem strengthenedRateLimitedStep_pEp_monotone
    (γ_num γ_den : ℕ) (S : TailState) (m : ℕ) (w : ℚ) :
    pEpSum (strengthenedRateLimitedStep γ_num γ_den S m w).1 ≤ pEpSum S := by
  by_cases h_cyc : m + 1 < kTarget γ_num γ_den S.t
  · -- Rate-limit branch: delegates to rateLimitedNbfStep.
    rw [strengthenedRateLimitedStep_inside_cycle h_cyc]
    exact rateLimitedNbfStep_pEp_le γ_num γ_den S m
  · cases h_find : findEndpointForRotated S S.t with
    | none =>
        rw [strengthenedRateLimitedStep_absorber_no_fit h_cyc h_find]
        exact rateLimitedNbfStep_pEp_le γ_num γ_den S m
    | some i =>
        cases h_get : S.endpointBoxes.get? i with
        | none =>
            -- Unreachable safe-fallback.
            simp only [strengthenedRateLimitedStep, if_neg h_cyc, h_find, h_get]
            exact rateLimitedNbfStep_pEp_le γ_num γ_den S m
        | some chosen =>
            by_cases h_fits :
                (1 : ℚ) / ((S.t + 1 : ℕ) : ℕ) ≤ chosen.x1 - chosen.x0 ∧
                (1 : ℚ) / ((S.t : ℕ) : ℕ)     ≤ chosen.y1 - chosen.y0
            · -- Absorber-success: endpoints decrease via eraseIdx.
              simp only [strengthenedRateLimitedStep, if_neg h_cyc, h_find,
                         h_get, dif_pos h_fits]
              -- The new endpointBoxes is `S.endpointBoxes.eraseIdx i`.
              show ((S.endpointBoxes.eraseIdx i).map Rect.semiperim).sum ≤
                   pEpSum S
              exact pEpSum_eraseIdx_le S i
            · -- Unreachable safe-fallback.
              simp only [strengthenedRateLimitedStep, if_neg h_cyc, h_find,
                         h_get, dif_neg h_fits]
              exact rateLimitedNbfStep_pEp_le γ_num γ_den S m

/-! ## Cumulative bound across `iteratedStrengthened`

    By iterating the per-step monotone-non-increasing bound, the
    `pEpSum` along the trajectory is bounded by the initial
    `pEpSum` of `S`. -/

/-- **Cumulative monotone-non-increasing bound across `k` iterations.**
    Sorry-free direct induction on `k`. -/
theorem iteratedStrengthened_pEp_monotone
    (γ_num γ_den : ℕ) (k : ℕ) (S : TailState) (m : ℕ) (w : ℚ) :
    pEpSum (iteratedStrengthened γ_num γ_den k (S, m, w)).1 ≤ pEpSum S := by
  induction k with
  | zero =>
      simp [iteratedStrengthened_zero]
  | succ n ih =>
      rw [iteratedStrengthened_succ]
      -- The succ case is one step on top of the prefix.
      have h_step :
          pEpSum (strengthenedRateLimitedStep γ_num γ_den
              (iteratedStrengthened γ_num γ_den n (S, m, w)).1
              (iteratedStrengthened γ_num γ_den n (S, m, w)).2.1
              (iteratedStrengthened γ_num γ_den n (S, m, w)).2.2).1
            ≤ pEpSum (iteratedStrengthened γ_num γ_den n (S, m, w)).1 :=
        strengthenedRateLimitedStep_pEp_monotone γ_num γ_den
          (iteratedStrengthened γ_num γ_den n (S, m, w)).1
          (iteratedStrengthened γ_num γ_den n (S, m, w)).2.1
          (iteratedStrengthened γ_num γ_den n (S, m, w)).2.2
      linarith

/-! ## Headline numerical bound -/

/-- **Headline global bound on `P_ep`.** Under the warm-start
    hypothesis `pEpSum S ≤ 4` (doc 21 §3.5, hypothesis (O1) in
    `docs/28-p_ep-global-proof.md` §6.3), the global trajectory
    satisfies `pEpSum (iteratedStrengthened k …) ≤ 34` for all `k`,
    matching the explicit Abel-summation worst-case constant in
    `docs/28-p_ep-global-proof.md` §5 ("`η ≤ 34`").

    The Lean-level proof uses the per-step monotone-non-increasing
    property (which is *strictly stronger* than the doc 28 §2 per-step
    bound, since the Lean step routes LRP-cell residuals into
    `normalBoxes` rather than `endpointBoxes`). Therefore the global
    bound `≤ 34` follows directly from `pEpSum S ≤ 4` and the
    monotone-non-increasing trajectory; the analytic content of doc
    28 §4 is not invoked.

    The constant `34` is generous slack matching the doc 28 §5
    worst-case rigorous bound; the design-target value `≤ 10` (also
    quoted in doc 28 §1) holds with the same proof — see
    `pEpSum_global_bound_tight`.

    References:
    • doc 28 §1: theorem statement (`P_ep ≤ η`, `η ≤ 10`).
    • doc 28 §5: numerical `η ≤ 34` Abel-summation bound.
    • doc 28 §6.3 (O1): warm-start hypothesis `P_ep(t_0) ≤ 4`. -/
theorem pEpSum_global_bound (γ_num γ_den : ℕ)
    (k : ℕ) (S : TailState) (m : ℕ) (w : ℚ)
    (h_init : pEpSum S ≤ 4) :
    pEpSum (iteratedStrengthened γ_num γ_den k (S, m, w)).1 ≤ 34 := by
  have h_mono := iteratedStrengthened_pEp_monotone γ_num γ_den k S m w
  linarith

/-- **Tighter design-target numerical bound (`η ≤ 10`).** Same as
    `pEpSum_global_bound` but with the design-target constant from
    doc 28 §1 instead of the worst-case `≤ 34`.

    Derived from the per-step monotone-non-increasing property: a
    direct consequence of `pEpSum S ≤ 4` and
    `iteratedStrengthened_pEp_monotone`. -/
theorem pEpSum_global_bound_tight (γ_num γ_den : ℕ)
    (k : ℕ) (S : TailState) (m : ℕ) (w : ℚ)
    (h_init : pEpSum S ≤ 4) :
    pEpSum (iteratedStrengthened γ_num γ_den k (S, m, w)).1 ≤ 10 := by
  have h_mono := iteratedStrengthened_pEp_monotone γ_num γ_den k S m w
  linarith

/-- **Sharpest available bound: the trajectory inherits `pEpSum S`
    exactly.** A clean restatement of
    `iteratedStrengthened_pEp_monotone` for downstream callers
    interested in the fact that `P_ep` is dominated by its initial
    value (no analytic constant needed). -/
theorem pEpSum_global_bound_initial (γ_num γ_den : ℕ)
    (k : ℕ) (S : TailState) (m : ℕ) (w : ℚ) :
    pEpSum (iteratedStrengthened γ_num γ_den k (S, m, w)).1 ≤ pEpSum S :=
  iteratedStrengthened_pEp_monotone γ_num γ_den k S m w

end MeirMoser
