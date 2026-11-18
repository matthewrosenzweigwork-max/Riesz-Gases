import HRS.MS.MovAdjTie

/-!
# S6.7 nonlinear row (packet N1): shrinking the constants of `MovNonlinearConclusion`

Namespace `HRS.MS.MovAdj`, helpers `s67_`.  Infrastructure for the supplement row `S:W:lem:r2mov-global-adjoint`; not a manuscript row.

`s67_shrink`: if `MovNonlinearConclusion .. εstar r c₀ c C` holds (`C > 0`), then for every `r' ∈ (0, r]` there is
`ε' ∈ (0, εstar]` with `MovNonlinearConclusion .. ε' r' c c C` (the rate `c₀` of the class is replaced by the decay rate `c`
of the decay bounds, the radius by `r'`).  Use: the global adjoint estimate needs the radius of the class to be small.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovAdj

open HRS HRS.Whole

variable {d : ℕ}

theorem MovDecayBounds.mono_amp {s q β : ℝ} {ρ₀ : Euc d → ℝ} {j m : ℕ} {c C K K' : ℝ}
    {ρ : ℝ → Euc d → ℝ} (h : MovDecayBounds d s q β ρ₀ j m c C K ρ) (hC : 0 ≤ C) (hK : K ≤ K') :
    MovDecayBounds d s q β ρ₀ j m c C K' ρ := by
  intro t ht
  obtain ⟨⟨h1, h2⟩, h3, h4, h5⟩ := h t ht
  have hmul : C * K * Real.exp (-c * t) ≤ C * K' * Real.exp (-c * t) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hK hC) (Real.exp_pos _).le
  exact ⟨⟨h1, h2.trans hmul⟩, h3, h4, h5.trans (ENNReal.ofReal_le_ofReal hmul)⟩

theorem s67_shrink {s q β : ℝ} {ρ₀ : Euc d → ℝ} {j m : ℕ} {εstar r c₀ c C : ℝ}
    (h : MovNonlinearConclusion d s q β ρ₀ j m εstar r c₀ c C) (hC : 0 < C) (hε : 0 < εstar)
    {r' : ℝ} (hr'0 : 0 < r') (hr' : r' ≤ r) :
    ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ εstar ∧ MovNonlinearConclusion d s q β ρ₀ j m ε' r' c c C := by
  refine ⟨min εstar (r' / C), lt_min hε (div_pos hr'0 hC), min_le_left _ _, ?_⟩
  intro f0 hf0
  have hsm : movInitialNorm ρ₀ j m f0 ≤ min εstar (r' / C) := hf0.small
  have hf0' : MovInitialClass ρ₀ j m εstar f0 :=
    ⟨hf0.cb, hf0.osc, hf0.mean, hsm.trans (min_le_left _ _)⟩
  obtain ⟨ρ, hρ, hpos, hratio, hdec1, hdec2, hint, huniq⟩ := h f0 hf0'
  refine ⟨ρ, ⟨hρ.solution, hρ.init, fun t ht => ⟨(hdec2 t ht).1.1, ?_⟩, hρ.cont, hρ.regular⟩, hpos, hratio,
    MovDecayBounds.mono_amp hdec2 hC.le hsm, hdec2, hint, fun ρ' hρ' t ht => huniq ρ' (hρ'.mono_radius hr') t ht⟩
  · have h1 := (hdec2 t ht).1.2
    refine h1.trans ?_
    have h2 : C * movInitialNorm ρ₀ j m f0 ≤ r' := by
      calc C * movInitialNorm ρ₀ j m f0 ≤ C * (r' / C) :=
            mul_le_mul_of_nonneg_left (hsm.trans (min_le_right _ _)) hC.le
        _ = r' := by field_simp
    exact mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le

end HRS.MS.MovAdj
