import HRS.MS.R26T8AP08c
import HRS.MS.R26T8AP10a15

/-!
# S8.2 T8A P08 (part d): pointwise bound of a conormal pair function
`r26t8a_f25_pt_bound`: `|F x y| ≤ A C w(x,y) (1 + |x-y|^(-s))` for `x ≠ y`, any `s > max σ 0`-type (`σ < s`, `0 < s`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_f25_pt_bound (b : ℕ) {σ s : ℝ} (hσs : σ < s) (hs : 0 < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {k : ℕ} {M A : ℝ} {F : Euc d → Euc d → ℝ}, 0 ≤ A → Conormal k b M σ A F →
      ∀ x y : Euc d, x ≠ y →
        |F x y| ≤ A * C * HRS.MS.Phase2S82.pairWeight M x y * (1 + ‖x - y‖ ^ (-s)) := by
  obtain ⟨C, hC0, hC⟩ := r26t8a_p10a_env b (e0 := σ + ((0 : ℕ) : ℝ)) (e := s)
    (by simpa using hσs) hs
  refine ⟨C, hC0, fun {k M A F} hA hF x y hxy => ?_⟩
  have hz : x - y ≠ 0 := sub_ne_zero.2 hxy
  have hb := hF.2 0 0 (by omega) ((1 / 2 : ℝ) • (x + y)) (x - y) hz
  have e1 : (1 / 2 : ℝ) • (x + y) + (1 / 2 : ℝ) • (x - y) = x := by module
  have e2 : (1 / 2 : ℝ) • (x + y) - (1 / 2 : ℝ) • (x - y) = y := by module
  rw [e1, e2] at hb
  have h0 : ‖mixedJet 0 0 F ((1 / 2 : ℝ) • (x + y)) (x - y)‖ = |F x y| := by
    have := r26t8a_nest_zero (E := Euc d) 0 (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2)
      ((1 / 2 : ℝ) • (x + y)) (x - y)
    show ‖r26t8a_nest 0 0 (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) _ _‖ = _
    rw [this, norm_iteratedFDeriv_zero]
    simp only [midPair, e1, e2, Real.norm_eq_abs]
  rw [h0] at hb
  refine hb.trans ?_
  have hpw0 : 0 ≤ HRS.MS.Phase2S82.pairWeight M x y := by
    unfold HRS.MS.Phase2S82.pairWeight
    exact mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _) (Real.rpow_nonneg (s83_jb_pos _).le _)
  have := hC ‖x - y‖ (norm_pos_iff.2 hz)
  calc A * HRS.MS.Phase2S82.pairWeight M x y *
        (1 + (min 1 ‖x - y‖) ^ (-(σ + ((0 : ℕ) : ℝ))) * (1 + |Real.log (min 1 ‖x - y‖)|) ^ b)
      ≤ A * HRS.MS.Phase2S82.pairWeight M x y * (C * (1 + ‖x - y‖ ^ (-s))) :=
        mul_le_mul_of_nonneg_left this (mul_nonneg hA hpw0)
    _ = A * C * HRS.MS.Phase2S82.pairWeight M x y * (1 + ‖x - y‖ ^ (-s)) := by ring

end HRS.MS.R26T8A
