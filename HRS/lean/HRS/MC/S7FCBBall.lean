import HRS.MC.S7FCBPhi

/-!
# FC-B, part 2: sup-norm comparison, ball integrals of the profile, `L^p` integrability of `w`

All balls are for the sup norm `‖z‖` of the torus (`Fin d → UnitAddCircle`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.Sec7.FCB

open HRS

variable {d : ℕ}

theorem fcb_eucDist_le (z : Torus d) : Torus.eucDist z 0 ≤ d * ‖z‖ := by
  rw [fcb_eucDist_eq_tdist, KernelGrad.tdist_zero_right]
  rw [EuclideanSpace.norm_eq]
  have h : ∀ i, ‖(KernelGrad.centeredRep z).ofLp i‖ ≤ ‖z‖ := by
    intro i
    rw [Real.norm_eq_abs, ← KernelGrad.norm_apply_eq]
    exact norm_le_pi_norm z i
  have h2 : ∑ i, ‖(KernelGrad.centeredRep z).ofLp i‖ ^ 2 ≤ d * ‖z‖ ^ 2 := by
    calc ∑ i, ‖(KernelGrad.centeredRep z).ofLp i‖ ^ 2 ≤ ∑ _i : Fin d, ‖z‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => by gcongr; exact h i
      _ = d * ‖z‖ ^ 2 := by simp
  by_cases hd : d = 0
  · subst hd
    simp
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hd
  refine Real.sqrt_le_iff.mpr ⟨by positivity, ?_⟩
  calc ∑ i, ‖(KernelGrad.centeredRep z).ofLp i‖ ^ 2 ≤ d * ‖z‖ ^ 2 := h2
    _ ≤ (d * ‖z‖) ^ 2 := by nlinarith [sq_nonneg ‖z‖]

theorem fcb_norm_le_eucDist (z : Torus d) : ‖z‖ ≤ Torus.eucDist z 0 := by
  rw [fcb_eucDist_eq_tdist]; exact KernelGrad.norm_le_tdist z

/-- Comparison of the envelope `w = g + c` with the profile at the sup norm. -/
theorem fcb_w_comp_sup (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ)) {c : ℝ}
    (hc : HRS.Sec7.EnvelopeConst (d := d) s c) :
    ∃ c1 c2 : ℝ, 0 < c1 ∧ 0 < c2 ∧ ∀ z : Torus d, z ≠ 0 →
      c1 * fcbPhi s ‖z‖ ≤ periodicRiesz d s z + c ∧
      periodicRiesz d s z + c ≤ c2 * fcbPhi s ‖z‖ := by
  obtain ⟨c1, c2, hc1, hc2, h⟩ := fcb_w_comp hd hs0 hs hc
  have hP := fcb_Phi_pos hs0 (show (0 : ℝ) < 1 / d by positivity)
  refine ⟨c1 / fcbPhi s (1 / d), c2, div_pos hc1 hP, hc2, fun z hz => ?_⟩
  obtain ⟨h1, h2⟩ := h z hz
  have hr : 0 < Torus.eucDist z 0 := by
    rw [fcb_eucDist_eq_tdist]; exact KernelGrad.tdist_pos hz
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hdpos : (0 : ℝ) < d := by positivity
  have hdn : Torus.eucDist z 0 / d ≤ ‖z‖ := by
    rw [div_le_iff₀ hdpos]; have := fcb_eucDist_le z; linarith
  constructor
  · have h3 : fcbPhi s ‖z‖ ≤ fcbPhi s (Torus.eucDist z 0 / d) := fcb_Phi_anti hs0 (by positivity) hdn
    have h4 := fcb_Phi_div hs0 hr hd
    have h5 : fcbPhi s ‖z‖ ≤ fcbPhi s (1 / d) * fcbPhi s (Torus.eucDist z 0) := h3.trans h4
    calc c1 / fcbPhi s (1 / d) * fcbPhi s ‖z‖
        ≤ c1 / fcbPhi s (1 / d) * (fcbPhi s (1 / d) * fcbPhi s (Torus.eucDist z 0)) := by
          gcongr
      _ = c1 * fcbPhi s (Torus.eucDist z 0) := by field_simp
      _ ≤ _ := h1
  · have h3 : fcbPhi s (Torus.eucDist z 0) ≤ fcbPhi s ‖z‖ :=
      fcb_Phi_anti hs0 hn (fcb_norm_le_eucDist z)
    calc periodicRiesz d s z + c ≤ c2 * fcbPhi s (Torus.eucDist z 0) := h2
      _ ≤ c2 * fcbPhi s ‖z‖ := by gcongr

/-- `Phi(t) ≤ A t^{-α}` on `(0,1]` for any `α > 0`, `α ≥ s`. -/
theorem fcb_Phi_le_rpow {s α : ℝ} (hs : 0 ≤ s) (hα : 0 < α) (hsα : s ≤ α) :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, 0 < t → t ≤ 1 → fcbPhi s t ≤ A * t ^ (-α) := by
  have h2 : (1 : ℝ) ≤ 2 ^ α := Real.one_le_rpow (by norm_num) hα.le
  refine ⟨1 + 2 ^ α + 1 / α, by positivity, fun t ht ht1 => ?_⟩
  have htα : 1 ≤ t ^ (-α) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht ht1 (by linarith)
  have hpow : 0 < t ^ (-α) := by positivity
  by_cases ht2 : t ≤ 1 / 2
  · rw [fcb_Phi_of_le ht2]
    unfold singEnvelope
    by_cases h0 : s = 0
    · simp only [h0, if_true]
      have hl : Real.log t ≤ 0 := Real.log_nonpos ht.le ht1
      rw [abs_of_nonpos hl]
      have hb := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos ht (-α))
      rw [Real.log_rpow ht] at hb
      have : -Real.log t ≤ t ^ (-α) / α := by
        have : -α * Real.log t ≤ t ^ (-α) - 1 := hb
        rw [le_div_iff₀ hα]; nlinarith
      have h5 : t ^ (-α) / α = (1 / α) * t ^ (-α) := by ring
      nlinarith
    · simp only [h0, if_false]
      have hmono : t ^ (-s) ≤ t ^ (-α) :=
        Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)
      have : 0 ≤ 1 / α := by positivity
      nlinarith
  · push Not at ht2
    have : fcbPhi s t = singEnvelope s (1 / 2) := by unfold fcbPhi; rw [min_eq_right ht2.le]
    rw [this]
    unfold singEnvelope
    by_cases h0 : s = 0
    · simp only [h0, if_true]
      have h3 : |Real.log (1 / 2 : ℝ)| = Real.log 2 := by
        rw [one_div, Real.log_inv, abs_neg, abs_of_pos (Real.log_pos (by norm_num))]
      rw [h3]
      have := Real.log_two_lt_d9
      have : 0 ≤ 1 / α := by positivity
      nlinarith
    · simp only [h0, if_false]
      have : (1 / 2 : ℝ) ^ (-s) ≤ 2 ^ α := by
        rw [Real.rpow_neg (by norm_num), one_div, Real.inv_rpow (by norm_num), inv_inv]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hsα
      have : 0 ≤ 1 / α := by positivity
      nlinarith

theorem fcb_norm_le_half (z : Torus d) : ‖z‖ ≤ 1 / 2 := by
  refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
  have := KernelGrad.abs_centeredRep_le z i
  rw [← KernelGrad.norm_apply_eq] at this
  exact this

end HRS.MC.Sec7.FCB
