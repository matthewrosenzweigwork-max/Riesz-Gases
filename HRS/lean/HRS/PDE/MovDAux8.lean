import HRS.PDE.MovDAux7

/-!
# MOVD Aux8: Hölder bound `∫ |S|² dν ≤ B` from an `L^q(Q)` bound on `dν/dQ` and an exponential moment of `S`
(`movT_source_limit_bdd`, uniform integrability of the regularised sources under the regularised laws)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

/-- `x^m ≤ (1 + ⌈m⌉!) e^x` for `x, m ≥ 0`. -/
theorem movd_rpow_le_exp {x m : ℝ} (hx : 0 ≤ x) (hm : 0 ≤ m) :
    x ^ m ≤ (1 + (⌈m⌉₊.factorial : ℝ)) * Real.exp x := by
  have hE1 : 1 ≤ Real.exp x := Real.one_le_exp hx
  have hf : (0 : ℝ) ≤ (⌈m⌉₊.factorial : ℝ) := Nat.cast_nonneg _
  rcases le_total x 1 with h1 | h1
  · have : x ^ m ≤ 1 := Real.rpow_le_one hx h1 hm
    nlinarith
  · have h2 : x ^ m ≤ x ^ ((⌈m⌉₊ : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h1 (Nat.le_ceil m)
    rw [Real.rpow_natCast] at h2
    have h3 := Real.pow_div_factorial_le_exp x hx ⌈m⌉₊
    have hfpos : (0 : ℝ) < (⌈m⌉₊.factorial : ℝ) := Nat.cast_pos.2 (Nat.factorial_pos _)
    rw [div_le_iff₀ hfpos] at h3
    nlinarith

/-- The constant of the Hölder bound. -/
def movd_Bhold (q Cq l C : ℝ) : ℝ :=
  Cq * ((1 + (⌈2 * (q / (q - 1))⌉₊.factorial : ℝ)) / l ^ (2 * (q / (q - 1))) * Real.exp C) ^
    (1 / (q / (q - 1)))

theorem movd_holder_L2 {α : Type*} [MeasurableSpace α] (ν Q : Measure α) [IsFiniteMeasure ν]
    [IsFiniteMeasure Q] (hac : ν ≪ Q) {q Cq : ℝ}
    (hq : 1 < q) (hCq : 0 ≤ Cq)
    (hLq : eLpNorm (ν.rnDeriv Q) (ENNReal.ofReal q) Q ≤ ENNReal.ofReal Cq) {S : α → ℝ}
    (hS : AEMeasurable S Q) {l C : ℝ} (hl : 0 < l)
    (hexp : ∫⁻ x, ENNReal.ofReal (Real.exp (l * |S x|)) ∂Q ≤ ENNReal.ofReal (Real.exp C)) :
    ∫⁻ x, ‖S x‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (movd_Bhold q Cq l C) := by
  set q' : ℝ := q / (q - 1) with hq'
  have hq1 : 0 < q - 1 := by linarith
  have hq'1 : 1 < q' := by
    rw [hq', lt_div_iff₀ hq1]; linarith
  have hconj : q.HolderConjugate q' := Real.HolderConjugate.conjExponent hq
  set m : ℝ := 2 * q' with hm
  have hm0 : 0 ≤ m := by positivity
  set K₁ : ℝ := (1 + (⌈m⌉₊.factorial : ℝ)) / l ^ m with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  -- pointwise bound
  have hpt : ∀ s : ℝ, (‖s‖ₑ ^ 2) ^ q' ≤ ENNReal.ofReal K₁ * ENNReal.ofReal (Real.exp (l * |s|)) := by
    intro s
    have h1 : (‖s‖ₑ ^ 2) ^ q' = ENNReal.ofReal (|s| ^ m) := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, show ((2 : ℕ) : ℝ) * q' = m by rw [hm]; push_cast; ring]
      rw [show ‖s‖ₑ = ENNReal.ofReal |s| by rw [← ofReal_norm]; rfl]
      rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg s) hm0]
    rw [h1, ← ENNReal.ofReal_mul hK₁0]
    refine ENNReal.ofReal_le_ofReal ?_
    have hx : 0 ≤ l * |s| := by positivity
    have h2 := movd_rpow_le_exp hx hm0
    rw [Real.mul_rpow hl.le (abs_nonneg s)] at h2
    have hlm : 0 < l ^ m := Real.rpow_pos_of_pos hl m
    rw [hK₁, div_mul_eq_mul_div, le_div_iff₀ hlm]
    nlinarith
  have hint : ∫⁻ x, (‖S x‖ₑ ^ 2) ^ q' ∂Q ≤ ENNReal.ofReal (K₁ * Real.exp C) := by
    calc ∫⁻ x, (‖S x‖ₑ ^ 2) ^ q' ∂Q
        ≤ ∫⁻ x, ENNReal.ofReal K₁ * ENNReal.ofReal (Real.exp (l * |S x|)) ∂Q := lintegral_mono fun x => hpt _
      _ = ENNReal.ofReal K₁ * ∫⁻ x, ENNReal.ofReal (Real.exp (l * |S x|)) ∂Q :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal K₁ * ENNReal.ofReal (Real.exp C) := by gcongr
      _ = ENNReal.ofReal (K₁ * Real.exp C) := (ENNReal.ofReal_mul hK₁0).symm
  have hgm : AEMeasurable (fun x => ‖S x‖ₑ ^ 2) Q := hS.enorm.pow_const 2
  have hhm : AEMeasurable (ν.rnDeriv Q) Q := (Measure.measurable_rnDeriv ν Q).aemeasurable
  have hν : ν = Q.withDensity (ν.rnDeriv Q) := (Measure.withDensity_rnDeriv_eq ν Q hac).symm
  have hlint : ∫⁻ x, ‖S x‖ₑ ^ 2 ∂ν = ∫⁻ x, (ν.rnDeriv Q * fun x => ‖S x‖ₑ ^ 2) x ∂Q := by
    conv_lhs => rw [hν]
    exact lintegral_withDensity_eq_lintegral_mul₀ hhm hgm
  rw [hlint]
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq Q hconj hhm hgm
  refine le_trans (le_of_eq rfl) (le_trans hH ?_)
  have hf1 : (∫⁻ x, ν.rnDeriv Q x ^ q ∂Q) ^ (1 / q) ≤ ENNReal.ofReal Cq := by
    refine le_trans (le_of_eq ?_) hLq
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp; linarith) (by simp)
      (Measure.measurable_rnDeriv ν Q).aestronglyMeasurable,
      ENNReal.toReal_ofReal (by linarith)]
    simp only [enorm_eq_self]
  have hf2 : (∫⁻ x, (‖S x‖ₑ ^ 2) ^ q' ∂Q) ^ (1 / q') ≤ ENNReal.ofReal ((K₁ * Real.exp C) ^ (1 / q')) := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)]
    exact ENNReal.rpow_le_rpow hint (by positivity)
  calc _ ≤ ENNReal.ofReal Cq * ENNReal.ofReal ((K₁ * Real.exp C) ^ (1 / q')) := mul_le_mul' hf1 hf2
    _ = ENNReal.ofReal (movd_Bhold q Cq l C) := by
      rw [← ENNReal.ofReal_mul hCq]
      rfl

end HRS

end
