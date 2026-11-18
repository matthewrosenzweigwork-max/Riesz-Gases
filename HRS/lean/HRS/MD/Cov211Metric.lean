import HRS.Prob.Metrics

/-!
# Packet COV211 (Prop. 2.11 `covariance_obstruction`), metric lemmas on `ℝ`

Generic lower bounds for `W_2`, `W_1` and the smooth distances `d_j` on probability measures on `ℝ`
by test functions (second-moment difference, Lipschitz tests, `C_b^j` tests).  No dynamics.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MD.Cov211

/-- `‖x‖ₑ ^ 2 = ofReal (x ^ 2)` for real `x`. -/
theorem enorm_rpow_two (x : ℝ) : ‖x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (x ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
    Real.rpow_two, sq_abs]

/-- The `L²` norm of `id` is the square root of the second moment. -/
theorem eLpNorm_id_two (P : Measure ℝ) (h : Integrable (fun x : ℝ => x ^ 2) P) :
    eLpNorm (fun x : ℝ => x) 2 P = ENNReal.ofReal (Real.sqrt (∫ x, x ^ 2 ∂P)) := by
  have hid : AEStronglyMeasurable (fun x : ℝ => x) P := measurable_id.aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hid]
  simp only [ENNReal.toReal_ofNat]
  simp_rw [enorm_rpow_two]
  rw [← ofReal_integral_eq_lintegral_ofReal h (Filter.Eventually.of_forall fun x => sq_nonneg x),
    ENNReal.ofReal_rpow_of_nonneg (integral_nonneg fun x => sq_nonneg x) (by norm_num),
    Real.sqrt_eq_rpow]

/-- `W₂(P,Q) ≥ |√(∫x²dP) - √(∫x²dQ)|` (reverse triangle inequality in `L²` of any coupling). -/
theorem second_moment_le_wasserstein (P Q : Measure ℝ) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (hP : Integrable (fun x : ℝ => x ^ 2) P)
    (hQ : Integrable (fun x : ℝ => x ^ 2) Q) :
    ENNReal.ofReal |Real.sqrt (∫ x, x ^ 2 ∂P) - Real.sqrt (∫ x, x ^ 2 ∂Q)| ≤
      wassersteinE 2 P Q := by
  unfold wassersteinE
  refine le_iInf fun π => ?_
  have hπ : IsProbabilityMeasure π.1 := π.2.isProbabilityMeasure
  have h1 : eLpNorm (fun z : ℝ × ℝ => z.1) 2 π.1 = ENNReal.ofReal (Real.sqrt (∫ x, x ^ 2 ∂P)) := by
    have := eLpNorm_map_measure (μ := π.1) (f := Prod.fst) (g := fun x : ℝ => x) (p := 2)
      (by exact aestronglyMeasurable_id) measurable_fst.aemeasurable
    rw [π.2.1] at this
    rw [← eLpNorm_id_two P hP, this]; rfl
  have h2 : eLpNorm (fun z : ℝ × ℝ => z.2) 2 π.1 = ENNReal.ofReal (Real.sqrt (∫ x, x ^ 2 ∂Q)) := by
    have := eLpNorm_map_measure (μ := π.1) (f := Prod.snd) (g := fun x : ℝ => x) (p := 2)
      (by exact aestronglyMeasurable_id) measurable_snd.aemeasurable
    rw [π.2.2] at this
    rw [← eLpNorm_id_two Q hQ, this]; rfl
  have m1 : AEStronglyMeasurable (fun z : ℝ × ℝ => z.1) π.1 := measurable_fst.aestronglyMeasurable
  have m2 : AEStronglyMeasurable (fun z : ℝ × ℝ => z.2) π.1 := measurable_snd.aestronglyMeasurable
  have hm12 : AEStronglyMeasurable (fun z : ℝ × ℝ => z.1 - z.2) π.1 := by fun_prop
  have hcost : (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂π.1) ^ (1 / (2 : ℝ)) =
      eLpNorm (fun z : ℝ × ℝ => z.1 - z.2) 2 π.1 := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hm12]
    simp only [ENNReal.toReal_ofNat]
    congr 1
    refine lintegral_congr fun z => ?_
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
  rw [hcost]
  have t1 : eLpNorm (fun z : ℝ × ℝ => z.1) 2 π.1 ≤
      eLpNorm (fun z : ℝ × ℝ => z.1 - z.2) 2 π.1 + eLpNorm (fun z : ℝ × ℝ => z.2) 2 π.1 := by
    calc eLpNorm (fun z : ℝ × ℝ => z.1) 2 π.1
        = eLpNorm ((fun z : ℝ × ℝ => z.1 - z.2) + (fun z : ℝ × ℝ => z.2)) 2 π.1 := by
          congr 1; funext z; simp
      _ ≤ _ := eLpNorm_add_le (by norm_num)
  have t2 : eLpNorm (fun z : ℝ × ℝ => z.2) 2 π.1 ≤
      eLpNorm (fun z : ℝ × ℝ => z.1 - z.2) 2 π.1 + eLpNorm (fun z : ℝ × ℝ => z.1) 2 π.1 := by
    calc eLpNorm (fun z : ℝ × ℝ => z.2) 2 π.1
        = eLpNorm ((fun z : ℝ × ℝ => z.2 - z.1) + (fun z : ℝ × ℝ => z.1)) 2 π.1 := by
          congr 1; funext z; simp
      _ ≤ eLpNorm (fun z : ℝ × ℝ => z.2 - z.1) 2 π.1 + eLpNorm (fun z : ℝ × ℝ => z.1) 2 π.1 :=
          eLpNorm_add_le (by norm_num)
      _ = _ := by
          congr 1
          have : (fun z : ℝ × ℝ => z.2 - z.1) = -(fun z : ℝ × ℝ => z.1 - z.2) := by
            funext z; simp
          rw [this, eLpNorm_neg]
  rw [h1, h2] at t1 t2
  set a := Real.sqrt (∫ x, x ^ 2 ∂P)
  set b := Real.sqrt (∫ x, x ^ 2 ∂Q)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  rcases le_total b a with hab | hab
  · rw [abs_of_nonneg (sub_nonneg.2 hab), ENNReal.ofReal_sub _ hb]
    exact tsub_le_iff_right.2 t1
  · rw [abs_of_nonpos (sub_nonpos.2 hab), neg_sub, ENNReal.ofReal_sub _ ha]
    exact tsub_le_iff_right.2 t2

/-- Lipschitz test: `|∫Φ d(P-Q)| / K ≤ W₁(P,Q)` for a `K`-Lipschitz bounded measurable `Φ`. -/
theorem lip_test_le_wasserstein_one (P Q : Measure ℝ) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (Φ : ℝ → ℝ) (K : ℝ) (hK : 0 < K) (hΦm : Measurable Φ)
    (C : ℝ) (hC : ∀ x, |Φ x| ≤ C) (hΦ : ∀ x y, |Φ x - Φ y| ≤ K * |x - y|) :
    ENNReal.ofReal (|∫ x, Φ x ∂P - ∫ x, Φ x ∂Q| / K) ≤ wassersteinE 1 P Q := by
  unfold wassersteinE
  refine le_iInf fun π => ?_
  have hπ : IsProbabilityMeasure π.1 := π.2.isProbabilityMeasure
  have iΦ1 : Integrable (fun z : ℝ × ℝ => Φ z.1) π.1 :=
    Integrable.of_bound (hΦm.comp measurable_fst).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun z => by simpa using hC z.1)
  have iΦ2 : Integrable (fun z : ℝ × ℝ => Φ z.2) π.1 :=
    Integrable.of_bound (hΦm.comp measurable_snd).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun z => by simpa using hC z.2)
  have e1 : ∫ x, Φ x ∂P = ∫ z, Φ z.1 ∂π.1 := by
    have h := integral_map (μ := π.1) (φ := Prod.fst) (f := Φ) measurable_fst.aemeasurable
      hΦm.aestronglyMeasurable
    rw [π.2.1] at h; exact h
  have e2 : ∫ x, Φ x ∂Q = ∫ z, Φ z.2 ∂π.1 := by
    have h := integral_map (μ := π.1) (φ := Prod.snd) (f := Φ) measurable_snd.aemeasurable
      hΦm.aestronglyMeasurable
    rw [π.2.2] at h; exact h
  rw [e1, e2, ← integral_sub iΦ1 iΦ2]
  have hle : ∀ z : ℝ × ℝ, ENNReal.ofReal (|Φ z.1 - Φ z.2|) ≤
      ENNReal.ofReal K * ENNReal.ofReal (‖z.1 - z.2‖ ^ (1 : ℝ)) := fun z => by
    rw [← ENNReal.ofReal_mul hK.le, Real.rpow_one, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal (hΦ z.1 z.2)
  calc ENNReal.ofReal (|∫ z, (Φ z.1 - Φ z.2) ∂π.1| / K)
      ≤ ENNReal.ofReal ((∫ z, |Φ z.1 - Φ z.2| ∂π.1) / K) := by
        gcongr
        exact abs_integral_le_integral_abs
    _ = ENNReal.ofReal K⁻¹ * ENNReal.ofReal (∫ z, |Φ z.1 - Φ z.2| ∂π.1) := by
        rw [← ENNReal.ofReal_mul (inv_nonneg.2 hK.le), div_eq_inv_mul]
    _ = ENNReal.ofReal K⁻¹ * ∫⁻ z, ENNReal.ofReal |Φ z.1 - Φ z.2| ∂π.1 := by
        have iA : Integrable (fun z : ℝ × ℝ => |Φ z.1 - Φ z.2|) π.1 := (iΦ1.sub iΦ2).abs
        rw [ofReal_integral_eq_lintegral_ofReal iA
          (Filter.Eventually.of_forall fun z => abs_nonneg _)]
    _ ≤ ENNReal.ofReal K⁻¹ * ∫⁻ z, ENNReal.ofReal K *
          ENNReal.ofReal (‖z.1 - z.2‖ ^ (1 : ℝ)) ∂π.1 := by
        gcongr with z
        exact hle z
    _ = (∫⁻ z, ENNReal.ofReal (‖z.1 - z.2‖ ^ (1 : ℝ)) ∂π.1) ^ (1 / (1 : ℝ)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc, ← ENNReal.ofReal_mul
          (inv_nonneg.2 hK.le), inv_mul_cancel₀ hK.ne', ENNReal.ofReal_one, one_mul, div_one,
          ENNReal.rpow_one]

/-- A `C_b^j` test: if `Φ/Cn` lies in the `C_b^j` unit ball then `|∫Φ d(P-Q)| ≤ Cn d_j(P,Q)`. -/
theorem ball_test_le_smoothDist (j : ℕ) (P Q : Measure ℝ) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (Φ : ℝ → ℝ) (Cn : ℝ) (hC : 0 < Cn)
    (hΦ : (fun x => Φ x / Cn) ∈ CbUnitBall ℝ j) (hΦi : Integrable Φ P) (hΦj : Integrable Φ Q) :
    |∫ x, Φ x ∂P - ∫ x, Φ x ∂Q| ≤ Cn * smoothDist j P Q := by
  have h := abs_integral_sub_le_smoothDist hΦ P Q
  have e : ∫ x, Φ x / Cn ∂P - ∫ x, Φ x / Cn ∂Q = (∫ x, Φ x ∂P - ∫ x, Φ x ∂Q) / Cn := by
    simp only [div_eq_inv_mul, integral_const_mul]; ring
  rw [e, abs_div, abs_of_pos hC, div_le_iff₀ hC] at h
  linarith

end HRS.MD.Cov211
