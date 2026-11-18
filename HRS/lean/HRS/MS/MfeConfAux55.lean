import HRS.MS.MfeConfAux54

/-!
# S.B.1, packet F6 (part 17): Fubini for the mollified law and the mollification error of a weighted-Lipschitz function

* `sb1_mol_prod_integrable`, `sb1_mol_integral`: `∫ u f dx = ∫ (∫ G_v(z) f(y+z) dz) dν(y)` for `|f| ≤ A (1+q)`;
* `sb1_mol_approx`: if `|f(x) - f(y)| ≤ D ‖x-y‖ (1 + ‖x‖ + ‖y‖)` then
  `|∫ u f dx - ∫ f dν| ≤ D (ε(v) + √v ∫ q dν)`, `ε(v) = √v (1/2 + 3Nd/2) + N d v → 0`.
-/

open MeasureTheory Filter Topology InformationTheory
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Mol HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section
variable {v : ℝ} {ν : Measure (EucConfig d N)}

theorem sb1_mol_prod_integrable (hv : 0 < v) [IsProbabilityMeasure ν] (hm : Integrable p4m_q ν)
    {f : EucConfig d N → ℝ} (hfc : Continuous f) {A : ℝ} (hA : 0 ≤ A)
    (hf : ∀ x, |f x| ≤ A * (1 + p4m_q x)) :
    Integrable (fun p : EucConfig d N × EucConfig d N => p4Gauss d N v (p.1 - p.2) * f p.1)
      ((volume : Measure (EucConfig d N)).prod ν) := by
  have hG1 := p4m_integrable_gauss (d := d) (N := N) hv
  have hG2 := p4m_integrable_poly_gauss (d := d) (N := N) hv 1
  simp only [pow_one] at hG2
  have k1 : Integrable (fun w : EucConfig d N => p4Gauss d N v w * (1 + 2 * p4m_q w)) volume := by
    have := hG1.add (hG2.const_mul 2)
    refine this.congr (Filter.Eventually.of_forall fun w => ?_)
    simp only [Pi.add_apply]; ring
  have i1 := p4m_prod_integrable (ν := ν) k1 (integrable_const (1 : ℝ))
  have i2 := p4m_prod_integrable (ν := ν) hG1 (hm.const_mul 2)
  have hmaj := (i1.add i2).const_mul A
  refine hmaj.mono' ?_ (Filter.Eventually.of_forall fun p => ?_)
  · exact (((p4m_continuous_gauss v).comp (continuous_fst.sub continuous_snd)).mul
      (hfc.comp continuous_fst)).aestronglyMeasurable
  · have hGp := p4m_gauss_pos (d := d) (N := N) hv (p.1 - p.2)
    have hq := p4m_q_add_le (p.1 - p.2) p.2
    have e : p.1 - p.2 + p.2 = p.1 := by abel
    rw [e] at hq
    have hq0 := p4m_q_nonneg (p.1 - p.2)
    have hq1 := p4m_q_nonneg p.2
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hGp]
    simp only [Pi.add_apply]
    calc p4Gauss d N v (p.1 - p.2) * |f p.1| ≤ p4Gauss d N v (p.1 - p.2) * (A * (1 + p4m_q p.1)) := by
          gcongr; exact hf _
      _ ≤ p4Gauss d N v (p.1 - p.2) * (A * (1 + (2 * p4m_q (p.1 - p.2) + 2 * p4m_q p.2))) := by
          gcongr
      _ = A * (1 * (p4Gauss d N v (p.1 - p.2) * (1 + 2 * p4m_q (p.1 - p.2))) +
          2 * p4m_q p.2 * p4Gauss d N v (p.1 - p.2)) := by ring

theorem sb1_mol_integral (hv : 0 < v) [IsProbabilityMeasure ν] (hm : Integrable p4m_q ν)
    {f : EucConfig d N → ℝ} (hfc : Continuous f) {A : ℝ} (hA : 0 ≤ A)
    (hf : ∀ x, |f x| ≤ A * (1 + p4m_q x)) :
    (∫ x, p4Mol v ν x * f x = ∫ y, (∫ z, p4Gauss d N v z * f (y + z)) ∂ν) ∧
      Integrable (fun y => ∫ z, p4Gauss d N v z * f (y + z)) ν := by
  have hint := sb1_mol_prod_integrable hv hm hfc hA hf
  have hH : ∀ y, ∫ x, p4Gauss d N v (x - y) * f x = ∫ z, p4Gauss d N v z * f (y + z) := by
    intro y
    have := integral_add_right_eq_self (μ := (volume : Measure (EucConfig d N)))
      (fun x => p4Gauss d N v (x - y) * f x) y
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [add_comm z y, add_sub_cancel_left]
  have e1 : ∀ x, p4Mol v ν x * f x = ∫ y, p4Gauss d N v (x - y) * f x ∂ν := fun x => by
    unfold p4Mol; rw [← integral_mul_const]
  refine ⟨?_, ?_⟩
  · simp_rw [e1]
    rw [integral_integral_swap (f := fun x y => p4Gauss d N v (x - y) * f x) hint]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => hH y)
  · have h := hint.integral_prod_right
    refine h.congr (Filter.Eventually.of_forall fun y => ?_)
    exact hH y

end

end HRS.MS.MfeConf
