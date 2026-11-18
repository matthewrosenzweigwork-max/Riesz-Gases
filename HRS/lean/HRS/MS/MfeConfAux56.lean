import HRS.MS.MfeConfAux55

/-!
# S.B.1, packet F6 (part 18): mollification error of a weighted-Lipschitz function

`sb1_mol_approx`: if `|f(x) - f(y)| ≤ D ‖x-y‖ (1 + ‖x‖ + ‖y‖)`, `|f| ≤ A (1+q)`, then
`|∫ u f dx - ∫ f dν| ≤ D (√v (1/2 + 3Nd/2) + N d v + √v ∫ q dν)`.
-/

open MeasureTheory Filter Topology InformationTheory
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Mol HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section
variable {v : ℝ} {ν : Measure (EucConfig d N)}

theorem sb1_elem_ineq {s nz ny qz qy : ℝ} (hs : 0 < s) (hz : nz ^ 2 ≤ qz) (hy : ny ^ 2 ≤ qy) :
    nz * (1 + 2 * ny + nz) ≤ s / 2 + s * qy + (3 / 2 * s⁻¹ + 1) * qz := by
  have h1 : s * (nz * (1 + 2 * ny + nz)) ≤ s * (s / 2 + s * ny ^ 2 + (3 / 2 * s⁻¹ + 1) * nz ^ 2) := by
    have e : s * (s / 2 + s * ny ^ 2 + (3 / 2 * s⁻¹ + 1) * nz ^ 2) =
        s ^ 2 / 2 + s ^ 2 * ny ^ 2 + (3 / 2 + s) * nz ^ 2 := by
      field_simp
    rw [e]
    nlinarith [sq_nonneg (s - nz), sq_nonneg (s * ny - nz)]
  have h2 := le_of_mul_le_mul_left h1 hs
  have h3 : s * ny ^ 2 ≤ s * qy := mul_le_mul_of_nonneg_left hy hs.le
  have h4 : (3 / 2 * s⁻¹ + 1) * nz ^ 2 ≤ (3 / 2 * s⁻¹ + 1) * qz :=
    mul_le_mul_of_nonneg_left hz (by positivity)
  linarith

theorem sb1_mol_approx (hv : 0 < v) [IsProbabilityMeasure ν] (hm : Integrable p4m_q ν) {M : ℝ}
    (hMν : ∫ y, p4m_q y ∂ν ≤ M) {f : EucConfig d N → ℝ} (hfc : Continuous f) {A : ℝ} (hA : 0 ≤ A)
    (hf : ∀ x, |f x| ≤ A * (1 + p4m_q x)) {D : ℝ} (hD : 0 ≤ D)
    (hlip : ∀ x y, |f x - f y| ≤ D * ‖x - y‖ * (1 + ‖x‖ + ‖y‖)) :
    |(∫ x, p4Mol v ν x * f x) - ∫ y, f y ∂ν| ≤
      D * (Real.sqrt v * (1 / 2 + 3 / 2 * ((N * d : ℕ) : ℝ)) + ((N * d : ℕ) : ℝ) * v + Real.sqrt v * M) := by
  obtain ⟨hI, hHint⟩ := sb1_mol_integral hv hm hfc hA hf
  set s := Real.sqrt v with hsdef
  have hs : 0 < s := Real.sqrt_pos.2 hv
  have hs2 : s ^ 2 = v := Real.sq_sqrt hv.le
  set c : ℝ := ((N * d : ℕ) : ℝ) with hc
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  have hG1 := p4m_integrable_gauss (d := d) (N := N) hv
  have hG2 := p4m_integrable_poly_gauss (d := d) (N := N) hv 1
  simp only [pow_one] at hG2
  have hqG : ∫ w : EucConfig d N, p4m_q w * p4Gauss d N v w = c * v := p4m_integral_q_gauss hv
  have hG1' : ∫ w : EucConfig d N, p4Gauss d N v w = 1 := p4m_integral_gauss hv
  have hfν : Integrable f ν := by
    refine ((hm.const_mul A).add (integrable_const A)).mono' hfc.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    refine (hf x).trans (le_of_eq ?_)
    simp only [Pi.add_apply]; ring
  set K0 : ℝ := (3 / 2 * s⁻¹ + 1) * (c * v) with hK0
  -- the pointwise estimate
  have hpt : ∀ y, |(∫ z, p4Gauss d N v z * f (y + z)) - f y| ≤
      D * (s / 2 + s * p4m_q y + K0) := by
    intro y
    have hfy : Integrable (fun z => p4Gauss d N v z * f (y + z)) := by
      have hmaj := (hG1.const_mul (A * (1 + 2 * p4m_q y))).add (hG2.const_mul (2 * A))
      refine hmaj.mono' (((p4m_continuous_gauss v).mul (hfc.comp (continuous_const.add continuous_id))
        ).aestronglyMeasurable) (Filter.Eventually.of_forall fun z => ?_)
      have hGp := p4m_gauss_pos (d := d) (N := N) hv z
      have hq := p4m_q_add_le y z
      have hq0 := p4m_q_nonneg y
      have hq1 := p4m_q_nonneg z
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos hGp]
      simp only [Pi.add_apply]
      calc p4Gauss d N v z * |f (y + z)| ≤ p4Gauss d N v z * (A * (1 + p4m_q (y + z))) := by
            gcongr; exact hf _
        _ ≤ p4Gauss d N v z * (A * (1 + (2 * p4m_q y + 2 * p4m_q z))) := by gcongr
        _ = A * (1 + 2 * p4m_q y) * p4Gauss d N v z + 2 * A * (p4m_q z * p4Gauss d N v z) := by ring
    have hdiff : (∫ z, p4Gauss d N v z * f (y + z)) - f y =
        ∫ z, p4Gauss d N v z * (f (y + z) - f y) := by
      have : ∀ z, p4Gauss d N v z * (f (y + z) - f y) =
          p4Gauss d N v z * f (y + z) - p4Gauss d N v z * f y := fun z => by ring
      simp_rw [this]
      rw [integral_sub hfy (hG1.mul_const _), integral_mul_const, hG1', one_mul]
    rw [hdiff, ← Real.norm_eq_abs]
    have hmaj : Integrable (fun z => D * (s / 2 + s * p4m_q y) * p4Gauss d N v z +
        D * (3 / 2 * s⁻¹ + 1) * (p4m_q z * p4Gauss d N v z)) :=
      (hG1.const_mul _).add (hG2.const_mul _)
    refine (norm_integral_le_of_norm_le hmaj (Filter.Eventually.of_forall fun z => ?_)).trans (le_of_eq ?_)
    · have hGp := p4m_gauss_pos (d := d) (N := N) hv z
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos hGp]
      have hl := hlip (y + z) y
      simp only [add_sub_cancel_left] at hl
      have hn : ‖y + z‖ ≤ ‖y‖ + ‖z‖ := norm_add_le _ _
      have hel := sb1_elem_ineq hs (p4m_norm_sq_le_q z) (p4m_norm_sq_le_q y)
      have hnz := norm_nonneg z
      have h1 : ‖z‖ * (1 + ‖y + z‖ + ‖y‖) ≤ ‖z‖ * (1 + 2 * ‖y‖ + ‖z‖) :=
        mul_le_mul_of_nonneg_left (by linarith) hnz
      have h2 : |f (y + z) - f y| ≤ D * (s / 2 + s * p4m_q y + (3 / 2 * s⁻¹ + 1) * p4m_q z) := by
        calc |f (y + z) - f y| ≤ D * ‖z‖ * (1 + ‖y + z‖ + ‖y‖) := hl
          _ = D * (‖z‖ * (1 + ‖y + z‖ + ‖y‖)) := by ring
          _ ≤ D * (‖z‖ * (1 + 2 * ‖y‖ + ‖z‖)) := by gcongr
          _ ≤ _ := by gcongr
      calc p4Gauss d N v z * |f (y + z) - f y|
          ≤ p4Gauss d N v z * (D * (s / 2 + s * p4m_q y + (3 / 2 * s⁻¹ + 1) * p4m_q z)) := by gcongr
        _ = D * (s / 2 + s * p4m_q y) * p4Gauss d N v z +
            D * (3 / 2 * s⁻¹ + 1) * (p4m_q z * p4Gauss d N v z) := by ring
    · rw [integral_add (hG1.const_mul _) (hG2.const_mul _), integral_const_mul, integral_const_mul, hG1', hqG]
      simp only [hK0]
      ring
  -- integrate over `ν`
  rw [hI, ← integral_sub hHint hfν]
  have hmaj : Integrable (fun y => D * (s / 2 + K0) + D * s * p4m_q y) ν :=
    (integrable_const _).add (hm.const_mul _)
  have hpt' : ∀ y, ‖(∫ z, p4Gauss d N v z * f (y + z)) - f y‖ ≤ D * (s / 2 + K0) + D * s * p4m_q y := by
    intro y
    rw [Real.norm_eq_abs]
    refine (hpt y).trans (le_of_eq ?_)
    ring
  have hb := norm_integral_le_of_norm_le hmaj (Filter.Eventually.of_forall hpt')
  rw [← Real.norm_eq_abs]
  refine hb.trans ?_
  rw [integral_add (integrable_const _) (hm.const_mul _), integral_const_mul (D * s) (fun y => p4m_q y)]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hKe : K0 = 3 / 2 * c * s + c * v := by
    simp only [hK0]
    field_simp
    rw [← hs2]
    ring
  have : D * s * ∫ y, p4m_q y ∂ν ≤ D * s * M := mul_le_mul_of_nonneg_left hMν (by positivity)
  rw [hKe]
  nlinarith

end

end HRS.MS.MfeConf
