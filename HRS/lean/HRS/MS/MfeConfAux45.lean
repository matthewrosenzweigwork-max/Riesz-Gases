import HRS.MS.MfeConfAux44

/-!
# S.B.1, packet F6 (part 7): bounds for the cut-off removal

* `sb1_Phi_bound`: `|u log u + u V/θ| ≤ A (1+q) u` for `|V| ≤ C_V (1+q)`, with `A` explicit and affine in `C_V`;
* `sb1_Ek_gen`: the cut-off error `|∑_k ∫ F ∂_kχ J_k|` for an arbitrary `F` with `|F| ≤ A_F (1+q)` is bounded by
  a tail integral of the weight (generalisation of `p4m_Ek_bound`, which fixes `F = Λ`).
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Mol
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section
variable {v θ : ℝ} {ν : Measure (EucConfig d N)}

theorem sb1_Phi_bound (hv : 0 < v) (hθ : 0 < θ) [IsProbabilityMeasure ν] (hm : Integrable p4m_q ν) {M CV : ℝ}
    (hM : ∫ y, p4m_q y ∂ν ≤ M) (hM0 : 0 ≤ M) (hCV : 0 ≤ CV) {V : EucConfig d N → ℝ}
    (hV : ∀ x, |V x| ≤ CV * (1 + p4m_q x)) (x : EucConfig d N) :
    |p4Mol v ν x * Real.log (p4Mol v ν x) + p4Mol v ν x * V x / θ| ≤
      (|Real.log (p4m_cst d N v)| + (1 + M) / v + CV / θ) * ((1 + p4m_q x) * p4Mol v ν x) := by
  have hu := p4m_mol_pos hv hm x
  have hl := p4m_mol_abs_log_le hv hm x
  have hq := p4m_q_nonneg x
  have hVx := hV x
  have e : p4Mol v ν x * Real.log (p4Mol v ν x) + p4Mol v ν x * V x / θ =
      p4Mol v ν x * (Real.log (p4Mol v ν x) + V x / θ) := by ring
  rw [e, abs_mul, abs_of_pos hu]
  have h1 : |Real.log (p4Mol v ν x) + V x / θ| ≤ |Real.log (p4Mol v ν x)| + |V x| / θ := by
    calc _ ≤ |Real.log (p4Mol v ν x)| + |V x / θ| := abs_add_le _ _
      _ = _ := by rw [abs_div, abs_of_pos hθ]
  have h2 : (p4m_q x + ∫ y, p4m_q y ∂ν) / v ≤ (1 + M) * (1 + p4m_q x) / v := by
    gcongr
    nlinarith [mul_nonneg hM0 hq]
  have h3 : |V x| / θ ≤ CV * (1 + p4m_q x) / θ := by gcongr
  have h4 : (1 + M) * (1 + p4m_q x) / v = (1 + M) / v * (1 + p4m_q x) := by ring
  have h5 : CV * (1 + p4m_q x) / θ = CV / θ * (1 + p4m_q x) := by ring
  have hc : 0 ≤ |Real.log (p4m_cst d N v)| := abs_nonneg _
  have hfin : |Real.log (p4Mol v ν x) + V x / θ| ≤
      (|Real.log (p4m_cst d N v)| + (1 + M) / v + CV / θ) * (1 + p4m_q x) := by
    nlinarith [mul_nonneg hc hq]
  calc p4Mol v ν x * |Real.log (p4Mol v ν x) + V x / θ|
      ≤ p4Mol v ν x * ((|Real.log (p4m_cst d N v)| + (1 + M) / v + CV / θ) * (1 + p4m_q x)) := by
        gcongr
    _ = _ := by ring

/-- The cut-off error term for an arbitrary quadratic-growth function `F`. -/
theorem sb1_Ek_gen {B K : ℝ} (hv : 0 < v) (hB : 0 ≤ B) (hK : 0 ≤ K) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (ν : Measure (EucConfig d N)) [IsProbabilityMeasure ν], Integrable p4m_q ν →
      ∀ (b : EucConfig d N → EucConfig d N), (∀ y, ‖b y‖ ≤ B + K * ‖y‖) →
      Continuous b → ∀ (F : EucConfig d N → ℝ) (AF : ℝ), 0 ≤ AF → (∀ x, |F x| ≤ AF * (1 + p4m_q x)) →
      ∀ (R L : ℝ), 1 ≤ R → 0 ≤ L → ∀ χ : EucConfig d N → ℝ,
      (∀ (x : EucConfig d N) (k : Fin N × Fin d), fderiv ℝ χ x (configBasis d N k) ≠ 0 →
        R ^ 2 ≤ p4m_q x ∧ p4m_q x ≤ 2 * R ^ 2) →
      (∀ (x : EucConfig d N) (k : Fin N × Fin d), |fderiv ℝ χ x (configBasis d N k)| ≤ L / R) →
      |∑ k : Fin N × Fin d, ∫ x, F x * fderiv ℝ χ x (configBasis d N k) *
        (θ * p4m_gu v ν k x - p4m_B v ν b k x)| ≤
        A * AF * L * ∫ x in {x | R ^ 2 ≤ p4m_q x}, (1 + p4m_q x) * ∫ y, p4m_E (1 / (4 * v)) (x - y) ∂ν := by
  obtain ⟨AJ, hAJ0, hAJ⟩ := p4m_J_bound (d := d) (N := N) hv θ hB hK
  refine ⟨((N * d : ℕ) : ℝ) * (3 * AJ), by positivity, fun ν _ hm b hbg hbc F AF hAF0 hF R L hR hL χ hχ0 hχ1 => ?_⟩
  have hR0 : 0 < R := by linarith
  set S : Set (EucConfig d N) := {x | R ^ 2 ≤ p4m_q x} with hS
  have hSm : MeasurableSet S := (isClosed_le continuous_const p4m_continuous_q).measurableSet
  set Wt : EucConfig d N → ℝ := fun x => (1 + p4m_q x) * ∫ y, p4m_E (1 / (4 * v)) (x - y) ∂ν with hWt
  have hWi : Integrable Wt volume := p4m_integrable_weight hm (by positivity)
  have hW0 : ∀ x, 0 ≤ Wt x := fun x => mul_nonneg (by have := p4m_q_nonneg x; linarith)
    (integral_nonneg fun y => (p4m_E_pos _ _).le)
  have hgi : Integrable (S.indicator Wt) volume := hWi.indicator hSm
  have hone : ∀ k : Fin N × Fin d, |∫ x, F x * fderiv ℝ χ x (configBasis d N k) *
      (θ * p4m_gu v ν k x - p4m_B v ν b k x)| ≤ 3 * AF * AJ * L * ∫ x in S, Wt x := by
    intro k
    rw [← Real.norm_eq_abs]
    have hint : ∫ x in S, Wt x = ∫ x, S.indicator Wt x := (integral_indicator hSm).symm
    have hint2 : 3 * AF * AJ * L * ∫ x in S, Wt x = ∫ x, 3 * AF * AJ * L * S.indicator Wt x := by
      rw [hint, integral_const_mul]
    rw [hint2]
    refine norm_integral_le_of_norm_le (hgi.const_mul (3 * AF * AJ * L)) (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    by_cases h0 : fderiv ℝ χ x (configBasis d N k) = 0
    · rw [h0]
      simp only [abs_zero, mul_zero, zero_mul]
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx]; have := hW0 x; positivity
      · rw [Set.indicator_of_notMem hx]; simp
    · obtain ⟨hq1, hq2⟩ := hχ0 x k h0
      have hx : x ∈ S := hq1
      rw [Set.indicator_of_mem hx]
      have hΛx := hF x
      have hJx := hAJ ν hm b hbg hbc k x
      have hd := hχ1 x k
      have hxn : ‖x‖ ≤ 2 * R := by
        have := p4m_norm_sq_le_q x
        have h1 : ‖x‖ ^ 2 ≤ (2 * R) ^ 2 := by nlinarith
        exact (abs_le_of_sq_le_sq' h1 (by positivity)).2
      have hdx : |fderiv ℝ χ x (configBasis d N k)| * (1 + ‖x‖) ≤ 3 * L := by
        calc |fderiv ℝ χ x (configBasis d N k)| * (1 + ‖x‖) ≤ L / R * (1 + 2 * R) := by gcongr
          _ = L * (1 / R + 2) := by field_simp
          _ ≤ L * 3 := by
            gcongr
            have : 1 / R ≤ 1 := by rw [div_le_one hR0]; exact hR
            linarith
          _ = _ := by ring
      have hq0 := p4m_q_nonneg x
      have hI0 : 0 ≤ ∫ y, p4m_E (1 / (4 * v)) (x - y) ∂ν := integral_nonneg fun y => (p4m_E_pos _ _).le
      have hdn := abs_nonneg (fderiv ℝ χ x (configBasis d N k))
      calc |F x| * |fderiv ℝ χ x (configBasis d N k)| *
            |θ * p4m_gu v ν k x - p4m_B v ν b k x|
          ≤ (AF * (1 + p4m_q x)) * |fderiv ℝ χ x (configBasis d N k)| *
            (AJ * ((1 + ‖x‖) * ∫ y, p4m_E (1 / (4 * v)) (x - y) ∂ν)) := by gcongr
        _ = (AF * AJ) * ((1 + p4m_q x) * ∫ y, p4m_E (1 / (4 * v)) (x - y) ∂ν) *
            (|fderiv ℝ χ x (configBasis d N k)| * (1 + ‖x‖)) := by ring
        _ ≤ (AF * AJ) * ((1 + p4m_q x) * ∫ y, p4m_E (1 / (4 * v)) (x - y) ∂ν) * (3 * L) := by
            gcongr
        _ = 3 * AF * AJ * L * Wt x := by rw [hWt]; ring
  calc |∑ k : Fin N × Fin d, ∫ x, F x * fderiv ℝ χ x (configBasis d N k) *
        (θ * p4m_gu v ν k x - p4m_B v ν b k x)|
      ≤ ∑ k : Fin N × Fin d, |∫ x, F x * fderiv ℝ χ x (configBasis d N k) *
        (θ * p4m_gu v ν k x - p4m_B v ν b k x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin N × Fin d, 3 * AF * AJ * L * ∫ x in S, Wt x := Finset.sum_le_sum fun k _ => hone k
    _ = ((N * d : ℕ) : ℝ) * (3 * AJ) * AF * L * ∫ x in S, Wt x := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_mul]
        ring

end

end HRS.MS.MfeConf
