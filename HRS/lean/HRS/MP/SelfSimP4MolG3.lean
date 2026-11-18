import HRS.MP.SelfSimP4MolG2

/-!
# MPP4MOL stage 5c (13): the cut-off error term
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MP.SelfSimP4Mol

variable {d N : ℕ}

theorem p4m_Lam_bound {v θ M CV : ℝ} (hv : 0 < v) (hθ : 0 < θ) (hM : 0 ≤ M) (hCV : 0 ≤ CV) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (ν : Measure (EucConfig d N)) [IsProbabilityMeasure ν], Integrable p4m_q ν →
      ∫ y, p4m_q y ∂ν ≤ M → ∀ V : EucConfig d N → ℝ, (∀ x, |V x| ≤ CV * (1 + p4m_q x)) →
      ∀ x, |p4m_Lam v θ ν V x| ≤ A * (1 + p4m_q x) := by
  refine ⟨|Real.log (p4m_cst d N v)| + (1 + M) / v + 1 + CV / θ, by positivity, fun ν _ hm hMν V hV x => ?_⟩
  have hl := p4m_mol_abs_log_le hv hm x
  have hq := p4m_q_nonneg x
  have hVx := hV x
  unfold p4m_Lam
  have h1 : |Real.log (p4Mol v ν x) + 1 + V x / θ| ≤ |Real.log (p4Mol v ν x)| + 1 + |V x| / θ := by
    calc _ ≤ |Real.log (p4Mol v ν x) + 1| + |V x / θ| := abs_add_le _ _
      _ ≤ (|Real.log (p4Mol v ν x)| + |1|) + |V x / θ| := by gcongr; exact abs_add_le _ _
      _ = _ := by rw [abs_one, abs_div, abs_of_pos hθ]
  have h2 : (p4m_q x + ∫ y, p4m_q y ∂ν) / v ≤ (1 + M) * (1 + p4m_q x) / v := by
    gcongr
    nlinarith [mul_nonneg hM hq]
  have h3 : |V x| / θ ≤ CV * (1 + p4m_q x) / θ := by gcongr
  have h4 : (1 + M) * (1 + p4m_q x) / v = (1 + M) / v * (1 + p4m_q x) := by ring
  have h5 : CV * (1 + p4m_q x) / θ = CV / θ * (1 + p4m_q x) := by ring
  have hc : 0 ≤ |Real.log (p4m_cst d N v)| := abs_nonneg _
  nlinarith [mul_nonneg hc hq]

/-- The cut-off error term is bounded by a tail integral of the weight. -/
theorem p4m_Ek_bound {v θ B K M CV : ℝ} (hv : 0 < v) (hθ : 0 < θ) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hM : 0 ≤ M) (hCV : 0 ≤ CV) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (ν : Measure (EucConfig d N)) [IsProbabilityMeasure ν], Integrable p4m_q ν →
      ∫ y, p4m_q y ∂ν ≤ M → ∀ (b : EucConfig d N → EucConfig d N), (∀ y, ‖b y‖ ≤ B + K * ‖y‖) →
      Continuous b → ∀ V : EucConfig d N → ℝ, (∀ x, |V x| ≤ CV * (1 + p4m_q x)) →
      ∀ (R L : ℝ), 1 ≤ R → 0 ≤ L → ∀ χ : EucConfig d N → ℝ,
      (∀ (x : EucConfig d N) (k : Fin N × Fin d), fderiv ℝ χ x (configBasis d N k) ≠ 0 →
        R ^ 2 ≤ p4m_q x ∧ p4m_q x ≤ 2 * R ^ 2) →
      (∀ (x : EucConfig d N) (k : Fin N × Fin d), |fderiv ℝ χ x (configBasis d N k)| ≤ L / R) →
      |∑ k : Fin N × Fin d, ∫ x, p4m_Lam v θ ν V x * fderiv ℝ χ x (configBasis d N k) *
        (θ * p4m_gu v ν k x - p4m_B v ν b k x)| ≤
        A * L * ∫ x in {x | R ^ 2 ≤ p4m_q x}, (1 + p4m_q x) * ∫ y, p4m_E (1 / (4 * v)) (x - y) ∂ν := by
  obtain ⟨AΛ, hAΛ0, hAΛ⟩ := p4m_Lam_bound (d := d) (N := N) (v := v) (θ := θ) hv hθ hM hCV
  obtain ⟨AJ, hAJ0, hAJ⟩ := p4m_J_bound (d := d) (N := N) hv θ hB hK
  refine ⟨((N * d : ℕ) : ℝ) * (3 * AΛ * AJ), by positivity, fun ν _ hm hMν b hbg hbc V hV R L hR hL χ hχ0 hχ1 => ?_⟩
  have hR0 : 0 < R := by linarith
  set S : Set (EucConfig d N) := {x | R ^ 2 ≤ p4m_q x} with hS
  have hSm : MeasurableSet S := (isClosed_le continuous_const p4m_continuous_q).measurableSet
  set Wt : EucConfig d N → ℝ := fun x => (1 + p4m_q x) * ∫ y, p4m_E (1 / (4 * v)) (x - y) ∂ν with hWt
  have hWi : Integrable Wt volume := p4m_integrable_weight hm (by positivity)
  have hW0 : ∀ x, 0 ≤ Wt x := fun x => mul_nonneg (by have := p4m_q_nonneg x; linarith)
    (integral_nonneg fun y => (p4m_E_pos _ _).le)
  have hgi : Integrable (S.indicator Wt) volume := hWi.indicator hSm
  have hone : ∀ k : Fin N × Fin d, |∫ x, p4m_Lam v θ ν V x * fderiv ℝ χ x (configBasis d N k) *
      (θ * p4m_gu v ν k x - p4m_B v ν b k x)| ≤ 3 * AΛ * AJ * L * ∫ x in S, Wt x := by
    intro k
    rw [← Real.norm_eq_abs]
    have hint : ∫ x in S, Wt x = ∫ x, S.indicator Wt x := (integral_indicator hSm).symm
    have hint2 : 3 * AΛ * AJ * L * ∫ x in S, Wt x = ∫ x, 3 * AΛ * AJ * L * S.indicator Wt x := by
      rw [hint, integral_const_mul]
    rw [hint2]
    refine norm_integral_le_of_norm_le (hgi.const_mul (3 * AΛ * AJ * L)) (Filter.Eventually.of_forall fun x => ?_)
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
      have hΛx := hAΛ ν hm hMν V hV x
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
      calc |p4m_Lam v θ ν V x| * |fderiv ℝ χ x (configBasis d N k)| *
            |θ * p4m_gu v ν k x - p4m_B v ν b k x|
          ≤ (AΛ * (1 + p4m_q x)) * |fderiv ℝ χ x (configBasis d N k)| *
            (AJ * ((1 + ‖x‖) * ∫ y, p4m_E (1 / (4 * v)) (x - y) ∂ν)) := by gcongr
        _ = (AΛ * AJ) * ((1 + p4m_q x) * ∫ y, p4m_E (1 / (4 * v)) (x - y) ∂ν) *
            (|fderiv ℝ χ x (configBasis d N k)| * (1 + ‖x‖)) := by ring
        _ ≤ (AΛ * AJ) * ((1 + p4m_q x) * ∫ y, p4m_E (1 / (4 * v)) (x - y) ∂ν) * (3 * L) := by
            gcongr
        _ = 3 * AΛ * AJ * L * Wt x := by rw [hWt]; ring
  calc |∑ k : Fin N × Fin d, ∫ x, p4m_Lam v θ ν V x * fderiv ℝ χ x (configBasis d N k) *
        (θ * p4m_gu v ν k x - p4m_B v ν b k x)|
      ≤ ∑ k : Fin N × Fin d, |∫ x, p4m_Lam v θ ν V x * fderiv ℝ χ x (configBasis d N k) *
        (θ * p4m_gu v ν k x - p4m_B v ν b k x)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin N × Fin d, 3 * AΛ * AJ * L * ∫ x in S, Wt x := Finset.sum_le_sum fun k _ => hone k
    _ = ((N * d : ℕ) : ℝ) * (3 * AΛ * AJ) * L * ∫ x in S, Wt x := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul,
          Nat.cast_mul]
        ring

theorem p4m_tail_tendsto {ν : Measure (EucConfig d N)} [IsProbabilityMeasure ν] (hm : Integrable p4m_q ν)
    {b : ℝ} (hb : 0 < b) :
    Tendsto (fun n : ℕ => ∫ x in {x | (n : ℝ) ^ 2 ≤ p4m_q x},
      (1 + p4m_q x) * ∫ y, p4m_E b (x - y) ∂ν) atTop (𝓝 0) := by
  have hWi := p4m_integrable_weight hm hb
  have : ∀ n : ℕ, (∫ x in {x | (n : ℝ) ^ 2 ≤ p4m_q x}, (1 + p4m_q x) * ∫ y, p4m_E b (x - y) ∂ν) =
      ∫ x, {x | (n : ℝ) ^ 2 ≤ p4m_q x}.indicator (fun x => (1 + p4m_q x) * ∫ y, p4m_E b (x - y) ∂ν) x := by
    intro n
    exact (integral_indicator ((isClosed_le continuous_const p4m_continuous_q).measurableSet)).symm
  simp_rw [this]
  have h0 : (0 : ℝ) = ∫ x : EucConfig d N, (0 : ℝ) := by simp
  rw [h0]
  refine tendsto_integral_of_dominated_convergence (fun x => ‖(1 + p4m_q x) * ∫ y, p4m_E b (x - y) ∂ν‖) ?_
    hWi.norm ?_ ?_
  · intro n
    exact (hWi.indicator ((isClosed_le continuous_const p4m_continuous_q).measurableSet)).aestronglyMeasurable
  · intro n
    refine Filter.Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ {x | (n : ℝ) ^ 2 ≤ p4m_q x}
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, norm_zero]; exact norm_nonneg _
  · refine Filter.Eventually.of_forall fun x => ?_
    obtain ⟨n0, hn0⟩ := exists_nat_gt (p4m_q x)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop n0] with n hn
    have hq := p4m_q_nonneg x
    have hn0pos : 0 < n0 := by exact_mod_cast lt_of_le_of_lt hq hn0
    have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0pos.trans_le hn
    have hnn : (n0 : ℝ) ≤ n := by exact_mod_cast hn
    have hx : x ∉ {x | (n : ℝ) ^ 2 ≤ p4m_q x} := by
      simp only [Set.mem_setOf_eq, not_le]
      nlinarith
    rw [Set.indicator_of_notMem hx]

end HRS.MP.SelfSimP4Mol
