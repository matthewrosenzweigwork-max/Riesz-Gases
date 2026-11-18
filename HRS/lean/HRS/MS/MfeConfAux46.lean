import HRS.MS.MfeConfAux45

/-!
# S.B.1, packet F6 (part 8): limits as the cut-off is removed, I

* `sb1_Lam_bound`: explicit bound `|Λ| ≤ A (1+q)` (affine in `C_V`);
* `sb1_Cu`, `sb1_int_q_mol_le`: a uniform bound for `∫ (1+q) u`;
* `sb1_tail_tendsto`: tails of an integrable function over `{q ≥ (n+1)²}` vanish;
* `sb1_integrable_free`, `sb1_tendsto_free`: `∫ χ_R Φ → ∫ Φ`.
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Mol
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

section
variable {v θ : ℝ} {ν : Measure (EucConfig d N)}

theorem sb1_Lam_bound (hv : 0 < v) (hθ : 0 < θ) [IsProbabilityMeasure ν] (hm : Integrable p4m_q ν) {M CV : ℝ}
    (hMν : ∫ y, p4m_q y ∂ν ≤ M) (hM : 0 ≤ M) (hCV : 0 ≤ CV) {V : EucConfig d N → ℝ}
    (hV : ∀ x, |V x| ≤ CV * (1 + p4m_q x)) (x : EucConfig d N) :
    |p4m_Lam v θ ν V x| ≤ (|Real.log (p4m_cst d N v)| + (1 + M) / v + 1 + CV / θ) * (1 + p4m_q x) := by
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

/-- A uniform bound for `∫ (1+q) u`. -/
def sb1Cu (d N : ℕ) (v M : ℝ) : ℝ :=
  p4m_cst d N v * ((∫ w : EucConfig d N, p4m_E (1 / (2 * v)) w) +
    2 * (∫ w : EucConfig d N, p4m_q w * p4m_E (1 / (2 * v)) w) +
    2 * (∫ w : EucConfig d N, p4m_E (1 / (2 * v)) w) * M)

theorem sb1_int_q_mol_le (hv : 0 < v) [IsProbabilityMeasure ν] (hm : Integrable p4m_q ν) {M : ℝ}
    (hMν : ∫ y, p4m_q y ∂ν ≤ M) :
    ∫ x, (1 + p4m_q x) * p4Mol v ν x ≤ sb1Cu d N v M := by
  have hb : 0 < 1 / (2 * v) := by positivity
  have e : ∫ x, (1 + p4m_q x) * p4Mol v ν x =
      p4m_cst d N v * ∫ x, (1 + p4m_q x) * ∫ y, p4m_E (1 / (2 * v)) (x - y) ∂ν := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [p4m_mol_eq_E hv ν x]
    ring
  rw [e]
  unfold sb1Cu
  refine mul_le_mul_of_nonneg_left ?_ (p4m_cst_pos hv).le
  refine (p4m_weight_integral_le hm hb).trans ?_
  have hI0 : 0 ≤ ∫ w : EucConfig d N, p4m_E (1 / (2 * v)) w := integral_nonneg fun w => (p4m_E_pos _ _).le
  nlinarith

theorem sb1_Cu_nonneg (hv : 0 < v) {M : ℝ} (hM : 0 ≤ M) : 0 ≤ sb1Cu d N v M := by
  have hb : 0 < 1 / (2 * v) := by positivity
  unfold sb1Cu
  have h1 : 0 ≤ ∫ w : EucConfig d N, p4m_E (1 / (2 * v)) w := integral_nonneg fun w => (p4m_E_pos _ _).le
  have h2 : 0 ≤ ∫ w : EucConfig d N, p4m_q w * p4m_E (1 / (2 * v)) w :=
    integral_nonneg fun w => mul_nonneg (p4m_q_nonneg w) (p4m_E_pos _ _).le
  have := p4m_cst_pos (d := d) (N := N) hv
  positivity

/-- Tails of an integrable function over `{q ≥ (n+1)²}` vanish. -/
theorem sb1_tail_tendsto {g : EucConfig d N → ℝ} (hg : Integrable g) :
    Tendsto (fun n : ℕ => ∫ x in {x | ((n : ℝ) + 1) ^ 2 ≤ p4m_q x}, g x) atTop (𝓝 0) := by
  have hmeas : ∀ n : ℕ, MeasurableSet {x : EucConfig d N | ((n : ℝ) + 1) ^ 2 ≤ p4m_q x} := fun n =>
    (isClosed_le continuous_const p4m_continuous_q).measurableSet
  have : ∀ n : ℕ, (∫ x in {x | ((n : ℝ) + 1) ^ 2 ≤ p4m_q x}, g x) =
      ∫ x, {x | ((n : ℝ) + 1) ^ 2 ≤ p4m_q x}.indicator g x := fun n => (integral_indicator (hmeas n)).symm
  simp_rw [this]
  have h0 : (0 : ℝ) = ∫ x : EucConfig d N, (0 : ℝ) := by simp
  rw [h0]
  refine tendsto_integral_of_dominated_convergence (fun x => ‖g x‖) ?_ hg.norm ?_ ?_
  · intro n
    exact (hg.indicator (hmeas n)).aestronglyMeasurable
  · intro n
    refine Filter.Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ {x | ((n : ℝ) + 1) ^ 2 ≤ p4m_q x}
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
    have hx : x ∉ {x | ((n : ℝ) + 1) ^ 2 ≤ p4m_q x} := by
      simp only [Set.mem_setOf_eq, not_le]
      nlinarith
    rw [Set.indicator_of_notMem hx]

theorem sb1_integrable_free (hv : 0 < v) (hθ : 0 < θ) [IsProbabilityMeasure ν] (hm : Integrable p4m_q ν) {M CV : ℝ}
    (hMν : ∫ y, p4m_q y ∂ν ≤ M) (hM : 0 ≤ M) (hCV : 0 ≤ CV) {V : EucConfig d N → ℝ} (hVc : Continuous V)
    (hV : ∀ x, |V x| ≤ CV * (1 + p4m_q x)) :
    Integrable (fun x => p4Mol v ν x * Real.log (p4Mol v ν x) + p4Mol v ν x * V x / θ) volume := by
  have hcu := p4m_cont_u hv hm (ν := ν)
  refine ((p4m_integrable_q_mol hv hm).const_mul (|Real.log (p4m_cst d N v)| + (1 + M) / v + CV / θ)).mono'
    (((hcu.mul (hcu.log fun x => (p4m_mol_pos hv hm x).ne')).add ((hcu.mul hVc).div_const θ)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact sb1_Phi_bound hv hθ hm hMν hM hCV hV x

theorem sb1_tendsto_free (hv : 0 < v) (hθ : 0 < θ) [IsProbabilityMeasure ν] (hm : Integrable p4m_q ν) {M CV : ℝ}
    (hMν : ∫ y, p4m_q y ∂ν ≤ M) (hM : 0 ≤ M) (hCV : 0 ≤ CV) {V : EucConfig d N → ℝ} (hVc : Continuous V)
    (hV : ∀ x, |V x| ≤ CV * (1 + p4m_q x)) :
    Tendsto (fun n : ℕ => ∫ x, p4m_chi ((n : ℝ) + 1) x *
      (p4Mol v ν x * Real.log (p4Mol v ν x) + p4Mol v ν x * V x / θ)) atTop
      (𝓝 (∫ x, (p4Mol v ν x * Real.log (p4Mol v ν x) + p4Mol v ν x * V x / θ))) := by
  have hcu := p4m_cont_u hv hm (ν := ν)
  have hΦc : Continuous (fun x => p4Mol v ν x * Real.log (p4Mol v ν x) + p4Mol v ν x * V x / θ) :=
    (hcu.mul (hcu.log fun x => (p4m_mol_pos hv hm x).ne')).add ((hcu.mul hVc).div_const θ)
  refine tendsto_integral_of_dominated_convergence
    (fun x => (|Real.log (p4m_cst d N v)| + (1 + M) / v + CV / θ) * ((1 + p4m_q x) * p4Mol v ν x)) ?_
    ((p4m_integrable_q_mol hv hm).const_mul _) ?_ ?_
  · intro n
    exact ((p4m_contDiff_chi (R := (n : ℝ) + 1)).continuous.mul hΦc).aestronglyMeasurable
  · intro n
    refine Filter.Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (p4m_chi_nonneg _ _)]
    calc p4m_chi ((n : ℝ) + 1) x * |p4Mol v ν x * Real.log (p4Mol v ν x) + p4Mol v ν x * V x / θ|
        ≤ 1 * |p4Mol v ν x * Real.log (p4Mol v ν x) + p4Mol v ν x * V x / θ| := by
          gcongr
          exact p4m_chi_le_one _ _
      _ ≤ _ := by rw [one_mul]; exact sb1_Phi_bound hv hθ hm hMν hM hCV hV x
  · refine Filter.Eventually.of_forall fun x => ?_
    obtain ⟨n0, hn0⟩ := exists_nat_gt (p4m_q x)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop n0] with n hn
    have hnn : (n0 : ℝ) ≤ n := by exact_mod_cast hn
    have hq := p4m_q_nonneg x
    have hn1 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [p4m_chi_eq_one (R := (n : ℝ) + 1) (by positivity) (by nlinarith), one_mul]

end

end HRS.MS.MfeConf
