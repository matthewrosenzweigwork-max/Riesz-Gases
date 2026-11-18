import HRS.MS.SharpBias
import HRS.MS.SharpCritAux2
import HRS.MS.QsfOsc8
import HRS.Whole.Critical

/-!
# S79 (S7.9 `shifted_field_static`, `shifted_field_path`, `critical_path_limit`): plan and norm bounds

Frozen statements: `HRS.Whole.shifted_field_static`, `shifted_field_path`, `critical_path_limit`
(`HRS/Whole/Critical.lean:113..`), TeX S L6133-6192.  The TeX proof: the preceding static / stationary-path theorems give the
comparison bounds for the exactly centered field `zeta_N = sqrt N (mu_N - m_N)`; the added deterministic shift
`sqrt N (m_N - mu) - N^{3/2-p} b` has `B_m` norm `<= C N^{3/2-p-theta}` (S7.1, `S:eq:field-bias-remainder`); translations
preserve the `C_b^2` unit ball and are `W_1`-isometries; triangle inequality.

## Status of the three declarations

* `shifted_field_static`: provable from merged results.  Inputs: S4.5 `S45.quadratic_static_field_osc_proof`
  (`QsfOsc8`), S7.1 `S71.sharp_bias_quadratic_proof` (`SharpBias`), `S78.s78_deltaN_eq`, `S78.s78_biasTheta_pos`
  (`SharpCritAux2`), `eta_eq_zeta_add`, `meanEmpirical_eq_firstMarginal`.  S2.1 is not an input of the static statement.
* `shifted_field_path`, `critical_path_limit`: need the CONCLUSION of S2.1(i) (`HRS.Whole.whole_space_stationary`,
  `Headline.lean:334`, still `stated`) as an input theorem, not as a hypothesis; the `GibbsInvariant` hypothesis of S2.1(i) is
  available from `IsCanonicalRealization.invariant`.  Moreover `shifted_field_path` quantifies a window start `a0 >= 0`, while
  S2.1(i) is stated for `a0 = 0` only: the window needs stationarity of the particle path law and of the Gaussian field
  (semigroup property of `propagatorW`, Lyapunov identity), which are not in the tree.  `critical_path_limit` uses `a0 = 0` only.

## Files

`ShiftFldAux1` (this file: `B_m` norm of an `L^2(mu)`-density), `Aux2` (translation of smooth distances), `Aux3` (the shift
remainder from S7.1), `ShiftFldTie` (`shifted_field_static_proof : type_of% @shifted_field_static`, unconditional), `Aux4` (continuity
of `X -> mu_N(X) - nu` in `B_m`, translation invariance of `W_p`), `Aux5`/`Aux6` (`s79_core`: for a window start `a0`, the mean-field
centered window is the centered window plus a constant path, so distances change by at most `K N^{3/2-p-theta}`), `Aux7`
(rates at `s = 2d/3`), `ShiftFldCond` (`critical_path_limit_of_S21`, conditional on `type_of% @whole_space_stationary`),
`ShiftFldCond2` (`shifted_field_path_cond_tie`, conditional on `whole_space_stationary` and on two TRUE window-stationarity statements
`ParticleWindowStationary`, `GaussianWindowStationary` that are not in the tree).

## This file (`ShiftFldAux1`): the `B_m` norm of an `L^2(mu)`-density

For `m > d`, an element `u` of `B_m` with `|u(h_alpha)| <= K` for all Hermite functions has `||u|| <= K sqrt(sum lambda^{-m})`;
if `u(h_alpha) = int h_alpha r dmu` with `r in L^2(mu)`, `mu` a probability measure, then `K = C_0 ||r||_{L^2(mu)}`
(Cramer bound `|h_alpha| <= C_0`).  Applied to `r = phi - 1 - delta b` this gives
`||ofMeasureDiff m m_N mu - delta . biasField|| <= K ||phi - 1 - delta b||_{L^2(mu)}`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Whole.S79

open HRS (Euc)

variable {d : ℕ} {m : ℝ}

theorem s79_hermiteCoeff_ofSeq (hm : (d : ℝ) < m) (c : MultiIndex d → ℝ)
    (hc : ∃ C, ∀ α, |c α| ≤ C) (α : MultiIndex d) :
    OscDual.hermiteCoeff (OscDual.ofSeq m c) α = c α := by
  have hmem := OscDual.memℓp_of_bounded hm c hc
  unfold OscDual.hermiteCoeff
  rw [OscDual.coord_ofSeq_of_mem _ hmem α]
  have h := rpow_neg_half_mul m _ (oscEv_pos α)
  linear_combination (c α) * h

theorem s79_hermiteCoeff_sub (u v : OscDual d m) (α : MultiIndex d) :
    OscDual.hermiteCoeff (u - v) α = OscDual.hermiteCoeff u α - OscDual.hermiteCoeff v α := by
  have : u - v = u + (-1 : ℝ) • v := by rw [neg_one_smul, sub_eq_add_neg]
  rw [this, OscDual.hermiteCoeff_add, OscDual.hermiteCoeff_smul]
  ring

theorem s79_norm_le_of_coeff (hm : (d : ℝ) < m) (u : OscDual d m) (K : ℝ) (hK : 0 ≤ K)
    (h : ∀ α, |OscDual.hermiteCoeff u α| ≤ K) :
    ‖u‖ ≤ K * Real.sqrt (∑' α : MultiIndex d, oscEigenvalue d α ^ (-m)) := by
  have hS := OscDual.summable_oscEv_neg_rpow (d := d) hm
  rw [OscDual.norm_eq]
  have hsum : Summable fun α : MultiIndex d => oscEigenvalue d α ^ (-m) * OscDual.hermiteCoeff u α ^ 2 := by
    simp_rw [OscDual.hermiteCoeff_sq]
    exact OscDual.coord_sq_summable' u
  have hle : ∀ α : MultiIndex d, oscEigenvalue d α ^ (-m) * OscDual.hermiteCoeff u α ^ 2 ≤
      oscEigenvalue d α ^ (-m) * K ^ 2 := by
    intro α
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (oscEv_pos α).le _)
    exact sq_le_sq' (by linarith [abs_le.1 (h α)]) (abs_le.1 (h α)).2
  have h1 := Summable.tsum_le_tsum hle hsum (hS.mul_right (K ^ 2))
  rw [tsum_mul_right] at h1
  calc Real.sqrt (∑' α : MultiIndex d, oscEigenvalue d α ^ (-m) * OscDual.hermiteCoeff u α ^ 2)
      ≤ Real.sqrt ((∑' α : MultiIndex d, oscEigenvalue d α ^ (-m)) * K ^ 2) := Real.sqrt_le_sqrt h1
    _ = K * Real.sqrt (∑' α : MultiIndex d, oscEigenvalue d α ^ (-m)) := by
        rw [Real.sqrt_mul (tsum_nonneg fun α => Real.rpow_nonneg (oscEv_pos α).le _),
          Real.sqrt_sq hK, mul_comm]

theorem s79_integral_abs_le_l2Norm {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {r : Euc d → ℝ}
    (hr : MemLp r 2 μ) : ∫ x, |r x| ∂μ ≤ l2Norm μ r := by
  have habs : MemLp (fun x => |r x|) 2 μ := hr.abs
  have hv := ProbabilityTheory.variance_nonneg (fun x => |r x|) μ
  rw [ProbabilityTheory.variance_eq_sub habs] at hv
  simp only [Pi.pow_apply] at hv
  have e : ∫ x, (|r x|)^2 ∂μ = ∫ x, r x ^ 2 ∂μ :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => sq_abs _)
  rw [e] at hv
  unfold l2Norm
  exact Real.le_sqrt_of_sq_le (by linarith)

/-- `|∫ h r dμ| ≤ C₀ ‖r‖_{L²(μ)}` for a measurable `h` with `|h| ≤ C₀`, `μ` a probability measure. -/
theorem s79_abs_integral_le {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {r h : Euc d → ℝ}
    (hr : MemLp r 2 μ) (hh : AEStronglyMeasurable h μ) {C0 : ℝ} (hC : ∀ x, |h x| ≤ C0) :
    |∫ x, h x * r x ∂μ| ≤ C0 * l2Norm μ r := by
  have hr1 : Integrable r μ := hr.integrable (by norm_num)
  have hint : Integrable (fun x => h x * r x) μ :=
    hr1.bdd_mul hh (c := C0) (Filter.Eventually.of_forall fun x => by simpa using hC x)
  calc |∫ x, h x * r x ∂μ| ≤ ∫ x, |h x * r x| ∂μ := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (μ := μ) (fun x => h x * r x)
    _ ≤ ∫ x, C0 * |r x| ∂μ := by
        refine integral_mono hint.abs (hr1.abs.const_mul C0) fun x => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hC x) (abs_nonneg _)
    _ = C0 * ∫ x, |r x| ∂μ := integral_const_mul _ _
    _ ≤ C0 * l2Norm μ r := by
        have hC0 : 0 ≤ C0 := (abs_nonneg _).trans (hC 0)
        exact mul_le_mul_of_nonneg_left (s79_integral_abs_le_l2Norm hr) hC0

/-- `∫ g d(μ.withDensity (ofReal ρ)) = ∫ ρ g dx` for a nonnegative real `ρ`. -/
theorem s79_integral_withDensityReal {ρ : Euc d → ℝ} (hρ : IsProbDensity ρ) (g : Euc d → ℝ) :
    ∫ x, g x ∂(withDensityReal ρ) = ∫ x, ρ x * g x := by
  unfold withDensityReal
  rw [integral_withDensity_eq_integral_toReal_smul (hρ.measurable.ennreal_ofReal)
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp [ENNReal.toReal_ofReal (hρ.nonneg x)]

/-- The `B_m` norm of `m_N - μ - δ b` (with `m_N = φ μ`, `b = bd · ρ`) is controlled by the `L²(μ)` norm of
`φ - 1 - δ bd`, with a constant depending only on `d` and `m > d`. -/
theorem s79_bias_vec_bound (hm : (d : ℝ) < m) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ρ bd φ : Euc d → ℝ) (δ : ℝ), IsProbDensity ρ → Measurable φ →
      (∀ x, 0 ≤ φ x) → MemLp bd 2 (withDensityReal ρ) →
      MemLp (fun x => φ x - 1 - δ * bd x) 2 (withDensityReal ρ) →
      ‖OscDual.ofMeasureDiff m ((withDensityReal ρ).withDensity (fun x => ENNReal.ofReal (φ x)))
          (withDensityReal ρ) - δ • OscDual.ofFun m (fun x => bd x * ρ x)‖ ≤
        K * l2Norm (withDensityReal ρ) (fun x => φ x - 1 - δ * bd x) := by
  obtain ⟨C0, hC0⟩ := hermiteFunD_uniform_bound (d := d)
  have hC0nn : 0 ≤ C0 := (abs_nonneg _).trans (hC0 0 0)
  refine ⟨C0 * Real.sqrt (∑' α : MultiIndex d, oscEigenvalue d α ^ (-m)),
    mul_nonneg hC0nn (Real.sqrt_nonneg _), ?_⟩
  intro ρ bd φ δ hρ hφm hφ0 hbd hr
  haveI hμ : IsProbabilityMeasure (withDensityReal ρ) := HRS.Whole.Q34.isProbabilityMeasure_nu hρ
  set μ : Measure (Euc d) := withDensityReal ρ with hμdef
  set r : Euc d → ℝ := fun x => φ x - 1 - δ * bd x with hrdef
  have hr1 : Integrable r μ := hr.integrable (by norm_num)
  have hbd1 : Integrable bd μ := hbd.integrable (by norm_num)
  have hφint : Integrable φ μ := by
    have : φ = fun x => r x + 1 + δ * bd x := by funext x; simp only [hrdef]; ring
    rw [this]
    exact (hr1.add (integrable_const 1)).add (hbd1.const_mul δ)
  haveI hfin : IsFiniteMeasure (μ.withDensity fun x => ENNReal.ofReal (φ x)) :=
    isFiniteMeasure_withDensity_ofReal hφint.2
  have hhm : ∀ α : MultiIndex d, AEStronglyMeasurable (hermiteFunD α) μ := fun α =>
    (contDiff_hermiteFunD α).continuous.aestronglyMeasurable
  have hhint : ∀ (α : MultiIndex d) (f : Euc d → ℝ), Integrable f μ →
      Integrable (fun x => hermiteFunD α x * f x) μ := fun α f hf =>
    hf.bdd_mul (hhm α) (c := C0) (Filter.Eventually.of_forall fun x => by simpa using hC0 α x)
  -- the coefficient of the shifted bias
  have hbcoef : ∀ α : MultiIndex d, Whole.hermiteCoeff (fun x => bd x * ρ x) α =
      ∫ x, hermiteFunD α x * bd x ∂μ := by
    intro α
    rw [hμdef, s79_integral_withDensityReal hρ]
    unfold Whole.hermiteCoeff
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
  have hbbd : ∃ C, ∀ α : MultiIndex d, |Whole.hermiteCoeff (fun x => bd x * ρ x) α| ≤ C :=
    ⟨C0 * l2Norm μ bd, fun α => by
      rw [hbcoef]; exact s79_abs_integral_le hbd (hhm α) (fun x => hC0 α x)⟩
  have hcoef : ∀ α : MultiIndex d, OscDual.hermiteCoeff
      (OscDual.ofMeasureDiff m (μ.withDensity fun x => ENNReal.ofReal (φ x)) μ -
        δ • OscDual.ofFun m (fun x => bd x * ρ x)) α = ∫ x, hermiteFunD α x * r x ∂μ := by
    intro α
    rw [s79_hermiteCoeff_sub, OscDual.hermiteCoeff_smul, OscDual.hermiteCoeff_ofMeasureDiff hm]
    unfold OscDual.ofFun
    rw [s79_hermiteCoeff_ofSeq hm _ hbbd, hbcoef]
    unfold measureHermiteCoeff
    rw [integral_withDensity_eq_integral_toReal_smul (hφm.ennreal_ofReal)
      (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
    have e1 : ∀ x, (ENNReal.ofReal (φ x)).toReal • hermiteFunD α x = hermiteFunD α x * φ x := by
      intro x; simp [ENNReal.toReal_ofReal (hφ0 x), mul_comm]
    simp_rw [e1]
    have e2 : ∫ x, hermiteFunD α x * r x ∂μ =
        ∫ x, hermiteFunD α x * φ x ∂μ - ∫ x, hermiteFunD α x ∂μ -
          δ * ∫ x, hermiteFunD α x * bd x ∂μ := by
      have h1 := hhint α φ hφint
      have h2 : Integrable (hermiteFunD α) μ := by
        simpa using hhint α (fun _ => (1 : ℝ)) (integrable_const 1)
      have h3 := (hhint α bd hbd1).const_mul δ
      have h12 : Integrable (fun x => hermiteFunD α x * φ x - hermiteFunD α x) μ := h1.sub h2
      have key : ∫ x, hermiteFunD α x * r x ∂μ = ∫ x, (hermiteFunD α x * φ x - hermiteFunD α x -
          δ * (hermiteFunD α x * bd x)) ∂μ :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [hrdef]; ring)
      rw [key, integral_sub h12 h3, integral_sub h1 h2, integral_const_mul]
    rw [e2]
  have hbound := s79_norm_le_of_coeff hm
    (OscDual.ofMeasureDiff m (μ.withDensity fun x => ENNReal.ofReal (φ x)) μ -
        δ • OscDual.ofFun m (fun x => bd x * ρ x)) (C0 * l2Norm μ r)
    (mul_nonneg hC0nn (Real.sqrt_nonneg _))
    (fun α => by rw [hcoef]; exact s79_abs_integral_le hr (hhm α) (fun x => hC0 α x))
  calc _ ≤ C0 * l2Norm μ r * Real.sqrt (∑' α : MultiIndex d, oscEigenvalue d α ^ (-m)) := hbound
    _ = _ := by ring

end HRS.Whole.S79
