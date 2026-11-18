import HRS.MS.MovBridgeAux1

/-!
# MOVA3B1, part 2: the analytic family for the `Σ → H` three-lines argument

Namespace `HRS.MS.MovOsc`, helpers `mova3b1_`.  For a compactly supported `L²` test function `K` and
`Θ ∈ L²` the map `z ↦ ∫ W^{(z-θ)δ} Θ K` (`W = 1 + 4π²|ξ|²`) is entire and bounded on `0 ≤ Re z ≤ 1`
(`mova3b1_I_differentiable`, `mova3b1_I_bdd`); `mova3b1_F` is the finite Hermite combination used in
`mo_interp_osc_H`.  Also Cauchy-Schwarz in the form needed on the boundary lines.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ComplexConjugate
open HRS.Whole HRS.MS.MovInterp HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

namespace HRS.MS.MovOsc

variable {d : ℕ}

/-- The bound `1 + 4π²R²` for the weight on the ball of radius `R`. -/
def mova3b1_Wb (R : ℝ) : ℝ := 1 + 4 * Real.pi ^ 2 * R ^ 2

lemma mova3b1_Wb_ge (R : ℝ) : 1 ≤ mova3b1_Wb R := by
  unfold mova3b1_Wb; nlinarith [sq_nonneg (Real.pi * R)]

lemma mova3b1_Wb_rpow_nonneg (R e : ℝ) : 0 ≤ mova3b1_Wb R ^ e :=
  Real.rpow_nonneg (by linarith [mova3b1_Wb_ge R]) _

lemma mova3b1_W_rpow_cont (e : ℝ) : Continuous fun ξ : Euc d => mova3b1_W ξ ^ e :=
  mova3b1_W_cont.rpow_const fun ξ => Or.inl (mova3b1_W_pos ξ).ne'

lemma mova3b1_rpow_le {R : ℝ} {ξ : Euc d} (hξ : ‖ξ‖ ≤ R) (e : ℝ) :
    mova3b1_W ξ ^ e ≤ mova3b1_Wb R ^ |e| := by
  have hW1 := mova3b1_W_ge ξ
  have hle : mova3b1_W ξ ≤ mova3b1_Wb R := by
    unfold mova3b1_W mova3b1_Wb
    have : ‖ξ‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hξ 2
    nlinarith [Real.pi_pos]
  calc mova3b1_W ξ ^ e ≤ mova3b1_W ξ ^ |e| :=
        Real.rpow_le_rpow_of_exponent_le hW1 (le_abs_self e)
    _ ≤ mova3b1_Wb R ^ |e| := Real.rpow_le_rpow (by linarith) hle (abs_nonneg e)

/-! ### Cauchy-Schwarz -/

lemma mova3b1_CS {P Q : Euc d → ℝ} (hP0 : ∀ ξ, 0 ≤ P ξ) (hQ0 : ∀ ξ, 0 ≤ Q ξ)
    (hPm : AEStronglyMeasurable P volume) (hQm : AEStronglyMeasurable Q volume)
    (hP2 : Integrable (fun ξ => P ξ ^ 2) volume) (hQ2 : Integrable (fun ξ => Q ξ ^ 2) volume) :
    ∫ ξ, P ξ * Q ξ ≤ Real.sqrt (∫ ξ, P ξ ^ 2) * Real.sqrt (∫ ξ, Q ξ ^ 2) := by
  have hMP : MemLp P 2 volume := (memLp_two_iff_integrable_sq hPm).2 hP2
  have hMQ : MemLp Q 2 volume := (memLp_two_iff_integrable_sq hQm).2 hQ2
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := (volume : Measure (Euc d)))
    (p := 2) (q := 2) Real.HolderConjugate.two_two (Eventually.of_forall hP0)
    (Eventually.of_forall hQ0) (by simpa using hMP) (by simpa using hMQ)
  have e1 : ∫ ξ, P ξ ^ (2 : ℝ) = ∫ ξ, P ξ ^ 2 := by
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp
  have e2 : ∫ ξ, Q ξ ^ (2 : ℝ) = ∫ ξ, Q ξ ^ 2 := by
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp
  rw [e1, e2] at hH
  simpa [Real.sqrt_eq_rpow] using hH

/-! ### Entire dependence on `z` -/

section Analytic

variable {R : ℝ} {g : Euc d → ℂ}

lemma mova3b1_weighted_int (hg : Integrable g volume) (hsupp : ∀ ξ : Euc d, R < ‖ξ‖ → g ξ = 0)
    (e : ℝ) : Integrable (fun ξ => mova3b1_W ξ ^ e * ‖g ξ‖) volume := by
  refine (hg.norm.const_mul (mova3b1_Wb R ^ |e|)).mono'
    ((mova3b1_W_rpow_cont e).aestronglyMeasurable.mul hg.aestronglyMeasurable.norm)
    (Eventually.of_forall fun ξ => ?_)
  by_cases hξ : ‖ξ‖ ≤ R
  · rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (mova3b1_W_pos ξ).le _)
      (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_right (mova3b1_rpow_le hξ e) (norm_nonneg _)
  · rw [hsupp ξ (not_le.1 hξ)]; simp

lemma mova3b1_cpow_mul_integrable (hg : Integrable g volume)
    (hsupp : ∀ ξ : Euc d, R < ‖ξ‖ → g ξ = 0) (y : ℂ) :
    Integrable (fun ξ => ((mova3b1_W ξ : ℝ) : ℂ) ^ y * g ξ) volume := by
  have hWm : Measurable fun ξ : Euc d => ((mova3b1_W ξ : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp mova3b1_W_cont.measurable
  refine (mova3b1_weighted_int hg hsupp y.re).mono'
    ((hWm.pow_const y).aestronglyMeasurable.mul hg.aestronglyMeasurable)
    (Eventually.of_forall fun ξ => ?_)
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (mova3b1_W_pos ξ)]

/-- The analytic family `z ↦ ∫ W^{(z-θ)δ} g`. -/
def mova3b1_I (θ δ : ℝ) (g : Euc d → ℂ) (z : ℂ) : ℂ :=
  ∫ ξ, ((mova3b1_W ξ : ℝ) : ℂ) ^ ((z - (θ : ℂ)) * (δ : ℂ)) * g ξ

lemma mova3b1_I_differentiable (θ δ : ℝ) (hg : Integrable g volume)
    (hsupp : ∀ ξ : Euc d, R < ‖ξ‖ → g ξ = 0) : Differentiable ℂ (mova3b1_I θ δ g) := by
  set a : ℝ := |δ| with ha
  set ε : ℝ := if 0 ≤ δ then 1 else -1 with hε0
  have hε : ε * a = δ := by
    by_cases h : 0 ≤ δ
    · simp [hε0, ha, h, abs_of_nonneg h]
    · simp [hε0, ha, h, abs_of_neg (not_le.1 h)]
  set w : Euc d → ℝ := fun ξ => mova3b1_W ξ ^ a with hw
  have hw1 : ∀ ξ, 1 ≤ w ξ := fun ξ => Real.one_le_rpow (mova3b1_W_ge ξ) (abs_nonneg _)
  have hwm : Measurable w := (mova3b1_W_rpow_cont a).measurable
  have hint : ∀ R' : ℝ, Integrable (fun ξ => w ξ ^ R' * ‖g ξ‖) volume := by
    intro R'
    refine (mova3b1_weighted_int hg hsupp (a * R')).congr (Eventually.of_forall fun ξ => ?_)
    simp only [hw]
    rw [← Real.rpow_mul (mova3b1_W_pos ξ).le]
  have hH := mova3_differentiable_weighted volume w hw1 hwm g hg.aestronglyMeasurable hint
  have key : mova3b1_I θ δ g =
      fun z => (fun y : ℂ => ∫ ξ, ((w ξ : ℝ) : ℂ) ^ y * g ξ) ((ε : ℂ) * (z - (θ : ℂ))) := by
    funext z
    unfold mova3b1_I
    congr 1; funext ξ; congr 1
    have hWne : ((mova3b1_W ξ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (mova3b1_W_pos ξ).ne'
    have hwne : ((w ξ : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (lt_of_lt_of_le one_pos (hw1 ξ)).ne'
    rw [Complex.cpow_def_of_ne_zero hWne, Complex.cpow_def_of_ne_zero hwne,
      ← Complex.ofReal_log (mova3b1_W_pos ξ).le,
      ← Complex.ofReal_log (lt_of_lt_of_le one_pos (hw1 ξ)).le]
    have hl : Real.log (w ξ) = a * Real.log (mova3b1_W ξ) := Real.log_rpow (mova3b1_W_pos ξ) a
    rw [hl]
    congr 1
    rw [← hε]
    push_cast
    ring
  rw [key]
  exact hH.comp (by fun_prop)

lemma mova3b1_I_bdd (θ δ : ℝ) (hg : Integrable g volume)
    (hsupp : ∀ ξ : Euc d, R < ‖ξ‖ → g ξ = 0) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    {z : ℂ} (hz0 : 0 ≤ z.re) (hz1 : z.re ≤ 1) :
    ‖mova3b1_I θ δ g z‖ ≤ mova3b1_Wb R ^ |δ| * ∫ ξ, ‖g ξ‖ := by
  unfold mova3b1_I
  rw [← integral_const_mul]
  refine (norm_integral_le_of_norm_le (hg.norm.const_mul _) (Eventually.of_forall fun ξ => ?_))
  by_cases hξ : ‖ξ‖ ≤ R
  · rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (mova3b1_W_pos ξ)]
    have hre : (((z - (θ : ℂ)) * (δ : ℂ))).re = (z.re - θ) * δ := by
      simp [Complex.mul_re]
    rw [hre]
    have h1 := mova3b1_rpow_le hξ ((z.re - θ) * δ)
    have h2 : |(z.re - θ) * δ| ≤ |δ| := by
      rw [abs_mul]
      have : |z.re - θ| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
      exact mul_le_of_le_one_left (abs_nonneg _) this
    have h3 : mova3b1_Wb R ^ |(z.re - θ) * δ| ≤ mova3b1_Wb R ^ |δ| :=
      Real.rpow_le_rpow_of_exponent_le (mova3b1_Wb_ge R) h2
    exact mul_le_mul_of_nonneg_right (h1.trans h3) (norm_nonneg _)
  · rw [hsupp ξ (not_le.1 hξ)]; simp

end Analytic

/-! ### The test function `K = 1_{‖ξ‖ ≤ R} W^σ conj Ψ` -/

/-- The compactly supported partner `K = 1_{‖ξ‖ ≤ R} W^σ conj Ψ`. -/
def mova3b1_K (σ R : ℝ) (Ψ : Euc d → ℂ) : Euc d → ℂ :=
  (Metric.closedBall (0 : Euc d) R).indicator fun ξ => ((mova3b1_W ξ ^ σ : ℝ) : ℂ) * conj (Ψ ξ)

/-- `Q = 1_{‖ξ‖ ≤ R} W^{σ/2} ‖Ψ‖`. -/
def mova3b1_Q (σ R : ℝ) (Ψ : Euc d → ℂ) : Euc d → ℝ :=
  (Metric.closedBall (0 : Euc d) R).indicator fun ξ => mova3b1_W ξ ^ (σ / 2) * ‖Ψ ξ‖

lemma mova3b1_K_supp (σ R : ℝ) (Ψ : Euc d → ℂ) :
    ∀ ξ : Euc d, R < ‖ξ‖ → mova3b1_K σ R Ψ ξ = 0 := by
  intro ξ hξ
  unfold mova3b1_K
  rw [Set.indicator_of_notMem]
  simpa [not_le] using hξ

lemma mova3b1_K_norm (σ R : ℝ) (Ψ : Euc d → ℂ) (ξ : Euc d) :
    ‖mova3b1_K σ R Ψ ξ‖ = (Metric.closedBall (0 : Euc d) R).indicator
      (fun ξ => mova3b1_W ξ ^ σ * ‖Ψ ξ‖) ξ := by
  unfold mova3b1_K
  rw [norm_indicator_eq_indicator_norm]
  congr 1
  funext ξ
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (mova3b1_W_pos ξ).le _),
    Complex.norm_conj]

lemma mova3b1_K_memLp (σ R : ℝ) {Ψ : Euc d → ℂ} (hΨ : MemLp Ψ 2 volume) :
    MemLp (mova3b1_K σ R Ψ) 2 volume := by
  have hm : AEStronglyMeasurable (mova3b1_K σ R Ψ) volume := by
    unfold mova3b1_K
    refine AEStronglyMeasurable.indicator ?_ Metric.isClosed_closedBall.measurableSet
    exact (Complex.continuous_ofReal.comp (mova3b1_W_rpow_cont σ)).aestronglyMeasurable.mul
      (Complex.continuous_conj.comp_aestronglyMeasurable hΨ.aestronglyMeasurable)
  refine (hΨ.const_mul (((mova3b1_Wb R ^ |σ| : ℝ)) : ℂ)).of_le hm (Eventually.of_forall fun ξ => ?_)
  rw [mova3b1_K_norm, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith [mova3b1_Wb_ge R]) _)]
  by_cases hξ : ‖ξ‖ ≤ R
  · rw [Set.indicator_of_mem (by simpa using hξ)]
    exact mul_le_mul_of_nonneg_right (mova3b1_rpow_le hξ σ) (norm_nonneg _)
  · rw [Set.indicator_of_notMem (by simpa using hξ)]
    exact mul_nonneg (mova3b1_Wb_rpow_nonneg R _) (norm_nonneg _)

lemma mova3b1_Q_sq (σ R : ℝ) (Ψ : Euc d → ℂ) (ξ : Euc d) :
    mova3b1_Q σ R Ψ ξ ^ 2 = (Metric.closedBall (0 : Euc d) R).indicator
      (fun ξ => mova3b1_W ξ ^ σ * ‖Ψ ξ‖ ^ 2) ξ := by
  unfold mova3b1_Q
  by_cases hξ : ξ ∈ Metric.closedBall (0 : Euc d) R
  · rw [Set.indicator_of_mem hξ, Set.indicator_of_mem hξ, mul_pow, mova3_rpow_half_sq (mova3b1_W_pos ξ)]
  · rw [Set.indicator_of_notMem hξ, Set.indicator_of_notMem hξ]; simp

lemma mova3b1_Q_nonneg (σ R : ℝ) (Ψ : Euc d → ℂ) (ξ : Euc d) : 0 ≤ mova3b1_Q σ R Ψ ξ := by
  unfold mova3b1_Q
  refine Set.indicator_nonneg (fun ξ _ => ?_) ξ
  exact mul_nonneg (Real.rpow_nonneg (mova3b1_W_pos ξ).le _) (norm_nonneg _)

lemma mova3b1_Q_meas (σ R : ℝ) {Ψ : Euc d → ℂ} (hΨ : MemLp Ψ 2 volume) :
    AEStronglyMeasurable (mova3b1_Q σ R Ψ) volume := by
  unfold mova3b1_Q
  exact AEStronglyMeasurable.indicator
    ((mova3b1_W_rpow_cont (σ / 2)).aestronglyMeasurable.mul hΨ.aestronglyMeasurable.norm)
    Metric.isClosed_closedBall.measurableSet

lemma mova3b1_Q_sq_integrable (σ R : ℝ) {Ψ : Euc d → ℂ} (hΨ : MemLp Ψ 2 volume) :
    Integrable (fun ξ => mova3b1_Q σ R Ψ ξ ^ 2) volume := by
  refine (hΨ.norm.integrable_sq.const_mul (mova3b1_Wb R ^ |σ|)).mono'
    ((mova3b1_Q_meas σ R hΨ).pow 2) (Eventually.of_forall fun ξ => ?_)
  rw [mova3b1_Q_sq, Real.norm_of_nonneg (Set.indicator_nonneg (fun ξ _ =>
    mul_nonneg (Real.rpow_nonneg (mova3b1_W_pos ξ).le _) (sq_nonneg _)) ξ)]
  by_cases hξ : ‖ξ‖ ≤ R
  · rw [Set.indicator_of_mem (by simpa using hξ)]
    exact mul_le_mul_of_nonneg_right (mova3b1_rpow_le hξ σ) (sq_nonneg _)
  · rw [Set.indicator_of_notMem (by simpa using hξ)]
    exact mul_nonneg (mova3b1_Wb_rpow_nonneg R _) (sq_nonneg _)

/-! ### The family `F` -/

/-- `F(z) = ∑_α u_α(z) ∫ W^{(z-θ)δ} Θ_α K`, with the rotated coefficients `u_α(z)`. -/
def mova3b1_F (S : Finset (MultiIndex d)) (c : MultiIndex d → ℝ)
    (Θ : MultiIndex d → Euc d → ℂ) (K : Euc d → ℂ) (θ r0 r1 δ : ℝ) (z : ℂ) : ℂ :=
  ∑ α ∈ S, mova3_ua (oscEigenvalue d) c θ r0 r1 z α * mova3b1_I θ δ (fun ξ => Θ α ξ * K ξ) z

section F

variable {S : Finset (MultiIndex d)} {c : MultiIndex d → ℝ} {Θ : MultiIndex d → Euc d → ℂ}
  {K : Euc d → ℂ} {R : ℝ}

lemma mova3b1_ThetaK_integrable (hΘ : ∀ α, MemLp (Θ α) 2 volume) (hK : MemLp K 2 volume)
    (α : MultiIndex d) : Integrable (fun ξ => Θ α ξ * K ξ) volume :=
  (hΘ α).integrable_mul hK

lemma mova3b1_ThetaK_supp (hKs : ∀ ξ : Euc d, R < ‖ξ‖ → K ξ = 0) (α : MultiIndex d)
    (ξ : Euc d) (hξ : R < ‖ξ‖) : Θ α ξ * K ξ = 0 := by
  rw [hKs ξ hξ, mul_zero]

lemma mova3b1_F_differentiable (hΘ : ∀ α, MemLp (Θ α) 2 volume) (hK : MemLp K 2 volume)
    (hKs : ∀ ξ : Euc d, R < ‖ξ‖ → K ξ = 0) (θ r0 r1 δ : ℝ) :
    Differentiable ℂ (mova3b1_F S c Θ K θ r0 r1 δ) := by
  unfold mova3b1_F
  refine Differentiable.fun_sum fun α _ => ?_
  refine Differentiable.mul ?_ (mova3b1_I_differentiable θ δ (mova3b1_ThetaK_integrable hΘ hK α)
    (mova3b1_ThetaK_supp hKs α))
  unfold mova3_ua
  fun_prop

lemma mova3b1_F_bdd (hΘ : ∀ α, MemLp (Θ α) 2 volume) (hK : MemLp K 2 volume)
    (hKs : ∀ ξ : Euc d, R < ‖ξ‖ → K ξ = 0) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (r0 r1 δ : ℝ) :
    ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → ‖mova3b1_F S c Θ K θ r0 r1 δ z‖ ≤ C := by
  refine ⟨∑ α ∈ S, (|c α| * Real.exp (|r1 - r0| * |Real.log (oscEigenvalue d α)| / 2)) *
      (mova3b1_Wb R ^ |δ| * ∫ ξ, ‖Θ α ξ * K ξ‖), fun z hz0 hz1 => ?_⟩
  unfold mova3b1_F
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => ?_)
  rw [norm_mul]
  have ha : ‖mova3_ua (oscEigenvalue d) c θ r0 r1 z α‖ ≤
      |c α| * Real.exp (|r1 - r0| * |Real.log (oscEigenvalue d α)| / 2) := by
    rw [mova3_norm_ua]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (mova3_exp_arg_le hθ0 hθ1 hz0 hz1).1) (abs_nonneg _)
  exact mul_le_mul ha (mova3b1_I_bdd θ δ (mova3b1_ThetaK_integrable hΘ hK α)
    (mova3b1_ThetaK_supp hKs α) hθ0 hθ1 hz0 hz1) (norm_nonneg _) (by positivity)

/-- `F(z)` as one integral. -/
lemma mova3b1_F_eq_integral (hΘ : ∀ α, MemLp (Θ α) 2 volume) (hK : MemLp K 2 volume)
    (hKs : ∀ ξ : Euc d, R < ‖ξ‖ → K ξ = 0) (θ r0 r1 δ : ℝ) (z : ℂ) :
    mova3b1_F S c Θ K θ r0 r1 δ z = ∫ ξ, ((mova3b1_W ξ : ℝ) : ℂ) ^ ((z - (θ : ℂ)) * (δ : ℂ)) *
      ((∑ α ∈ S, mova3_ua (oscEigenvalue d) c θ r0 r1 z α * Θ α ξ) * K ξ) := by
  unfold mova3b1_F mova3b1_I
  have hint : ∀ α ∈ S, Integrable (fun ξ => mova3_ua (oscEigenvalue d) c θ r0 r1 z α *
      (((mova3b1_W ξ : ℝ) : ℂ) ^ ((z - (θ : ℂ)) * (δ : ℂ)) * (Θ α ξ * K ξ))) volume :=
    fun α _ => (mova3b1_cpow_mul_integrable (mova3b1_ThetaK_integrable hΘ hK α)
      (mova3b1_ThetaK_supp hKs α) _).const_mul _
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ hint]
  congr 1; funext ξ
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  ring

end F

end HRS.MS.MovOsc
