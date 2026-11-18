import HRS.MS.MovDecAux2
import HRS.MS.GapExt

/-!
# MOV-2e (3): Poincaré closing, Gronwall, exponential decay of the energy  (S6.2, TeX L4278-4343)

Namespace `HRS.MS.MovDec`, helper prefix `mov2e_`.  Infrastructure for S6.2 (`W:lem:r2mov-linear`); not a manuscript row.

* `mov2e_poinc_ext`: the Poincaré inequality `c Var_μ f ≤ ∫ |∇f|² dμ` of `Gap.gap_ext` (stated for `C¹` functions with
  *bounded* gradient) extends, by a cutoff `χ(x/n)` and the elementary inequality
  `|a + b|² ≤ (1+ε)|a|² + (1+1/ε)|b|²`, to `C¹` functions in `L²(μ)` with `|∇f|² ∈ L¹(μ)` (needed for `f = A f` whose
  gradient `Z/ψ` is unbounded).  `Gap.gap_ext` applies to every `0 ≤ s < d` (through `GapRef`), so the Poincaré
  inputs `euc_thermal_gaussian_bounds_proof` (bullet 2) and `reflection_gap_poincare_proof` (both cases) are used in their
  common form `gap_ext`.
* `mov2e_poincare_closing`: for `⟨v, ψ⟩ = 0`, `c ν E(v) ≤ ∫ |Z|² dx` (`Var_μ(A f) ≥ ν E(v)` using `K ≥ 0`).
* `mov2e_energy_decay`: for a family `u(t)` of Schwartz functions with `⟨u(t), ψ⟩ = 0` and
  `d/dt u(t) = -S u(t)` in `L²` (right derivative, `S u(t)` the pointwise formula), `E(u(t)) ≤ e^{-2 c ν t} E(u(0))`
  and `‖u(t)‖₂² ≤ ((ν + M)/ν) e^{-2cνt} ‖u(0)‖₂²`.
* `mov2e_decay` (thermal equilibrium, all `0 ≤ s < d`), `mov2e_sandwich`, `mov2e_poincare`: the packaged statements.

Hypothesis form of the abstract family (the extension to `L²` data, the sandwich `T(t) = T(1) T(t-2) T(1)` and the
identification of `T(t) φ` with such a family are the job of MOV-2d / the assembly): `u : ℝ → 𝓢(ℝ^d)`; for every `t ≥ 0`
(i) `⟨u(t), √ρ⟩ = 0`, (ii) `t ↦ u(t) ∈ L²` is continuous on `[0, ∞)`, (iii) the `L²`-valued map has right derivative `-w(t)`
at `t` with `w(t) = movS u(t)` a.e. (this is `MovIsSemigroup.generator` for `T(t) φ ∈ 𝓢`, `d/dt T(t) φ = -S T(t) φ`).
Documented adjustments relative to the plan sketch: (a) the energy is written in the variable `v = √ρ f` (`mov2eE`), the
constant projection of `K` disappearing on zero mean; (b) the Poincaré input is `Gap.gap_ext` (bounded gradients, via
`GapRef`, all `0 ≤ s < d`) extended by the cutoff `mov2e_poinc_ext` (the gradient `Z/ψ` of `A f` is unbounded), instead of the
two separately cited statements; (c) positivity of the interaction form uses `wr13c_Kmu_nonneg` for `s > 0` and
`Psd.log_energy_nonneg` (zero mass, Gaussian pair integrability) for `s = 0`; the upper bound is the Schur test of
`wr13c_schur_W_real` (`s > 0`) resp. the Hilbert-Schmidt bound `∬ log²|x-y| ρ ρ < ∞` (`s = 0`, `d ≥ 2`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovDec

open HRS.Whole

variable {d : ℕ}

lemma mov2e_norm_gradient (f : Euc d → ℝ) (x : Euc d) : ‖gradient f x‖ = ‖fderiv ℝ f x‖ := by
  simp [gradient]

/-! ### Poincaré inequalities -/

/-- Poincaré for `C¹` functions with bounded gradient (the form of `Gap.gap_ext`). -/
def Mov2ePoincBdd (d : ℕ) (ρ : Euc d → ℝ) (c : ℝ) : Prop :=
  ∀ f : Euc d → ℝ, ContDiff ℝ 1 f → (∃ Cf : ℝ, ∀ x, ‖gradient f x‖ ≤ Cf) →
    MemLp f 2 (HRS.Whole.withDensityReal ρ) →
    c * ProbabilityTheory.variance f (HRS.Whole.withDensityReal ρ) ≤
      ∫ x, ‖gradient f x‖ ^ 2 ∂(HRS.Whole.withDensityReal ρ)

/-- Poincaré for `C¹` functions in `L²(μ)` with `|∇f|² ∈ L¹(μ)` (the form of `euc_thermal_gaussian_bounds`). -/
def Mov2ePoinc (d : ℕ) (ρ : Euc d → ℝ) (c : ℝ) : Prop :=
  ∀ f : Euc d → ℝ, ContDiff ℝ 1 f → MemLp f 2 (HRS.Whole.withDensityReal ρ) →
    Integrable (fun x => ‖gradient f x‖ ^ 2) (HRS.Whole.withDensityReal ρ) →
    c * ProbabilityTheory.variance f (HRS.Whole.withDensityReal ρ) ≤
      ∫ x, ‖gradient f x‖ ^ 2 ∂(HRS.Whole.withDensityReal ρ)

/-! #### The cutoff -/

/-- The scaling `x ↦ x/(n+1)` as a continuous linear map. -/
def mov2eL (d : ℕ) (n : ℕ) : Euc d →L[ℝ] Euc d := ((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ (Euc d)

lemma mov2eL_apply (n : ℕ) (x : Euc d) : mov2eL d n x = ((n : ℝ) + 1)⁻¹ • x := by
  simp [mov2eL]

lemma mov2eL_norm (n : ℕ) : ‖mov2eL d n‖ ≤ ((n : ℝ) + 1)⁻¹ := by
  have hR : 0 < (n : ℝ) + 1 := by positivity
  refine (ContinuousLinearMap.opNorm_smul_le _ _).trans ?_
  rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR)]
  calc ((n : ℝ) + 1)⁻¹ * ‖ContinuousLinearMap.id ℝ (Euc d)‖ ≤ ((n : ℝ) + 1)⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (inv_pos.2 hR).le
    _ = _ := mul_one _

/-- `χ_n(x) = θ(x/(n+1))`, `θ` the bump of `MovForceAux4`. -/
def mov2eChi (d : ℕ) (n : ℕ) (x : Euc d) : ℝ :=
  HRS.MS.MovForce.movb2_theta d (mov2eL d n x)

lemma mov2eChi_smooth (n : ℕ) : ContDiff ℝ ∞ (mov2eChi d n) :=
  (HRS.MS.MovForce.movb2_theta_smooth (d := d)).comp (mov2eL d n).contDiff

lemma mov2eChi_nonneg (n : ℕ) (x : Euc d) : 0 ≤ mov2eChi d n x :=
  HRS.MS.MovForce.movb2_theta_nonneg _

lemma mov2eChi_le_one (n : ℕ) (x : Euc d) : mov2eChi d n x ≤ 1 :=
  HRS.MS.MovForce.movb2_theta_le_one _

lemma mov2eChi_eq_one {n : ℕ} {x : Euc d} (hx : ‖x‖ ≤ (n : ℝ) + 1) : mov2eChi d n x = 1 := by
  unfold mov2eChi
  refine HRS.MS.MovForce.movb2_theta_one ?_
  have hR : 0 < (n : ℝ) + 1 := by positivity
  rw [mov2eL_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR)]
  calc ((n : ℝ) + 1)⁻¹ * ‖x‖ ≤ ((n : ℝ) + 1)⁻¹ * ((n : ℝ) + 1) :=
        mul_le_mul_of_nonneg_left hx (inv_pos.2 hR).le
    _ = 1 := inv_mul_cancel₀ hR.ne'

lemma mov2eChi_support (n : ℕ) : HasCompactSupport (mov2eChi d n) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) (2 * ((n : ℝ) + 1))) fun x hx => ?_
  have hR : 0 < (n : ℝ) + 1 := by positivity
  have hx' : 2 * ((n : ℝ) + 1) < ‖x‖ := by simpa using hx
  unfold mov2eChi
  refine HRS.MS.MovForce.movb2_theta_zero ?_
  rw [mov2eL_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR)]
  have : 2 * ((n : ℝ) + 1) ≤ ‖x‖ := hx'.le
  calc (2 : ℝ) = ((n : ℝ) + 1)⁻¹ * (2 * ((n : ℝ) + 1)) := by field_simp
    _ ≤ ((n : ℝ) + 1)⁻¹ * ‖x‖ := mul_le_mul_of_nonneg_left this (inv_pos.2 hR).le

lemma mov2eChi_fderiv : ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) (x : Euc d),
    ‖fderiv ℝ (mov2eChi d n) x‖ ≤ K / ((n : ℝ) + 1) := by
  have hθ : ContDiff ℝ ∞ (HRS.MS.MovForce.movb2_theta d) := HRS.MS.MovForce.movb2_theta_smooth
  have hcs : HasCompactSupport (HRS.MS.MovForce.movb2_theta d) :=
    (HRS.MS.MovForce.movb2_bump d).hasCompactSupport
  have hfd : Continuous (fderiv ℝ (HRS.MS.MovForce.movb2_theta d)) :=
    hθ.continuous_fderiv (by simp)
  obtain ⟨K, hK⟩ := hfd.bounded_above_of_compact_support (hcs.fderiv (𝕜 := ℝ))
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  refine ⟨K, hK0, fun n x => ?_⟩
  have hR : 0 < (n : ℝ) + 1 := by positivity
  have hdθ : DifferentiableAt ℝ (HRS.MS.MovForce.movb2_theta d) (mov2eL d n x) :=
    (hθ.differentiable (by simp)) _
  have hcomp := hdθ.hasFDerivAt.comp x (mov2eL d n).hasFDerivAt
  have h1 : fderiv ℝ (mov2eChi d n) x =
      (fderiv ℝ (HRS.MS.MovForce.movb2_theta d) (mov2eL d n x)).comp (mov2eL d n) := hcomp.fderiv
  rw [h1]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  calc ‖fderiv ℝ (HRS.MS.MovForce.movb2_theta d) (mov2eL d n x)‖ * ‖mov2eL d n‖
      ≤ K * ((n : ℝ) + 1)⁻¹ := mul_le_mul (hK _) (mov2eL_norm n) (norm_nonneg _) hK0
    _ = K / ((n : ℝ) + 1) := by rw [div_eq_mul_inv]


/-- **Extension of the Poincaré inequality from bounded to `L²(μ)` gradients** (cutoff `χ(x/(n+1))`). -/
theorem mov2e_poinc_ext {ρ : Euc d → ℝ} (hρ : Mov2eRho d ρ) {c : ℝ}
    (h : Mov2ePoincBdd d ρ c) : Mov2ePoinc d ρ c := by
  intro f hf hf2 hG
  have hprob := mov2e_isProb hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  obtain ⟨K, hK0, hK⟩ := mov2eChi_fderiv (d := d)
  set I : ℝ := ∫ x, ‖gradient f x‖ ^ 2 ∂μ with hI
  set F2 : ℝ := ∫ x, f x ^ 2 ∂μ with hF2
  have hI0 : 0 ≤ I := integral_nonneg fun x => sq_nonneg _
  have hf1 : Integrable f μ := hf2.integrable one_le_two
  have hfsq : Integrable (fun x => f x ^ 2) μ := hf2.integrable_sq
  have hfd : Differentiable ℝ f := hf.differentiable (by norm_num)
  -- the truncations
  set fn : ℕ → Euc d → ℝ := fun n x => mov2eChi d n x * f x with hfn
  have hχd : ∀ n, Differentiable ℝ (mov2eChi d n) := fun n =>
    ((mov2eChi_smooth n).differentiable (by simp))
  have hfn1 : ∀ n, ContDiff ℝ 1 (fn n) := fun n =>
    ((mov2eChi_smooth n).of_le (by exact_mod_cast le_top)).mul hf
  have hfn_fd : ∀ n x, fderiv ℝ (fn n) x =
      mov2eChi d n x • fderiv ℝ f x + f x • fderiv ℝ (mov2eChi d n) x := fun n x =>
    fderiv_mul (hχd n x) (hfd x)
  have hfn_abs : ∀ n x, |fn n x| ≤ |f x| := fun n x => by
    simp only [hfn, abs_mul, abs_of_nonneg (mov2eChi_nonneg n x)]
    calc mov2eChi d n x * |f x| ≤ 1 * |f x| :=
          mul_le_mul_of_nonneg_right (mov2eChi_le_one n x) (abs_nonneg _)
      _ = _ := one_mul _
  have hfn_eq : ∀ (n : ℕ) (x : Euc d), ‖x‖ ≤ (n : ℝ) + 1 → fn n x = f x := fun n x hx => by
    simp only [hfn, mov2eChi_eq_one hx, one_mul]
  have hfn_mem : ∀ n, MemLp (fn n) 2 μ := fun n =>
    hf2.of_le (hfn1 n).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simpa only [Real.norm_eq_abs] using hfn_abs n x)
  have hfn_bdd : ∀ n, ∃ Cf : ℝ, ∀ x, ‖gradient (fn n) x‖ ≤ Cf := fun n => by
    have hcs : HasCompactSupport (fn n) := (mov2eChi_support (d := d) n).mul_right
    have hcont : Continuous (fderiv ℝ (fn n)) := (hfn1 n).continuous_fderiv (by norm_num)
    obtain ⟨C, hC⟩ := hcont.bounded_above_of_compact_support (hcs.fderiv (𝕜 := ℝ))
    exact ⟨C, fun x => by rw [mov2e_norm_gradient]; exact hC x⟩
  have hgap : ∀ n, c * ProbabilityTheory.variance (fn n) μ ≤ ∫ x, ‖gradient (fn n) x‖ ^ 2 ∂μ :=
    fun n => h _ (hfn1 n) (hfn_bdd n) (hfn_mem n)
  -- pointwise bound
  have hptw : ∀ ε : ℝ, 0 < ε → ∀ (n : ℕ) (x : Euc d), ‖gradient (fn n) x‖ ^ 2 ≤
      (1 + ε) * ‖gradient f x‖ ^ 2 + (1 + 1 / ε) * (K / ((n : ℝ) + 1)) ^ 2 * f x ^ 2 := by
    intro ε hε n x
    set a : ℝ := ‖fderiv ℝ f x‖ with ha
    set b : ℝ := |f x| * (K / ((n : ℝ) + 1)) with hb
    have h1 : ‖gradient (fn n) x‖ ≤ a + b := by
      rw [mov2e_norm_gradient, hfn_fd]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (mov2eChi_nonneg n x)]
        calc mov2eChi d n x * ‖fderiv ℝ f x‖ ≤ 1 * ‖fderiv ℝ f x‖ :=
              mul_le_mul_of_nonneg_right (mov2eChi_le_one n x) (norm_nonneg _)
          _ = a := one_mul _
      · rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hK n x) (abs_nonneg _)
    have hn0 : 0 ≤ ‖gradient (fn n) x‖ := norm_nonneg _
    have hb0 : 0 ≤ b := mul_nonneg (abs_nonneg _) (div_nonneg hK0 (by positivity))
    have ha0 : 0 ≤ a := norm_nonneg _
    have key : (a + b) ^ 2 ≤ (1 + ε) * a ^ 2 + (1 + 1 / ε) * b ^ 2 := by
      have e : (1 + ε) * a ^ 2 + (1 + 1 / ε) * b ^ 2 - (a + b) ^ 2 = (ε * a - b) ^ 2 / ε := by
        field_simp; ring
      have h2 : 0 ≤ (ε * a - b) ^ 2 / ε := by positivity
      linarith
    have h3 : ‖gradient (fn n) x‖ ^ 2 ≤ (a + b) ^ 2 := pow_le_pow_left₀ hn0 h1 2
    have h4 : b ^ 2 = (K / ((n : ℝ) + 1)) ^ 2 * f x ^ 2 := by
      rw [hb, mul_pow, sq_abs]; ring
    have h5 : a ^ 2 = ‖gradient f x‖ ^ 2 := by rw [ha, mov2e_norm_gradient]
    calc ‖gradient (fn n) x‖ ^ 2 ≤ (a + b) ^ 2 := h3
      _ ≤ (1 + ε) * a ^ 2 + (1 + 1 / ε) * b ^ 2 := key
      _ = _ := by rw [h4, h5]; ring
  -- integral bound
  have hint : ∀ ε : ℝ, 0 < ε → ∀ n : ℕ, ∫ x, ‖gradient (fn n) x‖ ^ 2 ∂μ ≤
      (1 + ε) * I + (1 + 1 / ε) * (K / ((n : ℝ) + 1)) ^ 2 * F2 := by
    intro ε hε n
    have hr : Integrable (fun x => (1 + ε) * ‖gradient f x‖ ^ 2 +
        (1 + 1 / ε) * (K / ((n : ℝ) + 1)) ^ 2 * f x ^ 2) μ :=
      (hG.const_mul _).add (hfsq.const_mul _)
    calc ∫ x, ‖gradient (fn n) x‖ ^ 2 ∂μ ≤ ∫ x, ((1 + ε) * ‖gradient f x‖ ^ 2 +
          (1 + 1 / ε) * (K / ((n : ℝ) + 1)) ^ 2 * f x ^ 2) ∂μ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _) hr
            (Filter.Eventually.of_forall fun x => hptw ε hε n x)
      _ = _ := by
          rw [integral_add (hG.const_mul _) (hfsq.const_mul _), integral_const_mul, integral_const_mul]
  -- convergence of the variances
  have hv : ∀ X : Euc d → ℝ, MemLp X 2 μ →
      ProbabilityTheory.variance X μ = ∫ x, X x ^ 2 ∂μ - (∫ x, X x ∂μ) ^ 2 := fun X hX => by
    rw [ProbabilityTheory.variance_eq_sub hX]
    simp [Pi.pow_apply]
  have hev : ∀ x : Euc d, ∀ᶠ n : ℕ in atTop, fn n x = f x := fun x =>
    Filter.eventually_atTop.2 ⟨⌈‖x‖⌉₊, fun n hn => hfn_eq n x
      ((Nat.le_ceil _).trans ((by exact_mod_cast hn : (⌈‖x‖⌉₊ : ℝ) ≤ n).trans (by linarith)))⟩
  have hT1 : Tendsto (fun n => ∫ x, fn n x ^ 2 ∂μ) atTop (𝓝 F2) := by
    refine tendsto_integral_of_dominated_convergence (fun x => f x ^ 2)
      (fun n => ((hfn1 n).continuous.pow 2).aestronglyMeasurable) hfsq (fun n => ?_) ?_
    · refine Filter.Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact sq_le_sq.2 (hfn_abs n x)
    · refine Filter.Eventually.of_forall fun x => ?_
      exact tendsto_const_nhds.congr' ((hev x).mono fun n hn => by simp only [hn])
  have hT2 : Tendsto (fun n => ∫ x, fn n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => |f x|)
      (fun n => (hfn1 n).continuous.aestronglyMeasurable) hf1.abs (fun n => ?_) ?_
    · exact Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs]; exact hfn_abs n x
    · refine Filter.Eventually.of_forall fun x => ?_
      exact tendsto_const_nhds.congr' ((hev x).mono fun n hn => by simp only [hn])
  have hvar : Tendsto (fun n => ProbabilityTheory.variance (fn n) μ) atTop
      (𝓝 (ProbabilityTheory.variance f μ)) := by
    rw [hv f hf2]
    have := hT1.sub (hT2.pow 2)
    refine this.congr fun n => ?_
    rw [hv _ (hfn_mem n)]
  -- the limit
  have hε : ∀ ε : ℝ, 0 < ε → c * ProbabilityTheory.variance f μ ≤ (1 + ε) * I := by
    intro ε hε
    have hu : Tendsto (fun n : ℕ => (1 + ε) * I + (1 + 1 / ε) * (K / ((n : ℝ) + 1)) ^ 2 * F2)
        atTop (𝓝 ((1 + ε) * I + 0)) := by
      refine tendsto_const_nhds.add ?_
      have h0 : Tendsto (fun n : ℕ => K * (1 / ((n : ℝ) + 1))) atTop (𝓝 (K * 0)) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.const_mul K
      have h1 := ((h0.pow 2).const_mul (1 + 1 / ε)).mul_const F2
      simp only [mul_zero, zero_pow two_ne_zero, zero_mul] at h1
      refine h1.congr fun n => ?_
      simp only [mul_one_div]
    have := le_of_tendsto_of_tendsto' (hvar.const_mul c) hu (fun n => (hgap n).trans (hint ε hε n))
    simpa using this
  refine le_of_forall_pos_le_add fun ε' hε' => ?_
  have hpos : 0 < ε' / (I + 1) := div_pos hε' (by linarith)
  have := hε _ hpos
  have h2 : ε' / (I + 1) * I ≤ ε' := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
    nlinarith
  linarith


/-! ### Closing with the Poincaré inequality -/

section Closing

variable {s : ℝ} {ρ : Euc d → ℝ}

lemma mov2e_norm_sq_gradient (f : Euc d → ℝ) (x : Euc d) :
    ‖gradient f x‖ ^ 2 = ∑ i : Fin d, (fderiv ℝ f x (EuclideanSpace.single i 1)) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs, sq_abs, movtr_gradient_apply]

/-- `∂_i (W/ψ) = Z_i / ψ`: `ψ ∇(A f) = Z`. -/
lemma mov2e_Af_deriv (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ) (β : ℝ)
    (v : SchwartzMap (Euc d) ℝ) (i : Fin d) (x : Euc d) :
    fderiv ℝ (fun y => mov2eW d s β ρ v y / Real.sqrt (ρ y)) x (EuclideanSpace.single i 1) =
      mov2eZ d s β ρ v i x / Real.sqrt (ρ x) := by
  have hψ0 : ∀ y, Real.sqrt (ρ y) ≠ 0 := fun y => (hρ.psi_pos y).ne'
  have hψs : ContDiff ℝ 1 (fun y => Real.sqrt (ρ y)) := hρ.data.sqrt_smooth.of_le (by exact_mod_cast le_top)
  have hAf : ContDiff ℝ 1 (fun y => mov2eW d s β ρ v y / Real.sqrt (ρ y)) :=
    (mov2e_W_GD hd hs0 hsd hρ hE β v).1.div hψs hψ0
  have hAfd : DifferentiableAt ℝ (fun y => mov2eW d s β ρ v y / Real.sqrt (ρ y)) x :=
    (hAf.differentiable (by norm_num)) x
  have hψd : DifferentiableAt ℝ (fun y => Real.sqrt (ρ y)) x := (hψs.differentiable (by norm_num)) x
  have hprod : (fun y => Real.sqrt (ρ y) * (mov2eW d s β ρ v y / Real.sqrt (ρ y))) = mov2eW d s β ρ v :=
    funext fun y => mul_div_cancel₀ _ (hψ0 y)
  have h1 : fderiv ℝ (fun y => Real.sqrt (ρ y) * (mov2eW d s β ρ v y / Real.sqrt (ρ y))) x =
      Real.sqrt (ρ x) • fderiv ℝ (fun y => mov2eW d s β ρ v y / Real.sqrt (ρ y)) x +
        (mov2eW d s β ρ v x / Real.sqrt (ρ x)) • fderiv ℝ (fun y => Real.sqrt (ρ y)) x :=
    (hψd.hasFDerivAt.mul hAfd.hasFDerivAt).fderiv
  rw [hprod] at h1
  have h2 := congrArg (fun L => L (EuclideanSpace.single i (1 : ℝ))) h1
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul] at h2
  rw [mov2e_W_deriv hd hs0 hsd hρ hE β v i x] at h2
  have hρd : DifferentiableAt ℝ ρ x := (hρ.data.smooth.differentiable (by simp)) x
  rw [HRS.MS.MovForce.mv1_fderiv_sqrt hρd (hρ.pos x), (movtr_gradient_apply (fun y => Real.log (ρ y)) x i).symm] at h2
  have hs := hψ0 x
  have hss : Real.sqrt (ρ x) * Real.sqrt (ρ x) = ρ x := hρ.psi_sq x
  set A := fderiv ℝ (fun y => mov2eW d s β ρ v y / Real.sqrt (ρ y)) x (EuclideanSpace.single i 1) with hA
  rw [eq_div_iff hs]
  generalize Real.sqrt (ρ x) = p at hs h2 ⊢
  have : mov2eW d s β ρ v x / p * (1 / 2 * p * gradient (fun y => Real.log (ρ y)) x i) =
      1 / 2 * gradient (fun y => Real.log (ρ y)) x i * mov2eW d s β ρ v x := by
    field_simp
  rw [this] at h2
  linarith

/-- The `E` form against `W`: `ν E(v) ≤ ∫ W² - (∫ ψ W)²` for `⟨v, ψ⟩ = 0`. -/
lemma mov2e_var_lower (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ)
    (β : ℝ) (hβ : 0 < β) (v : SchwartzMap (Euc d) ℝ) (hmean : ∫ x, Real.sqrt (ρ x) * v x = 0) :
    β⁻¹ * mov2eE d s β ρ v ≤ (∫ x, (mov2eW d s β ρ v x) ^ 2) -
      (∫ x, Real.sqrt (ρ x) * mov2eW d s β ρ v x) ^ 2 := by
  have hd1 : 1 ≤ d := by omega
  have hGB := hρ.schwartz_GB v
  set U : Euc d → ℝ := HRS.Whole.convFun (rieszKernel d s) (mov2eH ρ v) with hU
  have hUPB : Mov2ePB U := (mov2e_U_data hd1 hs0 hsd hρ hE v).2.2.2
  have hψGD := hρ.psi_GD
  have hρGD := hρ.rho_GD
  have hWdef : ∀ x, mov2eW d s β ρ v x = β⁻¹ * v x + Real.sqrt (ρ x) * U x := fun x => rfl
  have hψψ : ∀ x, Real.sqrt (ρ x) * Real.sqrt (ρ x) = ρ x := hρ.psi_sq
  -- integrability
  have iv : Integrable (fun x => v x * v x) := mov2e_schw_int v v
  have ihU : Integrable (fun x => Real.sqrt (ρ x) * v x * U x) :=
    mov2e_conv_mul_integrable hd1 hs0 hsd hGB hGB
  have irUU : Integrable (fun x => ρ x * (U x * U x)) := (hρGD.mul_pb (hUPB.mul hUPB)).integrable
  have irU : Integrable (fun x => ρ x * U x) := (hρGD.mul_pb hUPB).integrable
  have ipv : Integrable (fun x => Real.sqrt (ρ x) * v x) := hGB.integrable hd1
  -- ∫ W²
  have hW2 : ∫ x, (mov2eW d s β ρ v x) ^ 2 =
      (β⁻¹) ^ 2 * (∫ x, v x * v x) + 2 * β⁻¹ * (∫ x, Real.sqrt (ρ x) * v x * U x) +
        ∫ x, ρ x * (U x * U x) := by
    have e : (fun x => (mov2eW d s β ρ v x) ^ 2) = fun x => (β⁻¹) ^ 2 * (v x * v x) +
        2 * β⁻¹ * (Real.sqrt (ρ x) * v x * U x) + ρ x * (U x * U x) := by
      funext x; rw [hWdef]
      have h := hψψ x
      generalize Real.sqrt (ρ x) = p at h ⊢
      rw [← h]; ring
    have j1 : Integrable (fun x => (β⁻¹) ^ 2 * (v x * v x)) := iv.const_mul _
    have j2 : Integrable (fun x => 2 * β⁻¹ * (Real.sqrt (ρ x) * v x * U x)) := ihU.const_mul _
    have j12 : Integrable (fun x => (β⁻¹) ^ 2 * (v x * v x) +
        2 * β⁻¹ * (Real.sqrt (ρ x) * v x * U x)) := j1.add j2
    rw [e, integral_add j12 irUU, integral_add j1 j2, integral_const_mul, integral_const_mul]
  -- ∫ ψ W
  have hψW : ∫ x, Real.sqrt (ρ x) * mov2eW d s β ρ v x = ∫ x, ρ x * U x := by
    have e : (fun x => Real.sqrt (ρ x) * mov2eW d s β ρ v x) =
        fun x => β⁻¹ * (Real.sqrt (ρ x) * v x) + ρ x * U x := by
      funext x; rw [hWdef]
      have h := hψψ x
      generalize Real.sqrt (ρ x) = p at h ⊢
      rw [← h]; ring
    rw [e, integral_add (ipv.const_mul _) irU, integral_const_mul, hmean, mul_zero, zero_add]
  -- Cauchy-Schwarz
  have hcs : (∫ x, ρ x * U x) ^ 2 ≤ ∫ x, ρ x * (U x * U x) := by
    have ha : MemLp (fun x => Real.sqrt (ρ x)) 2 volume :=
      (memLp_two_iff_integrable_sq hρ.data.sqrt_smooth.continuous.aestronglyMeasurable).2
        ((hψGD.mul hψGD).integrable.congr (Filter.Eventually.of_forall fun x => by simp [sq]))
    have hψU : Mov2eGD (fun x => Real.sqrt (ρ x) * U x) := hψGD.mul_pb hUPB
    have hb : MemLp (fun x => Real.sqrt (ρ x) * U x) 2 volume :=
      (memLp_two_iff_integrable_sq hψU.1.continuous.aestronglyMeasurable).2
        ((hψU.mul hψU).integrable.congr (Filter.Eventually.of_forall fun x => by simp [sq]))
    have := mov2e_cs ha hb
    have e1 : ∫ x, Real.sqrt (ρ x) * (Real.sqrt (ρ x) * U x) = ∫ x, ρ x * U x := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only; rw [← mul_assoc, hψψ x]
    have e2 : ∫ x, Real.sqrt (ρ x) ^ 2 = 1 := by
      rw [← hρ.prob.integral_one]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only; rw [sq, hψψ x]
    have e3 : ∫ x, (Real.sqrt (ρ x) * U x) ^ 2 = ∫ x, ρ x * (U x * U x) := by
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only
      have h := hψψ x
      generalize Real.sqrt (ρ x) = p at h ⊢
      rw [← h]; ring
    rw [e1, e2, e3, one_mul] at this
    exact this
  have hP0 := mov2e_pair_nonneg hd hs0 hsd hρ v hmean
  have hP : mov2ePairF d s (fun x => Real.sqrt (ρ x) * v x) (fun x => Real.sqrt (ρ x) * v x) =
      ∫ x, Real.sqrt (ρ x) * v x * U x :=
    mov2ePairF_eq_iter hd1 hs0 hsd hGB hGB
  rw [hW2, hψW]
  unfold mov2eE
  rw [hP] at hP0 ⊢
  have hβ' : 0 < β⁻¹ := inv_pos.2 hβ
  have h1 : (∫ x, v x * v x) = ∫ x, v x ^ 2 := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_); simp [sq]
  rw [h1]
  nlinarith [mul_nonneg hβ'.le hP0]

/-- **Poincaré closing**: `c ν E(v) ≤ ∫ ∑ Z_i² = ∫ ρ |∇ A f|²` for `⟨v, ψ⟩ = 0`. -/
theorem mov2e_poincare_closing (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ)
    (hE : Mov2eEll d ρ) {c : ℝ} (hc : 0 ≤ c) (hP : Mov2ePoinc d ρ c) (β : ℝ) (hβ : 0 < β)
    (v : SchwartzMap (Euc d) ℝ) (hmean : ∫ x, Real.sqrt (ρ x) * v x = 0) :
    c * β⁻¹ * mov2eE d s β ρ v ≤ ∫ x, ∑ i, (mov2eZ d s β ρ v i x) ^ 2 := by
  have hd1 : 1 ≤ d := by omega
  have hprob := mov2e_isProb hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have hψ0 : ∀ y, Real.sqrt (ρ y) ≠ 0 := fun y => (hρ.psi_pos y).ne'
  have hψs : ContDiff ℝ 1 (fun y => Real.sqrt (ρ y)) := hρ.data.sqrt_smooth.of_le (by exact_mod_cast le_top)
  set W := mov2eW d s β ρ v with hW
  set Af : Euc d → ℝ := fun y => W y / Real.sqrt (ρ y) with hAf
  have hWGD := mov2e_W_GD hd1 hs0 hsd hρ hE β v
  have hAf1 : ContDiff ℝ 1 Af := hWGD.1.div hψs hψ0
  have hpt : ∀ x, ρ x * (Af x) ^ 2 = (W x) ^ 2 := fun x => by
    have hs := hψ0 x
    have hss := hρ.psi_sq x
    simp only [hAf]
    generalize Real.sqrt (ρ x) = p at hs hss ⊢
    rw [← hss]; field_simp
  have hgrad : ∀ x, ρ x * ‖gradient Af x‖ ^ 2 = ∑ i, (mov2eZ d s β ρ v i x) ^ 2 := fun x => by
    rw [mov2e_norm_sq_gradient, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hAf, mov2e_Af_deriv hd1 hs0 hsd hρ hE β v i x]
    have hs := hψ0 x
    have hss := hρ.psi_sq x
    generalize Real.sqrt (ρ x) = p at hs hss ⊢
    rw [← hss]; field_simp
  have hZint : Integrable (fun x => ∑ i, (mov2eZ d s β ρ v i x) ^ 2) := by
    refine integrable_finsetSum _ fun i _ => ?_
    have := ((mov2e_Z_GD hd1 hs0 hsd hρ hE β v i).mul (mov2e_Z_GD hd1 hs0 hsd hρ hE β v i)).integrable
    exact this.congr (Filter.Eventually.of_forall fun x => by simp [sq])
  have hW2int : Integrable (fun x => (W x) ^ 2) := by
    refine (hWGD.mul hWGD).integrable.congr (Filter.Eventually.of_forall fun x => ?_)
    show W x * W x = W x ^ 2
    ring
  have hmem : MemLp Af 2 μ := by
    refine (memLp_two_iff_integrable_sq hAf1.continuous.aestronglyMeasurable).2 ?_
    rw [mov2e_integrable_mu hρ]
    exact hW2int.congr (Filter.Eventually.of_forall fun x => (hpt x).symm)
  have hGmu : Integrable (fun x => ‖gradient Af x‖ ^ 2) μ := by
    rw [mov2e_integrable_mu hρ]
    exact hZint.congr (Filter.Eventually.of_forall fun x => (hgrad x).symm)
  have hpo := hP Af hAf1 hmem hGmu
  have hI : ∫ x, ‖gradient Af x‖ ^ 2 ∂μ = ∫ x, ∑ i, (mov2eZ d s β ρ v i x) ^ 2 := by
    rw [mov2e_integral_mu hρ]
    exact integral_congr_ae (Filter.Eventually.of_forall hgrad)
  have hvar : ProbabilityTheory.variance Af μ =
      (∫ x, (W x) ^ 2) - (∫ x, Real.sqrt (ρ x) * W x) ^ 2 := by
    rw [ProbabilityTheory.variance_eq_sub hmem]
    have e1 : ∫ x, (Af ^ 2) x ∂μ = ∫ x, (W x) ^ 2 := by
      rw [mov2e_integral_mu hρ]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simpa [Pi.pow_apply] using hpt x)
    have e2 : ∫ x, Af x ∂μ = ∫ x, Real.sqrt (ρ x) * W x := by
      rw [mov2e_integral_mu hρ]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      have hs := hψ0 x
      have hss := hρ.psi_sq x
      simp only [hAf]
      generalize Real.sqrt (ρ x) = p at hs hss ⊢
      rw [← hss]; field_simp
    simp only [Pi.pow_apply] at e1 ⊢
    rw [e1, e2]
  have hlow := mov2e_var_lower hd hs0 hsd hρ hE β hβ v hmean
  rw [hvar] at hpo
  rw [hI] at hpo
  calc c * β⁻¹ * mov2eE d s β ρ v = c * (β⁻¹ * mov2eE d s β ρ v) := by ring
    _ ≤ c * ((∫ x, (W x) ^ 2) - (∫ x, Real.sqrt (ρ x) * W x) ^ 2) := mul_le_mul_of_nonneg_left hlow hc
    _ ≤ _ := hpo

end Closing


/-! ### The energy along an `L²`-differentiable path -/

section Path

open Asymptotics

variable {s : ℝ} {ρ : Euc d → ℝ}

lemma mov2e_inner_toLp {a b : Euc d → ℝ} (ha : MemLp a 2 volume) (hb : MemLp b 2 volume) :
    inner ℝ (ha.toLp a) (hb.toLp b) = ∫ x, a x * b x := by
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [ha.coeFn_toLp, hb.coeFn_toLp] with x h1 h2
  rw [h1, h2]
  simp [mul_comm]

/-- The `L²` element of `W_u`. -/
def mov2eWl (d : ℕ) (s β : ℝ) (ρ : Euc d → ℝ) (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ)
    (hE : Mov2eEll d ρ) (u : SchwartzMap (Euc d) ℝ) : Lp ℝ 2 (volume : Measure (Euc d)) :=
  (mov2e_W_memLp hd hs0 hsd hρ hE β u).toLp _

/-- **Expansion of the energy through the `L²` pairing**: for Schwartz `a, b`,
`E(a) = E(b) + 2 ⟨W_b, a - b⟩_{L²} + E(a - b)`. -/
lemma mov2e_E_toLp (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ) (β : ℝ)
    (a b : SchwartzMap (Euc d) ℝ) :
    mov2eE d s β ρ a = mov2eE d s β ρ b +
      2 * inner ℝ (mov2eWl d s β ρ hd hs0 hsd hρ hE b) (a.toLp 2 volume - b.toLp 2 volume) +
      mov2eE d s β ρ ⇑(a - b) := by
  have h := mov2e_E_expand hd hs0 hsd hρ β b (a - b)
  have e1 : (fun x => b x + (a - b) x) = ⇑a := by funext x; simp
  rw [e1] at h
  rw [h]
  have e2 : a.toLp 2 volume - b.toLp 2 volume = (a - b).toLp 2 volume := by
    have := (SchwartzMap.toLpCLM ℝ ℝ 2 (volume : Measure (Euc d))).map_sub a b
    simpa using this.symm
  rw [e2]
  have e3 : inner ℝ (mov2eWl d s β ρ hd hs0 hsd hρ hE b) ((a - b).toLp 2 volume) =
      ∫ x, (a - b) x * mov2eW d s β ρ b x := by
    unfold mov2eWl
    rw [SchwartzMap.toLp]
    rw [mov2e_inner_toLp (mov2e_W_memLp hd hs0 hsd hρ hE β b) ((a - b).memLp 2 volume)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    ring
  rw [e3]

lemma mov2e_toLp_norm_sq (a : SchwartzMap (Euc d) ℝ) : ‖a.toLp 2 volume‖ ^ 2 = ∫ x, a x ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  have := mov2e_inner_toLp (a.memLp 2 volume) (a.memLp 2 volume)
  rw [SchwartzMap.toLp]
  rw [this]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  ring


/-- Continuity of the energy along an `L²`-continuous path of Schwartz functions. -/
theorem mov2e_E_continuousWithinAt (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ)
    (hE : Mov2eEll d ρ) (β : ℝ) (u : ℝ → SchwartzMap (Euc d) ℝ) (S : Set ℝ) (t : ℝ)
    (hu : ContinuousWithinAt (fun τ => (u τ).toLp 2 volume) S t) :
    ContinuousWithinAt (fun τ => mov2eE d s β ρ (u τ)) S t := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨M, hM0, hM⟩ := mov2e_E_le hd hs0 hsd hρ β
  set Cb : ℝ := |β⁻¹| + M with hCb
  set Wl := mov2eWl d s β ρ hd1 hs0 hsd hρ hE (u t) with hWl
  have hn : Tendsto (fun τ => ‖(u τ).toLp 2 volume - (u t).toLp 2 volume‖) (𝓝[S] t) (𝓝 0) := by
    have := hu.tendsto.sub_const ((u t).toLp 2 volume)
    simpa using this.norm
  have hb : ∀ τ, |mov2eE d s β ρ (u τ) - mov2eE d s β ρ (u t)| ≤
      2 * ‖Wl‖ * ‖(u τ).toLp 2 volume - (u t).toLp 2 volume‖ +
        Cb * ‖(u τ).toLp 2 volume - (u t).toLp 2 volume‖ ^ 2 := by
    intro τ
    have h := mov2e_E_toLp hd1 hs0 hsd hρ hE β (u τ) (u t)
    have h1 : |inner ℝ Wl ((u τ).toLp 2 volume - (u t).toLp 2 volume)| ≤
        ‖Wl‖ * ‖(u τ).toLp 2 volume - (u t).toLp 2 volume‖ := by
      have := abs_real_inner_le_norm Wl ((u τ).toLp 2 volume - (u t).toLp 2 volume)
      exact this
    have h2 : |mov2eE d s β ρ ⇑(u τ - u t)| ≤ Cb * ‖(u τ).toLp 2 volume - (u t).toLp 2 volume‖ ^ 2 := by
      have e2 : (u τ).toLp 2 volume - (u t).toLp 2 volume = (u τ - u t).toLp 2 volume := by
        have := (SchwartzMap.toLpCLM ℝ ℝ 2 (volume : Measure (Euc d))).map_sub (u τ) (u t)
        simpa using this.symm
      rw [e2, mov2e_toLp_norm_sq]
      exact hM _
    have e3 : mov2eE d s β ρ (u τ) - mov2eE d s β ρ (u t) =
        2 * inner ℝ Wl ((u τ).toLp 2 volume - (u t).toLp 2 volume) + mov2eE d s β ρ ⇑(u τ - u t) := by
      linarith
    rw [e3]
    calc _ ≤ |2 * inner ℝ Wl ((u τ).toLp 2 volume - (u t).toLp 2 volume)| + |mov2eE d s β ρ ⇑(u τ - u t)| :=
          abs_add_le _ _
      _ ≤ 2 * (‖Wl‖ * ‖(u τ).toLp 2 volume - (u t).toLp 2 volume‖) +
            Cb * ‖(u τ).toLp 2 volume - (u t).toLp 2 volume‖ ^ 2 := by
          rw [abs_mul, abs_two]
          exact add_le_add (mul_le_mul_of_nonneg_left h1 (by norm_num)) h2
      _ = _ := by ring
  have hlim : Tendsto (fun τ => 2 * ‖Wl‖ * ‖(u τ).toLp 2 volume - (u t).toLp 2 volume‖ +
      Cb * ‖(u τ).toLp 2 volume - (u t).toLp 2 volume‖ ^ 2) (𝓝[S] t) (𝓝 0) := by
    have := (hn.const_mul (2 * ‖Wl‖)).add ((hn.pow 2).const_mul Cb)
    simpa using this
  unfold ContinuousWithinAt
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun τ => norm_nonneg _) (fun τ => by rw [Real.norm_eq_abs]; exact hb τ) hlim

/-- **Right derivative of the energy along the flow**:
`d/dτ E(u(τ)) = -2 ∫ ∑ Z_i²` at `τ = t` (right derivative) when `τ ↦ u(τ) ∈ L²` has right derivative `-S u(t)`. -/
theorem mov2e_E_hasDerivWithinAt (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ)
    (hE : Mov2eEll d ρ) (β : ℝ) (u : ℝ → SchwartzMap (Euc d) ℝ) (t : ℝ)
    (w : Lp ℝ 2 (volume : Measure (Euc d)))
    (hw : ∀ᵐ x ∂(volume : Measure (Euc d)), w x = movS d s β ρ (u t) x)
    (hder : HasDerivWithinAt (fun τ => (u τ).toLp 2 volume) (-w) (Set.Ici t) t) :
    HasDerivWithinAt (fun τ => mov2eE d s β ρ (u τ))
      (-2 * ∫ x, ∑ i, (mov2eZ d s β ρ (u t) i x) ^ 2) (Set.Ici t) t := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨M, hM0, hM⟩ := mov2e_E_le hd hs0 hsd hρ β
  set Cb : ℝ := |β⁻¹| + M with hCb
  set Wl := mov2eWl d s β ρ hd1 hs0 hsd hρ hE (u t) with hWl
  set A : ℝ → Lp ℝ 2 (volume : Measure (Euc d)) := fun τ => (u τ).toLp 2 volume with hA
  -- the pairing
  have hg : HasDerivWithinAt (fun τ => inner ℝ Wl (A τ)) (inner ℝ Wl (-w)) (Set.Ici t) t := by
    have := (innerSL ℝ Wl).hasFDerivAt.comp_hasDerivWithinAt t hder
    refine this.congr_deriv ?_
    simp
  -- identification of the derivative
  have hD : inner ℝ Wl (-w) = -∫ x, ∑ i, (mov2eZ d s β ρ (u t) i x) ^ 2 := by
    rw [inner_neg_right]
    congr 1
    have hmem : MemLp (movS d s β ρ (u t)) 2 volume := by
      refine (Lp.memLp w).ae_eq ?_
      filter_upwards [hw] with x hx using hx
    have e1 : inner ℝ Wl w = ∫ x, mov2eW d s β ρ (u t) x * w x := by
      rw [MeasureTheory.L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [(mov2e_W_memLp hd1 hs0 hsd hρ hE β (u t)).coeFn_toLp] with x hx
      rw [hWl, mov2eWl, hx]
      simp [mul_comm]
    rw [e1, ← (mov2e_energy_identity hd1 hs0 hsd hρ hE β (u t)).2]
    refine integral_congr_ae ?_
    filter_upwards [hw] with x hx
    rw [hx]
  -- remainder
  have hbig : (fun τ => ‖A τ - A t‖) =O[𝓝[Set.Ici t] t] (fun τ => τ - t) := by
    have := hder.hasFDerivWithinAt.isBigO_sub
    exact this.norm_left
  have hlit : (fun τ => ‖A τ - A t‖) =o[𝓝[Set.Ici t] t] (fun _ => (1 : ℝ)) := by
    rw [isLittleO_one_iff]
    have := hder.continuousWithinAt.tendsto.sub_const (A t)
    simpa using this.norm
  have hprod : (fun τ => ‖A τ - A t‖ * ‖A τ - A t‖) =o[𝓝[Set.Ici t] t] (fun τ => (τ - t) * 1) :=
    hbig.mul_isLittleO hlit
  have hrem : (fun τ => mov2eE d s β ρ ⇑(u τ - u t)) =o[𝓝[Set.Ici t] t] (fun τ => τ - t) := by
    have hle : (fun τ => mov2eE d s β ρ ⇑(u τ - u t)) =O[𝓝[Set.Ici t] t]
        (fun τ => ‖A τ - A t‖ * ‖A τ - A t‖) := by
      refine IsBigO.of_bound Cb (Filter.Eventually.of_forall fun τ => ?_)
      have e2 : A τ - A t = (u τ - u t).toLp 2 volume := by
        have := (SchwartzMap.toLpCLM ℝ ℝ 2 (volume : Measure (Euc d))).map_sub (u τ) (u t)
        simpa [hA] using this.symm
      have h1 := hM (u τ - u t)
      have h2 : ∫ x, (u τ - u t) x ^ 2 = ‖A τ - A t‖ ^ 2 := by rw [e2, mov2e_toLp_norm_sq]
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_self_nonneg ‖A τ - A t‖)]
      calc |mov2eE d s β ρ ⇑(u τ - u t)| ≤ Cb * ∫ x, (u τ - u t) x ^ 2 := h1
        _ = Cb * (‖A τ - A t‖ * ‖A τ - A t‖) := by rw [h2]; ring
    exact (hle.trans_isLittleO hprod).congr_right fun τ => mul_one _
  -- assemble
  rw [hasDerivWithinAt_iff_isLittleO]
  have hg' := hg.isLittleO
  have hkey : ∀ τ, mov2eE d s β ρ (u τ) - mov2eE d s β ρ (u t) -
      (τ - t) • (-2 * ∫ x, ∑ i, (mov2eZ d s β ρ (u t) i x) ^ 2) =
      2 * (inner ℝ Wl (A τ) - inner ℝ Wl (A t) - (τ - t) • inner ℝ Wl (-w)) +
        mov2eE d s β ρ ⇑(u τ - u t) := by
    intro τ
    have h := mov2e_E_toLp hd1 hs0 hsd hρ hE β (u τ) (u t)
    rw [← inner_sub_right] at *
    have : -2 * ∫ x, ∑ i, (mov2eZ d s β ρ (u t) i x) ^ 2 = 2 * inner ℝ Wl (-w) := by rw [hD]; ring
    rw [this]
    simp only [smul_eq_mul]
    have h' : mov2eE d s β ρ (u τ) = mov2eE d s β ρ (u t) +
        2 * inner ℝ Wl (A τ - A t) + mov2eE d s β ρ ⇑(u τ - u t) := h
    rw [h', inner_sub_right]
    ring
  simp_rw [hkey]
  exact (hg'.const_mul_left 2).add hrem

end Path

/-! ### Gronwall and exponential decay -/

section Decay

variable {s : ℝ} {ρ : Euc d → ℝ}

/-- **Exponential decay of the energy**: let `u(τ)` be Schwartz, with `⟨u(τ), ψ⟩ = 0`, `τ ↦ u(τ) ∈ L²` continuous on
`[0, ∞)` with right derivative `-w(t)`, `w(t) = S u(t)` a.e. (the pointwise formula `movS`) at every `t ≥ 0`.  Then,
with the Poincaré constant `c`, `E(u(t)) ≤ e^{-2 c ν t} E(u(0))`, `ν = β⁻¹`. -/
theorem mov2e_energy_decay (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ)
    (hE : Mov2eEll d ρ) {c : ℝ} (hc : 0 ≤ c) (hP : Mov2ePoinc d ρ c) (β : ℝ) (hβ : 0 < β)
    (u : ℝ → SchwartzMap (Euc d) ℝ)
    (hmean : ∀ t, 0 ≤ t → ∫ x, Real.sqrt (ρ x) * u t x = 0)
    (hcont : ContinuousOn (fun τ => (u τ).toLp 2 volume) (Set.Ici 0))
    (hder : ∀ t, 0 ≤ t → ∃ w : Lp ℝ 2 (volume : Measure (Euc d)),
      (∀ᵐ x ∂(volume : Measure (Euc d)), w x = movS d s β ρ (u t) x) ∧
        HasDerivWithinAt (fun τ => (u τ).toLp 2 volume) (-w) (Set.Ici t) t) :
    ∀ t, 0 ≤ t → mov2eE d s β ρ (u t) ≤ Real.exp (-(2 * c * β⁻¹) * t) * mov2eE d s β ρ (u 0) := by
  intro t ht
  set Q : ℝ → ℝ := fun τ => mov2eE d s β ρ (u τ) with hQ
  have hQc : ContinuousOn Q (Set.Icc 0 t) := fun σ hσ =>
    (mov2e_E_continuousWithinAt hd hs0 hsd hρ hE β u (Set.Ici 0) σ (hcont σ hσ.1)).mono
      (fun τ hτ => hτ.1)
  have hD : ∀ σ, 0 ≤ σ → HasDerivWithinAt Q (-2 * ∫ x, ∑ i, (mov2eZ d s β ρ (u σ) i x) ^ 2) (Set.Ici σ) σ := by
    intro σ hσ
    obtain ⟨w, hw, hwd⟩ := hder σ hσ
    exact mov2e_E_hasDerivWithinAt hd hs0 hsd hρ hE β u σ w hw hwd
  have hbound : ∀ σ ∈ Set.Ico 0 t, -2 * (∫ x, ∑ i, (mov2eZ d s β ρ (u σ) i x) ^ 2) ≤
      (-(2 * c * β⁻¹)) * Q σ + 0 := by
    intro σ hσ
    have := mov2e_poincare_closing hd hs0 hsd hρ hE hc hP β hβ (u σ) (hmean σ hσ.1)
    simp only [hQ]
    nlinarith
  have := le_gronwallBound_of_liminf_deriv_right_le (f := Q)
    (f' := fun σ => -2 * ∫ x, ∑ i, (mov2eZ d s β ρ (u σ) i x) ^ 2) (δ := Q 0) (K := -(2 * c * β⁻¹)) (ε := 0)
    (a := 0) (b := t) hQc
    (fun σ hσ r hr => (hD σ hσ.1).liminf_right_slope_le hr) le_rfl hbound t ⟨ht, le_rfl⟩
  rw [gronwallBound_ε0, sub_zero, mul_comm] at this
  exact this

/-- The thermal instance of the abstract hypotheses (MOV-0, `GapExt`). -/
theorem mov2e_thermal (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β q : ℝ} (hβ : 0 < β) (hq : 0 < q)
    {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s q β ρ) :
    Mov2eRho d ρ ∧ Mov2eEll d ρ ∧ ∃ c : ℝ, 0 < c ∧ Mov2ePoincBdd d ρ c := by
  obtain ⟨B, -, hR, -⟩ := HRS.MS.Mov0.mv0_gapref hd hs0 hsd hq hβ hρ
  have hq' : 0 < β * q := mul_pos hβ hq
  obtain ⟨hψs, hgrad, c, hc, hψb⟩ := HRS.MS.Mov0.mv0_sqrt_gauss hq' hR
  obtain ⟨hdlog, M0, hM0⟩ := HRS.MS.Mov0.mv0_dlog_bounds hq'.le hR
  have hM00 : 0 ≤ M0 := by
    have := hM0 0
    simp only [norm_zero, mul_zero, zero_add] at this
    exact (norm_nonneg _).trans this
  have hfs : ContDiff ℝ ∞ (fun x => gradient (fun y => Real.log (ρ y)) x) := by
    have : (fun x => gradient (fun y => Real.log (ρ y)) x) = fun x => (-(β * q)) • x + B x :=
      funext hgrad
    rw [this]
    exact (contDiff_id.const_smul (-(β * q))).add (HRS.MS.Mov0.mov0_B_smooth hR)
  refine ⟨⟨⟨hR.pos, hR.smooth, fun k => (hψb k).elim fun C hC => ⟨C, c, hc, hC⟩⟩, hρ.1.1⟩,
    ⟨⟨c, β * q, M0, hc, hq'.le, hM00, hψb, hfs, hM0, hdlog⟩⟩, ?_⟩
  obtain ⟨Mb, hMb⟩ := hR.cb 2
  obtain ⟨c', hc', hc''⟩ := HRS.MS.Gap.gap_ext hR hq' hMb
  exact ⟨c', hc', fun f hf hbd hmem => hc'' f hf hbd hmem⟩

end Decay

/-! ### The theorems for a thermal equilibrium -/

section Thermal

variable {s : ℝ}

/-- **The sandwich `ν I ≤ A ≤ C I`** (S6.2, exponential-decay paragraph): for a thermal equilibrium `ρ` there is `M ≥ 0`
with `ν ‖v‖² ≤ E(v) ≤ (ν + M) ‖v‖²` for every Schwartz `v` with `⟨v, √ρ⟩ = 0`, where
`E(v) = ν ∫ v² + ∬ g(x-y) (√ρ v)(x) (√ρ v)(y) dx dy = ⟨f, (ν I + K) f⟩_{L²(ρ)}`, `f = v/√ρ`, `ν = β⁻¹`,
`K = ` the (projected) convolution with `g = rieszKernel d s`.  All `0 ≤ s < d`: Schur test for `s > 0`,
Hilbert-Schmidt for `s = 0`. -/
theorem mov2e_sandwich (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β q : ℝ) (hβ : 0 < β) (hq : 0 < q)
    (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ v : SchwartzMap (Euc d) ℝ, ∫ x, Real.sqrt (ρ x) * v x = 0 →
      β⁻¹ * ∫ x, v x ^ 2 ≤ mov2eE d s β ρ v ∧
        mov2eE d s β ρ v ≤ (β⁻¹ + M) * ∫ x, v x ^ 2 := by
  obtain ⟨hR, -, -⟩ := mov2e_thermal hd hs0 hsd hβ hq hρ
  exact mov2e_E_bounds hd hs0 hsd hR β hβ

/-- The Poincaré inequality for `C¹` functions in `L²(μ)` with `|∇f|² ∈ L¹(μ)` (all `0 ≤ s < d`): `Gap.gap_ext`
(`reflection_gap_poincare_proof` for `s = 0`, `euc_thermal_gaussian_bounds_proof` bullet 2 for `s > 0`) plus the
cutoff extension `mov2e_poinc_ext`. -/
theorem mov2e_poincare (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β q : ℝ) (hβ : 0 < β) (hq : 0 < q)
    (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ) :
    ∃ c : ℝ, 0 < c ∧ ∀ f : Euc d → ℝ, ContDiff ℝ 1 f → MemLp f 2 (HRS.Whole.withDensityReal ρ) →
      Integrable (fun x => ‖gradient f x‖ ^ 2) (HRS.Whole.withDensityReal ρ) →
      c * ProbabilityTheory.variance f (HRS.Whole.withDensityReal ρ) ≤
        ∫ x, ‖gradient f x‖ ^ 2 ∂(HRS.Whole.withDensityReal ρ) := by
  obtain ⟨hR, -, c, hc, hP⟩ := mov2e_thermal hd hs0 hsd hβ hq hρ
  exact ⟨c, hc, mov2e_poinc_ext hR hP⟩

/-- **Exponential decay of the linearised flow in `L²` along Schwartz classical solutions** (S6.2, TeX L4278-4343, the
energy estimate `d/dt ⟨f, A f⟩ = -2 ∫ ρ |∇ A f|² ≤ -2 λ_* ν ⟨f, A f⟩` and the equivalence `ν I ≤ A ≤ C I`).

For a thermal equilibrium `ρ` there are `lam > 0`, `C ≥ 1` such that: if `u(t)`, `t ≥ 0`, are Schwartz functions with
`⟨u(t), √ρ⟩ = 0`, `t ↦ u(t) ∈ L²` continuous on `[0, ∞)` and, at every `t ≥ 0`, with right derivative `-w(t)` in `L²`
where `w(t) = movS u(t)` a.e. (i.e. `d/dt u = -S u`, classical solutions in the Schwartz core), then
`‖u(t)‖₂ ≤ C e^{-lam t} ‖u(0)‖₂`.  The constants depend only on `(d, s, β, q)`. -/
theorem mov2e_decay (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β q : ℝ) (hβ : 0 < β) (hq : 0 < q)
    (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ) :
    ∃ lam : ℝ, 0 < lam ∧ ∃ C : ℝ, 1 ≤ C ∧ ∀ u : ℝ → SchwartzMap (Euc d) ℝ,
      (∀ t, 0 ≤ t → ∫ x, Real.sqrt (ρ x) * u t x = 0) →
      ContinuousOn (fun τ => (u τ).toLp 2 volume) (Set.Ici 0) →
      (∀ t, 0 ≤ t → ∃ w : Lp ℝ 2 (volume : Measure (Euc d)),
        (∀ᵐ x ∂(volume : Measure (Euc d)), w x = movS d s β ρ (u t) x) ∧
          HasDerivWithinAt (fun τ => (u τ).toLp 2 volume) (-w) (Set.Ici t) t) →
      ∀ t, 0 ≤ t → ‖(u t).toLp 2 volume‖ ≤ C * Real.exp (-lam * t) * ‖(u 0).toLp 2 volume‖ := by
  obtain ⟨hR, hE, c, hc, hP⟩ := mov2e_thermal hd hs0 hsd hβ hq hρ
  have hP' := mov2e_poinc_ext hR hP
  obtain ⟨M, hM0, hM⟩ := mov2e_E_bounds hd hs0 hsd hR β hβ
  have hβ' : 0 < β⁻¹ := inv_pos.2 hβ
  have hC0 : 1 ≤ 1 + β * M := by nlinarith
  refine ⟨c * β⁻¹, mul_pos hc hβ', Real.sqrt (1 + β * M), Real.one_le_sqrt.2 hC0, fun u hmean hcont hder t ht => ?_⟩
  have hdec := mov2e_energy_decay hd hs0 hsd hR hE hc.le hP' β hβ u hmean hcont hder t ht
  obtain ⟨hlo, -⟩ := hM (u t) (hmean t ht)
  obtain ⟨-, hhi⟩ := hM (u 0) (hmean 0 le_rfl)
  rw [← mov2e_toLp_norm_sq] at hlo hhi
  set a : ℝ := ‖(u t).toLp 2 volume‖ with ha
  set b : ℝ := ‖(u 0).toLp 2 volume‖ with hb
  set X : ℝ := Real.exp (-(c * β⁻¹) * t) with hX
  have hX0 : 0 ≤ X := (Real.exp_pos _).le
  have hexp : Real.exp (-(2 * c * β⁻¹) * t) = X ^ 2 := by
    rw [hX, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hsq : a ^ 2 ≤ ((Real.sqrt (1 + β * M)) * X * b) ^ 2 := by
    have h1 : β⁻¹ * a ^ 2 ≤ X ^ 2 * ((β⁻¹ + M) * b ^ 2) := by
      calc β⁻¹ * a ^ 2 ≤ mov2eE d s β ρ (u t) := hlo
        _ ≤ Real.exp (-(2 * c * β⁻¹) * t) * mov2eE d s β ρ (u 0) := hdec
        _ ≤ X ^ 2 * ((β⁻¹ + M) * b ^ 2) := by
            rw [hexp]
            exact mul_le_mul_of_nonneg_left hhi (by positivity)
    have h2 : a ^ 2 ≤ β * (X ^ 2 * ((β⁻¹ + M) * b ^ 2)) := by
      have := mul_le_mul_of_nonneg_left h1 hβ.le
      rwa [← mul_assoc, mul_inv_cancel₀ hβ.ne', one_mul] at this
    calc a ^ 2 ≤ β * (X ^ 2 * ((β⁻¹ + M) * b ^ 2)) := h2
      _ = (1 + β * M) * X ^ 2 * b ^ 2 := by
          have h0 : β * β⁻¹ = 1 := mul_inv_cancel₀ hβ.ne'
          linear_combination (X ^ 2 * b ^ 2) * h0
      _ = ((Real.sqrt (1 + β * M)) * X * b) ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt (by linarith)]
  have hrhs : 0 ≤ (Real.sqrt (1 + β * M)) * X * b := by positivity
  have := (pow_le_pow_iff_left₀ (norm_nonneg _) hrhs (two_ne_zero)).1 hsq
  calc a ≤ (Real.sqrt (1 + β * M)) * X * b := this
    _ = Real.sqrt (1 + β * M) * Real.exp (-(c * β⁻¹) * t) * b := rfl

end Thermal

end HRS.MS.MovDec

end
