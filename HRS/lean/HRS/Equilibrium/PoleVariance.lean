/-
# HRS.Equilibrium.PoleVariance -- the variance clause of Lemma 4.1 (EQ-01a-3)

Lemma 4.1 `M:A:lem:pole` (source lines 3564-3577), variance clause `A:eq:pole-variance`:
`Var_{P_n^{x,t}}[∑ f(y_i)] ≤ C n ∫ |f|² e^{-tλ g(x-y)} dμ`, `n = N-1`, `λ = β/N`.

## Route (source proof, TeX lines 3583-3620, paragraph 2)

The pole law is `P = (μ^{⊗n}).tilted (EPole g)` (`poleLaw_eq_tilted`).  `g` is replaced by the heat split
`g_S = g_L + q - c` (`HeatSplit`, a.e. equal: `EPole_ae_eq`), `g_L(x-y) = ⟪Ψ x, Ψ y⟫` a finite positive
block, `q ≥ 0` with row bound `γ = Λ c` small (`exists_split_params`: `KappaSmall β γ`).

1. `exponent_identity`: with `S = ∑ Ψ(y_i)`, `m = μ(Ψ)`, `λ(n+1) = β`, and the calibration `t_N = -β Ξ̄_N` of the
   *unpoled* `(n+1)`-particle weak reference `R_{n+1}` (`CalibratedReference`),
   `EPole = E_ref^{x,t} - (λ/2)|S + Ψ x - (n+1)(m + Ξ̄)|² + (1-t) λ ⟨Ψ x, S⟩ + C0`.
   Here `E_ref^{x,t}` is the exponent of the weak ensemble `R^{x,t}` (`Rpole`) with pair kernel `q`, one-body field
   `φ - tλ q(· - x)` (`psiPole`: the pole is a fractional pin; it keeps `IsField`, row sums, `κ` unchanged).
   Hence `P = R^{x,t}.tilted (aPole)` (`pole_tilted_eq`).
2. The perturbation `(1-t)λ⟨Ψ x, S⟩` is bounded by `β g_L(0)`; the Gaussian factor is `≤ 1`; by Jensen
   (`tilted_le_smul_jensen`) `dP/dR^{x,t} ≤ exp(2β g_L(0) + (λ/2) E|S + Ψ x - (n+1)(m + Ξ̄)|²)`.
3. `Esq_le`: that second moment is `≤ 100 (n+1) g_L(0)`:  variance part `2 n g_L(0)` by Wu's linear inequality for the
   exchangeable weak ensemble with a general field (`field_second_moment_vec`), mean part `O(1)` by the Rebeschini-van
   Handel comparison (`mean_norm_le`): the marginals of `R^{x,t}` and of the conditional laws of `R_{n+1}` given one
   coordinate (a pinned ensemble, `rvh_pin_comparison`) differ by `O(1/N)` in total variation
   (`marginal_tv_le`, `pin_pole_event`).  So `dP/dR^{x,t} ≤ e^{52 β g_L(0)}` (`pole_le_Rpole`).
4. `pole_evariance_le`: `Var_P ≤ e^{52βg_L(0)} Var_R ≤ e^{52βg_L(0)} 2n ∫ f² dπ`, `π` the one-point marginal of
   `R^{x,t}`, `dπ/dμ ≤ e^{βγ + ψ_{x,t}}` (`field_marginal_le`), and `ψ_{x,t} ≤ βγ + 1 + β g_L(0) - tλ g(x - ·)`
   (`riesz_pole_variance_large`).
5. The smallness `|t_N·Ξ| ≤ 1` for `N` large is `exists_small_calib` (`ReferenceSmallness`, glued by
   `R0_eq_R0small`, `integral_empXi_R0`).  For the finitely many remaining `N`: Cauchy-Schwarz and the one-coordinate
   density bound (`riesz_pole_variance_crude`).  Final assembly: `pole_variance_clause_final`.
-/
import HRS.Equilibrium.PoleCavity
import HRS.Equilibrium.CalibratedReference
import HRS.Equilibrium.ReferenceSmallness

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.External

namespace PoleVar

open HRS Calib

/-! ### Stage 0: weak ensembles with a general one-body field -/

section GenField

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]
  {V : WeakPotential μ} {ψ : E → ℝ} {M M₁ lam : ℝ}

/-- Wu's linear inequality for the exchangeable weak ensemble with an arbitrary one-body field
(`IsField`), with the Dobrushin row sums `≤ 1/2`. -/
theorem field_linear_variance_symm {n : ℕ} [NeZero n] (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam)
    {Λ : ℝ} (hΛ : M₁ + lam * n * V.γ ≤ Λ)
    (hrow : ∀ i : Fin n, ∑ _j ∈ Finset.univ.erase i, 4 * Real.exp (M + Λ) * lam * V.γ ≤ 1 / 2)
    (f : E → ℝ) (hf : Measurable f) :
    evariance (fun y : Fin n → E => ∑ i, f (y i)) (fieldLaw V ψ lam n)
      ≤ 2 * n * evariance f ((fieldLaw V ψ lam n).map (fun x => x 0)) := by
  have hc0 : 0 ≤ 4 * Real.exp (M + Λ) * lam * V.γ := by
    have := V.γ_nonneg; positivity
  exact wu_linear_symm μ (fieldDensity V ψ lam n) (measurable_fieldDensity hψ.measurable V _ n)
    (fieldDensity_pos hψ hlam n) _ (fieldDensity_le hψ hlam n) (lintegral_fieldDensity hψ hlam n)
    (fun _ _ => 4 * Real.exp (M + Λ) * lam * V.γ) (fun _ _ => hc0)
    (fun i j hij x y hxy A hA => abs_siteKernel_sub_le (V := V) hψ hlam hΛ hij hxy hA)
    hrow (fun σ y => fieldDensity_comp_perm V _ _ σ y) f hf

/-- The one-coordinate marginal of the weak ensemble is dominated by `e^{Λ} e^{ψ} μ`. -/
theorem field_marginal_le {n : ℕ} (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam)
    {Λ : ℝ} (hΛ : M₁ + lam * n * V.γ ≤ Λ) (i : Fin n) {A : Set E} (hA : MeasurableSet A) :
    ((fieldLaw V ψ lam n).map (fun y => y i)) A
      ≤ ∫⁻ z in A, ENNReal.ofReal (Real.exp (Λ + ψ z)) ∂μ := by
  have : IsProbabilityMeasure (fieldLaw V ψ lam n) := (fieldSpec (V := V) hψ hlam n).isProb
  have hW := measurable_fieldDensity hψ.measurable V lam n
  have hS : MeasurableSet ((fun y : Fin n → E => y i) ⁻¹' A) := measurable_pi_apply i hA
  have hinv := invariant_density (μ := μ) (W := fieldDensity V ψ lam n) hW
    (fieldDensity_pos hψ hlam n) (fieldDensity_le hψ hlam n) i
    (φ := ((fun y : Fin n → E => y i) ⁻¹' A).indicator 1) (measurable_const.indicator hS)
  rw [Measure.map_apply (measurable_pi_apply i) hA]
  have hR : (fieldLaw V ψ lam n) ((fun y : Fin n → E => y i) ⁻¹' A)
      = ∫⁻ x, ((fun y : Fin n → E => y i) ⁻¹' A).indicator 1 x ∂(fieldLaw V ψ lam n) := by
    rw [lintegral_indicator_one hS]
  have hbound : ∀ x : Fin n → E,
      ∫⁻ z, ((fun y : Fin n → E => y i) ⁻¹' A).indicator (1 : (Fin n → E) → ℝ≥0∞)
        (Function.update x i z) ∂(siteKernel μ (fieldDensity V ψ lam n) i x)
        ≤ ∫⁻ z in A, ENNReal.ofReal (Real.exp (Λ + ψ z)) ∂μ := by
    intro x
    have hupd : ∀ z, ((fun y : Fin n → E => y i) ⁻¹' A).indicator (1 : (Fin n → E) → ℝ≥0∞)
        (Function.update x i z) = A.indicator 1 z := by
      intro z
      have : (Function.update x i z ∈ (fun y : Fin n → E => y i) ⁻¹' A) ↔ z ∈ A := by
        simp [Set.mem_preimage]
      by_cases hz : z ∈ A
      · rw [Set.indicator_of_mem (this.2 hz), Set.indicator_of_mem hz]; rfl
      · rw [Set.indicator_of_notMem (fun h => hz (this.1 h)), Set.indicator_of_notMem hz]
    simp_rw [hupd]
    rw [lintegral_indicator_one hA, siteKernel_fieldDensity hψ hlam, withDensity_apply _ hA]
    refine lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_
    have h1 := exp_le_integral_siteU (V := V) hψ hlam i x
    have h2 : Real.exp (-Λ) ≤ ∫ z', siteU V ψ lam i x z' ∂μ :=
      le_trans (Real.exp_le_exp.2 (by nlinarith [hψ.ge])) h1
    have hpos : 0 < ∫ z', siteU V ψ lam i x z' ∂μ := integral_siteU_pos hψ hlam i x
    rw [div_le_iff₀ hpos]
    have h3 : siteU V ψ lam i x z ≤ Real.exp (ψ z) := by
      unfold siteU
      refine Real.exp_le_exp.2 ?_
      have := mul_nonneg hlam (sumq_nonneg V i x z); linarith
    calc siteU V ψ lam i x z ≤ Real.exp (ψ z) := h3
      _ = Real.exp (Λ + ψ z) * Real.exp (-Λ) := by rw [← Real.exp_add]; ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
  rw [hR]
  have hinv' : ∫⁻ x, ((fun y : Fin n → E => y i) ⁻¹' A).indicator (1 : (Fin n → E) → ℝ≥0∞) x ∂(fieldLaw V ψ lam n) = _ := hinv.symm
  rw [hinv']
  calc ∫⁻ x, ∫⁻ z, ((fun y : Fin n → E => y i) ⁻¹' A).indicator (1 : (Fin n → E) → ℝ≥0∞)
        (Function.update x i z) ∂(siteKernel μ (fieldDensity V ψ lam n) i x) ∂(fieldLaw V ψ lam n)
      ≤ ∫⁻ _x, ∫⁻ z in A, ENNReal.ofReal (Real.exp (Λ + ψ z)) ∂μ ∂(fieldLaw V ψ lam n) :=
        lintegral_mono hbound
    _ = _ := by simp

/-- Real form of `field_linear_variance_symm` for a bounded `f`. -/
theorem field_linear_variance_real {n : ℕ} [NeZero n] (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam)
    {Λ : ℝ} (hΛ : M₁ + lam * n * V.γ ≤ Λ)
    (hrow : ∀ i : Fin n, ∑ _j ∈ Finset.univ.erase i, 4 * Real.exp (M + Λ) * lam * V.γ ≤ 1 / 2)
    {f : E → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ z, |f z| ≤ B) :
    variance (fun y : Fin n → E => ∑ i, f (y i)) (fieldLaw V ψ lam n)
      ≤ 2 * n * variance f ((fieldLaw V ψ lam n).map (fun x => x 0)) := by
  have hPr : IsProbabilityMeasure (fieldLaw V ψ lam n) := (fieldSpec (V := V) hψ hlam n).isProb
  have hm0 : Measurable (fun y : Fin n → E => y 0) := measurable_pi_apply 0
  have hπ : IsProbabilityMeasure ((fieldLaw V ψ lam n).map (fun x => x 0)) := inferInstance
  have h := field_linear_variance_symm (V := V) hψ hlam hΛ hrow f hf
  have hf2 : MemLp f 2 ((fieldLaw V ψ lam n).map (fun x => x 0)) :=
    MemLp.of_bound hf.aestronglyMeasurable B
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)
  have hF : Measurable fun y : Fin n → E => ∑ i, f (y i) :=
    Finset.measurable_sum _ fun j _ => hf.comp (measurable_pi_apply j)
  have hF2 : MemLp (fun y : Fin n → E => ∑ i, f (y i)) 2 (fieldLaw V ψ lam n) :=
    MemLp.of_bound hF.aestronglyMeasurable (n * B)
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]
        calc |∑ i, f (y i)| ≤ ∑ i, |f (y i)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : Fin n, B := Finset.sum_le_sum fun i _ => hB _
          _ = n * B := by simp)
  rw [← ofReal_variance hf2, ← ofReal_variance hF2] at h
  have h0 : 0 ≤ 2 * (n : ℝ) * variance f ((fieldLaw V ψ lam n).map (fun x => x 0)) :=
    mul_nonneg (by positivity) (variance_nonneg _ _)
  have e : (2 : ℝ≥0∞) * n * ENNReal.ofReal (variance f ((fieldLaw V ψ lam n).map (fun x => x 0)))
      = ENNReal.ofReal (2 * n * variance f ((fieldLaw V ψ lam n).map (fun x => x 0))) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num)]
    simp
  rw [e, ENNReal.ofReal_le_ofReal_iff h0] at h
  exact h

/-- Second moment of a shifted linear statistic. -/
theorem field_second_moment_le {n : ℕ} [NeZero n] (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam)
    {Λ : ℝ} (hΛ : M₁ + lam * n * V.γ ≤ Λ)
    (hrow : ∀ i : Fin n, ∑ _j ∈ Finset.univ.erase i, 4 * Real.exp (M + Λ) * lam * V.γ ≤ 1 / 2)
    {f : E → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ z, |f z| ≤ B) (c : ℝ) :
    ∫ y, (∑ i, f (y i) + c) ^ 2 ∂(fieldLaw V ψ lam n)
      ≤ 2 * n * ∫ y, (f (y 0)) ^ 2 ∂(fieldLaw V ψ lam n)
        + (∫ y, ∑ i, f (y i) ∂(fieldLaw V ψ lam n) + c) ^ 2 := by
  have hPr : IsProbabilityMeasure (fieldLaw V ψ lam n) := (fieldSpec (V := V) hψ hlam n).isProb
  set ν := fieldLaw V ψ lam n with hν
  have hF : Measurable fun y : Fin n → E => ∑ i, f (y i) :=
    Finset.measurable_sum _ fun j _ => hf.comp (measurable_pi_apply j)
  have hF2 : MemLp (fun y : Fin n → E => ∑ i, f (y i)) 2 ν :=
    MemLp.of_bound hF.aestronglyMeasurable (n * B)
      (Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs]
        calc |∑ i, f (y i)| ≤ ∑ i, |f (y i)| := Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ _i : Fin n, B := Finset.sum_le_sum fun i _ => hB _
          _ = n * B := by simp)
  have hG2 : MemLp (fun y : Fin n → E => ∑ i, f (y i) + c) 2 ν := hF2.add (memLp_const c)
  have hvar := field_linear_variance_real (V := V) hψ hlam hΛ hrow hf hB
  have hm0 : Measurable (fun y : Fin n → E => y 0) := measurable_pi_apply 0
  have hπ : variance f (ν.map (fun x => x 0)) ≤ ∫ y, (f (y 0)) ^ 2 ∂ν := by
    have := variance_le_expectation_sq (μ := ν.map (fun x : Fin n → E => x 0)) (X := f)
      hf.aestronglyMeasurable
    refine this.trans (le_of_eq ?_)
    change ∫ x, f x ^ 2 ∂(ν.map (fun x : Fin n → E => x 0)) = _
    rw [integral_map hm0.aemeasurable (hf.pow_const 2).aestronglyMeasurable]
  have e1 := variance_eq_sub hG2
  have e2 : variance (fun y : Fin n → E => ∑ i, f (y i) + c) ν
      = variance (fun y : Fin n → E => ∑ i, f (y i)) ν := variance_add_const hF.aestronglyMeasurable c
  have hint : ∫ y, (∑ i, f (y i) + c) ^ 2 ∂ν
      = variance (fun y : Fin n → E => ∑ i, f (y i) + c) ν
        + (∫ y, (∑ i, f (y i) + c) ∂ν) ^ 2 := by
    have := e1
    simp only [Pi.pow_apply] at this
    linarith
  have hmean : ∫ y, (∑ i, f (y i) + c) ∂ν = ∫ y, ∑ i, f (y i) ∂ν + c := by
    rw [integral_add (hF2.integrable (by norm_num)) (integrable_const c)]
    simp
  rw [hint, hmean, e2]
  have := mul_le_mul_of_nonneg_left hπ (by positivity : (0 : ℝ) ≤ 2 * n)
  linarith

end GenField

/-! ### Stage 0b: the weak reference with a pole -/

section PoleField

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]

/-- The one-body field of the weak reference with the pole `x` of strength `t lam`
(the pole is a fractional pin). -/
def psiPole (V : WeakPotential μ) (lam t : ℝ) (x : E) : E → ℝ :=
  fun z => V.φ z - t * lam * V.q z x

theorem isField_psiPole (V : WeakPotential μ) {lam t : ℝ} (hlam : 0 ≤ lam) (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (x : E) :
    IsField μ (psiPole V lam t x) V.M (V.M' + lam * V.γ) where
  measurable := by
    unfold psiPole
    exact V.measurable_φ.sub
      (Measurable.const_mul (V.measurable_q.comp (measurable_id.prodMk measurable_const)) _)
  le z := by
    unfold psiPole
    have := mul_nonneg (mul_nonneg ht0 hlam) (V.q_nonneg z x)
    linarith [V.φ_le z]
  integrable := by
    unfold psiPole
    exact V.integrable_φ.sub ((integrable_q_left V x).const_mul _)
  ge := by
    unfold psiPole
    rw [integral_sub V.integrable_φ ((integrable_q_left V x).const_mul _), integral_const_mul]
    have h1 := integral_q_left_le V x
    have h2 := V.neg_le_integral_φ
    have h3 : t * lam * ∫ z, V.q z x ∂μ ≤ lam * V.γ := by
      calc t * lam * ∫ z, V.q z x ∂μ ≤ t * lam * V.γ :=
            mul_le_mul_of_nonneg_left h1 (mul_nonneg ht0 hlam)
        _ ≤ 1 * lam * V.γ := by
            have := V.γ_nonneg
            gcongr
        _ = lam * V.γ := by ring
    linarith

theorem integrable_exp_field {ψ : E → ℝ} {M M₁ lam : ℝ} (V : WeakPotential μ)
    (hψ : IsField μ ψ M M₁) (hlam : 0 ≤ lam) (n : ℕ) :
    Integrable (fun y : Fin n → E => Real.exp (∑ i, ψ (y i) - lam * pairEnergy V y))
      (Measure.pi fun _ : Fin n => μ) := by
  refine Integrable.of_bound (C := Real.exp (n * M)) ?_ ?_
  · exact (Real.measurable_exp.comp ((Finset.measurable_sum _ fun i _ =>
      hψ.measurable.comp (measurable_pi_apply i)).sub
        ((measurable_pairEnergy V).const_mul _))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.2 ?_
    have h1 : ∑ i, ψ (y i) ≤ ∑ _i : Fin n, M := Finset.sum_le_sum fun i _ => hψ.le _
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    have h2 := mul_nonneg hlam (pairEnergy_nonneg V y)
    linarith

end PoleField

/-! ### Stage 1: tilts, Jensen and variance transfer -/

section Tilt

variable {α : Type*} [MeasurableSpace α]

/-- A tilt of a probability measure by a bounded measurable `a ≤ A` has density at most
`e^{A - ∫ a dν}` (Jensen for the normalizer). -/
theorem tilted_le_smul_jensen {ν : Measure α} [IsProbabilityMeasure ν] {a : α → ℝ}
    (ha : Measurable a) {A B : ℝ} (hA : ∀ y, a y ≤ A) (hB : ∀ y, |a y| ≤ B) :
    ν.tilted a ≤ ENNReal.ofReal (Real.exp (A - ∫ y, a y ∂ν)) • ν := by
  have hint : Integrable a ν := integrable_of_abs_le ha B hB
  have hintE : Integrable (fun y => Real.exp (a y)) ν :=
    integrable_of_abs_le (Real.measurable_exp.comp ha) (Real.exp B) fun y => by
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 ((le_abs_self _).trans (hB y))
  have hJ := log_integral_exp_ge hint hintE
  have hpos := integral_exp_pos hintE
  have hlow : Real.exp (∫ y, a y ∂ν) ≤ ∫ y, Real.exp (a y) ∂ν :=
    (Real.le_log_iff_exp_le hpos).1 hJ
  have hdens : ∀ y, Real.exp (a y) / ∫ z, Real.exp (a z) ∂ν ≤ Real.exp (A - ∫ y, a y ∂ν) := by
    intro y
    rw [div_le_iff₀ hpos]
    calc Real.exp (a y) ≤ Real.exp A := Real.exp_le_exp.2 (hA y)
      _ = Real.exp (A - ∫ y, a y ∂ν) * Real.exp (∫ y, a y ∂ν) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ _ := mul_le_mul_of_nonneg_left hlow (Real.exp_pos _).le
  intro S
  show (ν.withDensity fun x => ENNReal.ofReal (Real.exp (a x) / ∫ z, Real.exp (a z) ∂ν)) S ≤ _
  rw [withDensity_apply' _ S, Measure.smul_apply, smul_eq_mul]
  calc ∫⁻ x in S, ENNReal.ofReal (Real.exp (a x) / ∫ z, Real.exp (a z) ∂ν) ∂ν
      ≤ ∫⁻ _x in S, ENNReal.ofReal (Real.exp (A - ∫ y, a y ∂ν)) ∂ν :=
        lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hdens x)
    _ = _ := by rw [setLIntegral_const]

/-- Variance transfer under domination: `P ≤ K ν` gives `Var_P F ≤ K Var_ν F`. -/
theorem evariance_le_of_le_smul {ν P : Measure α} [IsProbabilityMeasure P] {K : ℝ≥0∞}
    (hle : P ≤ K • ν) {F : α → ℝ} (hF : Measurable F) :
    evariance F P ≤ K * evariance F ν := by
  refine (evariance_le_lintegral_sub P hF.aestronglyMeasurable (∫ z, F z ∂ν)).trans ?_
  calc ∫⁻ z, ‖F z - ∫ z, F z ∂ν‖ₑ ^ 2 ∂P
      ≤ ∫⁻ z, ‖F z - ∫ z, F z ∂ν‖ₑ ^ 2 ∂(K • ν) := lintegral_mono' hle le_rfl
    _ = K * evariance F ν := by
        rw [lintegral_smul_measure]
        rfl

end Tilt

/-! ### Stage 2: the exponent of the pole law and the algebraic identity -/

section Exponent

variable {d M : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {q gL : Torus d → ℝ}
  {Ψ : Torus d → EuclideanSpace ℝ (Fin M)} {γ : ℝ}

/-- The exponent of the pole law `A:eq:pole-law` (cavity exponent plus the pole tilt) on `Fin n → 𝕋^d`. -/
def EPole (g : Torus d → ℝ) (μ : Measure (Torus d)) (n : ℕ) (lam β t : ℝ) (x : Torus d)
    (Y : Config d n) : ℝ :=
  (-lam * pairSum g Y + β * ∑ i, convMeasure g μ (Y i)) + -(t * lam) * ∑ i, g (x - Y i)

theorem gL_even (h : RefHyp μ q gL Ψ γ) (z : Torus d) : gL (-z) = gL z := by
  have h1 := h.gL_eq 0 z
  have h2 := h.gL_eq z 0
  rw [zero_sub] at h1
  rw [sub_zero] at h2
  rw [h1, h2, real_inner_comm]

theorem integral_gL (h : RefHyp μ q gL Ψ γ) (z : Torus d) :
    ∫ w, gL (z - w) ∂μ = inner ℝ (Ψ z) (∫ w, Ψ w ∂μ) := by
  simp_rw [h.gL_eq]
  exact integral_inner h.integrable_Ψ (Ψ z)

theorem conv_gTot (h : RefHyp μ q gL Ψ γ) (c : ℝ) (z : Torus d) :
    convMeasure (gTot gL q c) μ z =
      inner ℝ (Ψ z) (∫ w, Ψ w ∂μ) + convMeasure q μ z - c := by
  unfold convMeasure gTot
  have e1 := integral_sub ((h.integrable_gL_section z).add (h.q_int z)) (integrable_const c)
  have e2 := integral_add (h.integrable_gL_section z) (h.q_int z)
  simp only [Pi.add_apply] at e1 e2
  rw [e1, e2, integral_gL h]
  simp

theorem sum_sum_gL (h : RefHyp μ q gL Ψ γ) {n : ℕ} (y : Fin n → Torus d) :
    ∑ a, ∑ b, gL (y a - y b) = ‖∑ i, Ψ (y i)‖ ^ 2 := by
  simp_rw [h.gL_eq]
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_sum]

/-- The constant in `exponent_identity`. -/
def C0 (μ : Measure (Torus d)) (Ψ : Torus d → EuclideanSpace ℝ (Fin M)) (gL : Torus d → ℝ)
    (c β lam t : ℝ) (n : ℕ) (x : Torus d)
    (Xb : EuclideanSpace ℝ (Fin M)) : ℝ :=
  (lam / 2) * c * (n : ℝ) ^ 2 + (lam / 2) * n * (gL 0 - c) - β * n * c + t * lam * n * c
    + n * inner ℝ ((-β) • Xb) (∫ w, Ψ w ∂μ)
    + (lam / 2) * ‖Ψ x - ((n : ℝ) + 1) • (∫ w, Ψ w ∂μ + Xb)‖ ^ 2

/-- **The exponent identity.**  With `S = ∑ Ψ(y_i)`, `m = μ(Ψ)`, `λ(n+1) = β`, `τ = -β Ξ̄`:
`E_pole(y) = E_ref(y) - (λ/2)|S + Ψ x - (n+1)(m + Ξ̄)|² + (1-t) λ ⟨Ψ x, S⟩ + C0`, where
`E_ref(y) = ∑_i (β q*μ(y_i) + τ·Ξ(y_i) - tλ q(y_i - x)) - λ ∑_{i<j} q(y_i - y_j)`. -/
theorem exponent_identity (h : RefHyp μ q gL Ψ γ) (c β lam t : ℝ) (n : ℕ)
    (hlam : β = lam * ((n : ℝ) + 1)) (x : Torus d) (Xb : EuclideanSpace ℝ (Fin M))
    (y : Fin n → Torus d) :
    EPole (gTot gL q c) μ n lam β t x y =
      (∑ i, (β * convMeasure q μ (y i) + inner ℝ ((-β) • Xb) (Xi μ Ψ (y i))
          - t * lam * q (y i - x)) - lam * pairSum q y)
      + (-(lam / 2) * ‖∑ i, Ψ (y i) + Ψ x - ((n : ℝ) + 1) • (∫ w, Ψ w ∂μ + Xb)‖ ^ 2)
      + (1 - t) * lam * inner ℝ (Ψ x) (∑ i, Ψ (y i))
      + C0 μ Ψ gL c β lam t n x Xb := by
  set S : EuclideanSpace ℝ (Fin M) := ∑ i, Ψ (y i) with hS
  set m : EuclideanSpace ℝ (Fin M) := ∫ w, Ψ w ∂μ with hm
  have hq_even : ∀ z, q (-z) = q z := h.q_even
  have hgeven : ∀ z, gTot gL q c (-z) = gTot gL q c z := fun z => by
    simp only [gTot, gL_even h z, hq_even z]
  -- pair sums
  have ha : pairSum (gTot gL q c) y = (1 / 2) * (‖S‖ ^ 2 + ∑ a, ∑ b, q (y a - y b)
      - c * (n : ℝ) ^ 2 - n * (gL 0 + q 0 - c)) := by
    rw [PoleCavityAux.pairSum_eq hgeven]
    have : ∑ a, ∑ b, gTot gL q c (y a - y b) =
        ‖S‖ ^ 2 + ∑ a, ∑ b, q (y a - y b) - c * (n : ℝ) ^ 2 := by
      simp only [gTot, Finset.sum_sub_distrib, Finset.sum_add_distrib]
      rw [sum_sum_gL h y]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
    rw [this]
    simp only [gTot]
  have hb : pairSum q y = (1 / 2) * (∑ a, ∑ b, q (y a - y b) - n * q 0) :=
    PoleCavityAux.pairSum_eq hq_even y
  have hc : ∑ i, convMeasure (gTot gL q c) μ (y i) =
      inner ℝ S m + ∑ i, convMeasure q μ (y i) - n * c := by
    simp_rw [conv_gTot h c]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hS, sum_inner]
    simp
    rfl
  have hd : ∑ i, gTot gL q c (x - y i) = inner ℝ (Ψ x) S + ∑ i, q (y i - x) - n * c := by
    have : ∀ i, gTot gL q c (x - y i) = inner ℝ (Ψ x) (Ψ (y i)) + q (y i - x) - c := fun i => by
      simp only [gTot, h.gL_eq]
      rw [← hq_even (y i - x), neg_sub]
    simp_rw [this]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, hS, inner_sum]
    simp
  have he : ∑ i, inner ℝ ((-β) • Xb) (Xi μ Ψ (y i)) =
      inner ℝ ((-β) • Xb) S - n * inner ℝ ((-β) • Xb) m := by
    simp only [Xi]
    simp_rw [inner_sub_right]
    rw [Finset.sum_sub_distrib, hS, inner_sum]
    simp
    exact Or.inl rfl
  have hnorm : ‖S + Ψ x - ((n : ℝ) + 1) • (m + Xb)‖ ^ 2 =
      ‖S‖ ^ 2 + 2 * (inner ℝ S (Ψ x) - ((n : ℝ) + 1) * (inner ℝ S m + inner ℝ S Xb))
        + ‖Ψ x - ((n : ℝ) + 1) • (m + Xb)‖ ^ 2 := by
    have : S + Ψ x - ((n : ℝ) + 1) • (m + Xb) = S + (Ψ x - ((n : ℝ) + 1) • (m + Xb)) := by abel
    rw [this, norm_add_sq_real]
    rw [inner_sub_right, inner_smul_right, inner_add_right]
  have hτ : inner ℝ ((-β) • Xb) S = -β * inner ℝ S Xb := by
    rw [inner_smul_left, real_inner_comm]
    simp
  have hsum : ∑ i, (β * convMeasure q μ (y i) + inner ℝ ((-β) • Xb) (Xi μ Ψ (y i))
          - t * lam * q (y i - x)) = β * ∑ i, convMeasure q μ (y i)
        + (inner ℝ ((-β) • Xb) S - n * inner ℝ ((-β) • Xb) m) - t * lam * ∑ i, q (y i - x) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, he, ← Finset.mul_sum, ← Finset.mul_sum]
  unfold EPole C0
  rw [hsum, ha, hb, hc, hd, hnorm, hτ, real_inner_comm S (Ψ x)]
  subst hlam
  ring

end Exponent

/-! ### Stage 3: the pole law as a bounded tilt of the weak reference with the pole -/

section Core

variable {d M : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {q gL : Torus d → ℝ}
  {Ψ : Torus d → EuclideanSpace ℝ (Fin M)} {γ : ℝ} (h : RefHyp μ q gL Ψ γ) {β : ℝ} (hβ : 0 < β)

/-- The weak potential of the calibrated reference `R_{n+1}`. -/
abbrev Vp (n : ℕ) (ht : ∀ x, |inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ 1) : WeakPotential μ :=
  weakPot h hβ.le (tN q μ Ψ β (n + 1)) ht

/-- The coupling `λ = β / (n+1)`. -/
def lamN (β : ℝ) (n : ℕ) : ℝ := β / ((n + 1 : ℕ) : ℝ)

/-- The weak reference with the pole: the field `φ - tλ q(· - x)`. -/
def Rpole (n : ℕ) (ht : ∀ x, |inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ 1) (x : Torus d) (t : ℝ) :
    Measure (Config d n) :=
  fieldLaw (Vp h hβ n ht) (psiPole (Vp h hβ n ht) (lamN β n) t x) (lamN β n) n

/-- The log-density of the pole law with respect to the weak reference with the pole,
`-(λ/2)|S + Ψ x - (n+1)(m + Ξ̄)|² + (1-t) λ ⟨Ψ x, S⟩`. -/
def aPole (μ : Measure (Torus d)) (Ψ : Torus d → EuclideanSpace ℝ (Fin M)) (β : ℝ) (n : ℕ)
    (x : Torus d) (t : ℝ) (Xb : EuclideanSpace ℝ (Fin M)) (y : Config d n) : ℝ :=
  -(lamN β n / 2) * ‖∑ i, Ψ (y i) + Ψ x - ((n : ℝ) + 1) • (∫ w, Ψ w ∂μ + Xb)‖ ^ 2
    + (1 - t) * lamN β n * inner ℝ (Ψ x) (∑ i, Ψ (y i))

theorem lamN_mul (n : ℕ) : β = lamN β n * ((n : ℝ) + 1) := by
  unfold lamN
  have : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  rw [this]
  have : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp

theorem pairEnergy_eq_pairSum {V : WeakPotential μ} (hV : ∀ a b, V.q a b = q (a - b)) {n : ℕ}
    (y : Config d n) : pairEnergy V y = pairSum q y := by
  rw [pairEnergy_eq_sum_lt]
  unfold pairSum
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr ?_ fun j _ => hV _ _
  ext j
  simp

theorem pole_tilted_eq (c : ℝ) (n : ℕ)
    (ht : ∀ x, |inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ 1) (x : Torus d) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (Measure.pi fun _ : Fin n => μ).tilted (EPole (gTot gL q c) μ n (lamN β n) β t x)
      = (Rpole h hβ n ht x t).tilted (aPole μ Ψ β n x t (Xibar q μ Ψ β (n + 1))) := by
  have hlam0 : 0 ≤ lamN β n := div_nonneg hβ.le (Nat.cast_nonneg _)
  have hψ := isField_psiPole (Vp h hβ n ht) hlam0 ht0 ht1 x
  have hint := integrable_exp_field (Vp h hβ n ht) hψ hlam0 n
  have hq : ∀ a b, (Vp h hβ n ht).q a b = q (a - b) := fun a b => rfl
  have htN : tN q μ Ψ β (n + 1) = (-β) • Xibar q μ Ψ β (n + 1) := h.tN_eq hβ (Nat.succ_pos n)
  have hfun : EPole (gTot gL q c) μ n (lamN β n) β t x =
      (fun y : Config d n => ∑ i, psiPole (Vp h hβ n ht) (lamN β n) t x (y i)
          - lamN β n * pairEnergy (Vp h hβ n ht) y) +
      (fun y => aPole μ Ψ β n x t (Xibar q μ Ψ β (n + 1)) y
          + C0 μ Ψ gL c β (lamN β n) t n x (Xibar q μ Ψ β (n + 1))) := by
    funext y
    rw [exponent_identity h c β (lamN β n) t n (lamN_mul n) x (Xibar q μ Ψ β (n + 1)) y]
    simp only [Pi.add_apply]
    rw [pairEnergy_eq_pairSum hq y]
    have : ∑ i, psiPole (Vp h hβ n ht) (lamN β n) t x (y i) =
        ∑ i, (β * convMeasure q μ (y i) + inner ℝ ((-β) • Xibar q μ Ψ β (n + 1)) (Xi μ Ψ (y i))
          - t * lamN β n * q (y i - x)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [psiPole, Vp, weakPot]
      rw [htN]
    rw [this]
    unfold aPole
    ring
  rw [hfun, ← tilted_tilted hint, tilted_add_const]
  unfold Rpole
  rw [fieldLaw_eq_tilted hint]

theorem isProb_Rpole (n : ℕ) (ht : ∀ x, |inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ 1)
    (x : Torus d) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsProbabilityMeasure (Rpole h hβ n ht x t) := by
  have hlam0 : 0 ≤ lamN β n := div_nonneg hβ.le (Nat.cast_nonneg _)
  exact (fieldSpec (V := Vp h hβ n ht) (isField_psiPole (Vp h hβ n ht) hlam0 ht0 ht1 x)
    hlam0 n).isProb

include h in
theorem measurable_aPole (n : ℕ) (x : Torus d) (t : ℝ) (Xb : EuclideanSpace ℝ (Fin M)) :
    Measurable (aPole μ Ψ β n x t Xb) := by
  have hS : Measurable fun y : Config d n => ∑ i, Ψ (y i) :=
    Finset.measurable_sum _ fun i _ => h.Ψ_meas.comp (measurable_pi_apply i)
  unfold aPole
  refine ((((hS.add_const _).sub_const _).norm.pow_const 2).const_mul _).add ?_
  exact (measurable_const.inner hS).const_mul _

include h in
theorem norm_sum_Ψ_le (n : ℕ) (y : Config d n) :
    ‖∑ i, Ψ (y i)‖ ≤ n * Real.sqrt (gL 0) := by
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i, ‖Ψ (y i)‖ ≤ ∑ _i : Fin n, Real.sqrt (gL 0) :=
        Finset.sum_le_sum fun i _ => h.norm_Ψ_le _
    _ = _ := by simp

include h hβ in
theorem abs_pert_le (n : ℕ) (x : Torus d) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (y : Config d n) :
    |(1 - t) * lamN β n * inner ℝ (Ψ x) (∑ i, Ψ (y i))| ≤ lamN β n * n * gL 0 := by
  have hlam0 : 0 ≤ lamN β n := div_nonneg hβ.le (Nat.cast_nonneg _)
  have hr : Real.sqrt (gL 0) * Real.sqrt (gL 0) = gL 0 := Real.mul_self_sqrt h.gL_zero_nonneg
  have h1 : |inner ℝ (Ψ x) (∑ i, Ψ (y i))| ≤ n * gL 0 := by
    calc |inner ℝ (Ψ x) (∑ i, Ψ (y i))| ≤ ‖Ψ x‖ * ‖∑ i, Ψ (y i)‖ := abs_real_inner_le_norm _ _
      _ ≤ Real.sqrt (gL 0) * (n * Real.sqrt (gL 0)) :=
          mul_le_mul (h.norm_Ψ_le x) (norm_sum_Ψ_le h n y) (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = n * (Real.sqrt (gL 0) * Real.sqrt (gL 0)) := by ring
      _ = n * gL 0 := by rw [hr]
  rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : 0 ≤ 1 - t), abs_of_nonneg hlam0]
  have hg0 := h.gL_zero_nonneg
  calc (1 - t) * lamN β n * |inner ℝ (Ψ x) (∑ i, Ψ (y i))| ≤ 1 * lamN β n * (n * gL 0) := by
        gcongr
        linarith
    _ = _ := by ring

end Core

section Core2

variable {d M : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {q gL : Torus d → ℝ}
  {Ψ : Torus d → EuclideanSpace ℝ (Fin M)} {γ : ℝ} (h : RefHyp μ q gL Ψ γ) {β : ℝ} (hβ : 0 < β)

include h hβ in
/-- **Bounded density of the pole law with respect to the weak reference with the pole**:
`dP/dR ≤ exp(2β g_L(0) + (λ/2) E_R|S + Ψ x - (n+1)(m + Ξ̄)|²)`. -/
theorem tilted_aPole_le (n : ℕ) (ht : ∀ x, |inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ 1)
    (x : Torus d) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {Esq : ℝ}
    (hE : ∫ y, ‖∑ i, Ψ (y i) + Ψ x - ((n : ℝ) + 1) • (∫ w, Ψ w ∂μ + Xibar q μ Ψ β (n + 1))‖ ^ 2
        ∂(Rpole h hβ n ht x t) ≤ Esq) :
    (Rpole h hβ n ht x t).tilted (aPole μ Ψ β n x t (Xibar q μ Ψ β (n + 1))) ≤
      ENNReal.ofReal (Real.exp (2 * β * gL 0 + (lamN β n / 2) * Esq)) • Rpole h hβ n ht x t := by
  have := isProb_Rpole h hβ n ht x ht0 ht1
  set Pr := Rpole h hβ n ht x t with hPr
  set Xb := Xibar q μ Ψ β (n + 1) with hXb
  have hlam0 : 0 ≤ lamN β n := div_nonneg hβ.le (Nat.cast_nonneg _)
  have hg0 := h.gL_zero_nonneg
  have hlamn : lamN β n * n ≤ β := by
    have := lamN_mul (β := β) n
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  set Wv : Config d n → EuclideanSpace ℝ (Fin M) := fun y =>
    ∑ i, Ψ (y i) + Ψ x - ((n : ℝ) + 1) • (∫ w, Ψ w ∂μ + Xb) with hWv
  have hWm : Measurable fun y : Config d n => ‖Wv y‖ ^ 2 := by
    have hS : Measurable fun y : Config d n => ∑ i, Ψ (y i) :=
      Finset.measurable_sum _ fun i _ => h.Ψ_meas.comp (measurable_pi_apply i)
    exact ((hS.add_const _).sub_const _).norm.pow_const 2
  set Cn : ℝ := n * Real.sqrt (gL 0) + Real.sqrt (gL 0)
    + ((n : ℝ) + 1) * (Real.sqrt (gL 0) + ‖Xb‖) with hCn
  have hWb : ∀ y, ‖Wv y‖ ≤ Cn := by
    intro y
    simp only [hWv]
    calc ‖∑ i, Ψ (y i) + Ψ x - ((n : ℝ) + 1) • (∫ w, Ψ w ∂μ + Xb)‖
        ≤ ‖∑ i, Ψ (y i) + Ψ x‖ + ‖((n : ℝ) + 1) • (∫ w, Ψ w ∂μ + Xb)‖ := norm_sub_le _ _
      _ ≤ (‖∑ i, Ψ (y i)‖ + ‖Ψ x‖) + ((n : ℝ) + 1) * (‖∫ w, Ψ w ∂μ‖ + ‖Xb‖) := by
          refine add_le_add (norm_add_le _ _) ?_
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
          exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
      _ ≤ _ := by
          have h1 := norm_sum_Ψ_le h n y
          have h2 := h.norm_Ψ_le x
          have h3 := h.norm_int_Ψ_le
          have : ((n : ℝ) + 1) * (‖∫ w, Ψ w ∂μ‖ + ‖Xb‖) ≤ ((n : ℝ) + 1) * (Real.sqrt (gL 0) + ‖Xb‖) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          linarith
  have hnorm0 : ∀ y, 0 ≤ ‖Wv y‖ := fun y => norm_nonneg _
  -- the two pieces of `a`
  set a1 : Config d n → ℝ := fun y => -(lamN β n / 2) * ‖Wv y‖ ^ 2 with ha1
  set a2 : Config d n → ℝ := fun y => (1 - t) * lamN β n * inner ℝ (Ψ x) (∑ i, Ψ (y i)) with ha2
  have ha : aPole μ Ψ β n x t Xb = fun y => a1 y + a2 y := rfl
  have ha1m : Measurable a1 := hWm.const_mul _
  have ha2m : Measurable a2 := by
    have hS : Measurable fun y : Config d n => ∑ i, Ψ (y i) :=
      Finset.measurable_sum _ fun i _ => h.Ψ_meas.comp (measurable_pi_apply i)
    exact (measurable_const.inner hS).const_mul _
  have ha1b : ∀ y, |a1 y| ≤ (lamN β n / 2) * Cn ^ 2 := by
    intro y
    simp only [ha1]
    rw [abs_mul, abs_neg, abs_of_nonneg (by positivity : 0 ≤ lamN β n / 2), abs_of_nonneg (sq_nonneg _)]
    gcongr
    exact hWb y
  have ha2b : ∀ y, |a2 y| ≤ lamN β n * n * gL 0 := fun y => abs_pert_le h hβ n x ht0 ht1 y
  have ha1i : Integrable a1 Pr := integrable_of_abs_le ha1m _ ha1b
  have ha2i : Integrable a2 Pr := integrable_of_abs_le ha2m _ ha2b
  have hWi : Integrable (fun y : Config d n => ‖Wv y‖ ^ 2) Pr := by
    refine integrable_of_abs_le hWm (Cn ^ 2) fun y => ?_
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (hnorm0 y) (hWb y) 2
  have hA : ∀ y, aPole μ Ψ β n x t Xb y ≤ β * gL 0 := by
    intro y
    show a1 y + a2 y ≤ _
    have h1 : a1 y ≤ 0 := by
      simp only [ha1]
      have : 0 ≤ (lamN β n / 2) * ‖Wv y‖ ^ 2 := by positivity
      linarith
    have h2 := (le_abs_self _).trans (ha2b y)
    have h3 : lamN β n * n * gL 0 ≤ β * gL 0 := mul_le_mul_of_nonneg_right hlamn hg0
    linarith
  have hB : ∀ y, |aPole μ Ψ β n x t Xb y| ≤ (lamN β n / 2) * Cn ^ 2 + lamN β n * n * gL 0 := by
    intro y
    show |a1 y + a2 y| ≤ _
    exact (abs_add_le _ _).trans (add_le_add (ha1b y) (ha2b y))
  have hJ := tilted_le_smul_jensen (ν := Pr) (measurable_aPole (β := β) h n x t Xb) hA hB
  refine hJ.trans ?_
  -- compare the constants
  have hint1 : ∫ y, a1 y ∂Pr = -(lamN β n / 2) * ∫ y, ‖Wv y‖ ^ 2 ∂Pr := by
    simp only [ha1]
    rw [integral_const_mul]
  have hint2 : -(lamN β n * n * gL 0) ≤ ∫ y, a2 y ∂Pr := by
    have : ∫ y, -(lamN β n * n * gL 0) ∂Pr ≤ ∫ y, a2 y ∂Pr :=
      integral_mono (integrable_const _) ha2i fun y => (abs_le.1 (ha2b y)).1
    simpa using this
  have hsplit : ∫ y, aPole μ Ψ β n x t Xb y ∂Pr = ∫ y, a1 y ∂Pr + ∫ y, a2 y ∂Pr := by
    rw [ha]
    exact integral_add ha1i ha2i
  have hE' : -(lamN β n / 2) * ∫ y, ‖Wv y‖ ^ 2 ∂Pr ≥ -(lamN β n / 2) * Esq := by
    have : ∫ y, ‖Wv y‖ ^ 2 ∂Pr ≤ Esq := hE
    nlinarith
  have hlow : -(lamN β n / 2) * Esq - β * gL 0 ≤ ∫ y, aPole μ Ψ β n x t Xb y ∂Pr := by
    rw [hsplit, hint1]
    have h3 : lamN β n * n * gL 0 ≤ β * gL 0 := mul_le_mul_of_nonneg_right hlamn hg0
    linarith
  intro S
  rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
  exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 (by linarith))) _

end Core2

section GenFieldVec

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]
  {V : WeakPotential μ} {ψ : E → ℝ} {M₀ M₁ lam : ℝ} {M : ℕ}

/-- Vector form of the second-moment bound: for a bounded measurable `Ψ : E → ℝ^M` and a constant
vector `c`, `E|∑ Ψ(y_i) + c|² ≤ 2 n E|Ψ(y_0)|² + |E(∑ Ψ(y_i) + c)|²`. -/
theorem field_second_moment_vec {n : ℕ} [NeZero n] (hψ : IsField μ ψ M₀ M₁) (hlam : 0 ≤ lam)
    {Λ : ℝ} (hΛ : M₁ + lam * n * V.γ ≤ Λ)
    (hrow : ∀ i : Fin n, ∑ _j ∈ Finset.univ.erase i, 4 * Real.exp (M₀ + Λ) * lam * V.γ ≤ 1 / 2)
    {Ψ : E → EuclideanSpace ℝ (Fin M)} (hΨm : Measurable Ψ) {r : ℝ} (hr : ∀ z, ‖Ψ z‖ ≤ r)
    (cv : EuclideanSpace ℝ (Fin M)) :
    ∫ y, ‖∑ i, Ψ (y i) + cv‖ ^ 2 ∂(fieldLaw V ψ lam n)
      ≤ 2 * n * ∫ y, ‖Ψ (y 0)‖ ^ 2 ∂(fieldLaw V ψ lam n)
        + ‖∫ y, (∑ i, Ψ (y i) + cv) ∂(fieldLaw V ψ lam n)‖ ^ 2 := by
  have hPr : IsProbabilityMeasure (fieldLaw V ψ lam n) := (fieldSpec (V := V) hψ hlam n).isProb
  set ν := fieldLaw V ψ lam n with hν
  have hfm : ∀ m : Fin M, Measurable fun z => (Ψ z).ofLp m := fun m =>
    (EuclideanSpace.proj (𝕜 := ℝ) m).continuous.measurable.comp hΨm
  have hfb : ∀ (m : Fin M) z, |(Ψ z).ofLp m| ≤ r := fun m z => by
    have := (PiLp.norm_apply_le (Ψ z) m).trans (hr z)
    simpa using this
  have hvm : Measurable fun y : Fin n → E => ∑ i, Ψ (y i) + cv :=
    (Finset.measurable_sum _ fun i _ => hΨm.comp (measurable_pi_apply i)).add_const _
  have hvb : ∀ y : Fin n → E, ‖∑ i, Ψ (y i) + cv‖ ≤ n * r + ‖cv‖ := fun y => by
    refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i, ‖Ψ (y i)‖ ≤ ∑ _i : Fin n, r := Finset.sum_le_sum fun i _ => hr _
      _ = _ := by simp
  have hvint : Integrable (fun y : Fin n → E => ∑ i, Ψ (y i) + cv) ν :=
    Integrable.of_bound hvm.aestronglyMeasurable _ (Filter.Eventually.of_forall hvb)
  have hmeanm : ∀ m : Fin M, (∫ y, (∑ i, Ψ (y i) + cv) ∂ν).ofLp m
      = ∫ y, ((∑ i, Ψ (y i) + cv).ofLp m) ∂ν := fun m => by
    have := ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj (𝕜 := ℝ) m) hvint
    simpa using this.symm
  have hcoord : ∀ (y : Fin n → E) (m : Fin M), (∑ i, Ψ (y i) + cv).ofLp m
      = ∑ i, (Ψ (y i)).ofLp m + cv.ofLp m := fun y m => by simp
  have hcm : ∀ m : Fin M, Measurable fun y : Fin n → E => (∑ i, Ψ (y i) + cv).ofLp m := fun m =>
    (EuclideanSpace.proj (𝕜 := ℝ) m).continuous.measurable.comp hvm
  have hcb : ∀ (m : Fin M) (y : Fin n → E), |(∑ i, Ψ (y i) + cv).ofLp m| ≤ n * r + ‖cv‖ :=
    fun m y => by
      have := (PiLp.norm_apply_le (∑ i, Ψ (y i) + cv) m).trans (hvb y)
      simpa using this
  have hper : ∀ m : Fin M, ∫ y, ((∑ i, Ψ (y i) + cv).ofLp m) ^ 2 ∂ν
      ≤ 2 * n * ∫ y, ((Ψ (y 0)).ofLp m) ^ 2 ∂ν
        + (∫ y, ((∑ i, Ψ (y i) + cv).ofLp m) ∂ν) ^ 2 := by
    intro m
    have h1 := field_second_moment_le (V := V) hψ hlam hΛ hrow (hfm m) (hfb m) (cv.ofLp m)
    have e1 : ∀ y : Fin n → E, (∑ i, Ψ (y i) + cv).ofLp m ^ 2
        = (∑ i, (Ψ (y i)).ofLp m + cv.ofLp m) ^ 2 := fun y => by rw [hcoord]
    simp_rw [e1, hcoord]
    have hsum : Integrable (fun y : Fin n → E => ∑ i, (Ψ (y i)).ofLp m) ν :=
      integrable_finsetSum _ fun i _ => Integrable.of_bound
        ((hfm m).comp (measurable_pi_apply i)).aestronglyMeasurable r
        (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs]; exact hfb m _)
    have e2 : ∫ y, (∑ i, (Ψ (y i)).ofLp m + cv.ofLp m) ∂ν
        = ∫ y, ∑ i, (Ψ (y i)).ofLp m ∂ν + cv.ofLp m := by
      rw [integral_add hsum (integrable_const _)]
      simp
    rw [e2]
    exact h1
  have hnorm : ∀ y : Fin n → E, ‖∑ i, Ψ (y i) + cv‖ ^ 2
      = ∑ m, ((∑ i, Ψ (y i) + cv).ofLp m) ^ 2 := fun y => by
    rw [EuclideanSpace.norm_sq_eq]
    simp
  have hnorm0 : ∀ y : Fin n → E, ‖Ψ (y 0)‖ ^ 2 = ∑ m, ((Ψ (y 0)).ofLp m) ^ 2 := fun y => by
    rw [EuclideanSpace.norm_sq_eq]
    simp
  have hint1 : ∀ m : Fin M, Integrable (fun y : Fin n → E => ((∑ i, Ψ (y i) + cv).ofLp m) ^ 2) ν :=
    fun m => integrable_of_abs_le ((hcm m).pow_const 2) ((n * r + ‖cv‖) ^ 2) fun y => by
      rw [abs_of_nonneg (sq_nonneg _)]
      have := hcb m y
      exact sq_le_sq' (by linarith [abs_le.1 this]) (by linarith [abs_le.1 this])
  have hint0 : ∀ m : Fin M, Integrable (fun y : Fin n → E => ((Ψ (y 0)).ofLp m) ^ 2) ν :=
    fun m => integrable_of_abs_le (((hfm m).comp (measurable_pi_apply 0)).pow_const 2) (r ^ 2) fun y => by
      rw [abs_of_nonneg (sq_nonneg _)]
      have := hfb m (y 0)
      exact sq_le_sq' (by linarith [abs_le.1 this]) (by linarith [abs_le.1 this])
  simp_rw [hnorm, hnorm0]
  rw [integral_finsetSum _ fun m _ => hint1 m, integral_finsetSum _ fun m _ => hint0 m]
  have h3 : ∑ m : Fin M, ∫ y, ((∑ i, Ψ (y i) + cv).ofLp m) ^ 2 ∂ν
      ≤ ∑ m : Fin M, (2 * n * ∫ y, ((Ψ (y 0)).ofLp m) ^ 2 ∂ν
        + (∫ y, ((∑ i, Ψ (y i) + cv).ofLp m) ∂ν) ^ 2) := Finset.sum_le_sum fun m _ => hper m
  refine h3.trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, EuclideanSpace.norm_sq_eq]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hmeanm m]
  simp

end GenFieldVec

section Marginals

variable {d M : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {q gL : Torus d → ℝ}
  {Ψ : Torus d → EuclideanSpace ℝ (Fin M)} {γ : ℝ} (h : RefHyp μ q gL Ψ γ) {β : ℝ} (hβ : 0 < β)

include h hβ in
theorem RN_eq_pinned (n : ℕ) (ht : ∀ x, |inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ 1) :
    RN q μ Ψ β (n + 1) = pinnedLaw (Vp h hβ n ht) (lamN β n) (n + 1) (fun e : Empty => e.elim) := by
  have hRN := h.RN_eq_fieldLaw (N := n + 1) hβ.le ht
  rw [hRN]
  unfold pinnedLaw
  have : pinField (Vp h hβ n ht) (lamN β n) (fun e : Empty => e.elim) = (Vp h hβ n ht).φ := by
    funext z; simp [pinField]
  rw [this]
  rfl

end Marginals

section PinPole

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} [IsProbabilityMeasure μ]

theorem pinField_pinsWith_empty (V : WeakPotential μ) (lam : ℝ) (x z : E) :
    pinField V lam (pinsWith (fun e : Empty => e.elim) x) z = V.φ z - lam * V.q z x := by
  rw [pinField_pinsWith]
  simp [pinField]

/-- The fractional pin: the pinned ensemble with pin `x` (strength `λ`) and the ensemble with the
pole `x` of strength `t λ` have marginals within `κ/N` in total variation. -/
theorem pin_pole_event (V : WeakPotential μ) {β : ℝ} (hβ : 0 ≤ β) {N n : ℕ} (hN0 : 0 < N)
    (hN : n + 1 ≤ N) (hκ : weakKappa V β ≤ 1 / 2) (x : E) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (j : Fin n) {A : Set E} (hA : MeasurableSet A) :
    |((pinnedLaw V (β / N) n (pinsWith (fun e : Empty => e.elim) x)).map (fun y => y j)).real A
      - ((fieldLaw V (psiPole V (β / N) t x) (β / N) n).map (fun y => y j)).real A|
        ≤ weakKappa V β / N := by
  have hlam : 0 ≤ β / N := div_nonneg hβ (Nat.cast_nonneg N)
  have hψ₁ := isField_pinField V hlam (pinsWith (fun e : Empty => e.elim) x)
  have hψ₂ := isField_psiPole V hlam ht0 ht1 x
  have hnN : n ≤ N := le_trans (Nat.le_add_right n _) hN
  have hcard : n + Fintype.card (Option Empty) ≤ N := by simpa [Fintype.card_option] using hN
  have hD : ∫ z, |pinField V (β / N) (pinsWith (fun e : Empty => e.elim) x) z
      - psiPole V (β / N) t x z| ∂μ ≤ β / N * V.γ := by
    have hpt : ∀ z, |pinField V (β / N) (pinsWith (fun e : Empty => e.elim) x) z
        - psiPole V (β / N) t x z| = (1 - t) * (β / N) * V.q z x := by
      intro z
      rw [pinField_pinsWith_empty]
      unfold psiPole
      have : V.φ z - β / N * V.q z x - (V.φ z - t * (β / N) * V.q z x)
          = -((1 - t) * (β / N) * V.q z x) := by ring
      rw [this, abs_neg, abs_of_nonneg (mul_nonneg (mul_nonneg (by linarith) hlam) (V.q_nonneg z x))]
    simp_rw [hpt]
    rw [integral_const_mul]
    have h1 := integral_q_left_le V x
    calc (1 - t) * (β / N) * ∫ z, V.q z x ∂μ ≤ (1 - t) * (β / N) * V.γ :=
          mul_le_mul_of_nonneg_left h1 (mul_nonneg (by linarith) hlam)
      _ ≤ 1 * (β / N) * V.γ := by
          have := V.γ_nonneg
          gcongr
          linarith
      _ = _ := by ring
  have h := rvh_field_event (V := V) j hψ₁ hψ₂ hlam (Λ := V.M' + β * V.γ)
    (weak_Lambda_le V hβ hN0 hcard) hD (r := weakKappa V β) (fun i => by
      rw [four_exp_eq]
      exact row_sum_le_of_uniform hN0 hnN (weakKappa_nonneg V hβ) i) (by linarith) hA
  refine h.trans ?_
  have e : V.M + (V.M' + β * V.γ) = V.M + V.M' + β * V.γ := by ring
  rw [e]
  have h1 : (1 : ℝ) / 2 ≤ 1 - weakKappa V β := by linarith
  have h2 : 0 ≤ 2 * Real.exp (V.M + V.M' + β * V.γ) * (β / N * V.γ) := by
    have := V.γ_nonneg; positivity
  rw [div_le_iff₀ (by linarith)]
  have h4 := four_exp_eq V β N
  rw [e] at h4
  calc 2 * Real.exp (V.M + V.M' + β * V.γ) * (β / N * V.γ)
      = (4 * Real.exp (V.M + V.M' + β * V.γ) * (β / N) * V.γ) * (1 / 2) := by ring
    _ = weakKappa V β / N * (1 / 2) := by rw [h4]
    _ ≤ weakKappa V β / N * (1 - weakKappa V β) :=
        mul_le_mul_of_nonneg_left h1 (div_nonneg (weakKappa_nonneg V hβ) (Nat.cast_nonneg N))

end PinPole

section Marginals2

open HRS.External.Entropy

variable {d M : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {q gL : Torus d → ℝ}
  {Ψ : Torus d → EuclideanSpace ℝ (Fin M)} {γ : ℝ} (h : RefHyp μ q gL Ψ γ) {β : ℝ} (hβ : 0 < β)

theorem weakKappa_Vp_le (n : ℕ) (ht : ∀ x, |inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ 1)
    (hκ : KappaSmall β γ) : weakKappa (Vp h hβ n ht) β ≤ 1 / 2 := by
  have e : weakKappa (Vp h hβ n ht) β = 4 * Real.exp ((β * γ + 1) + 0 + β * γ) * (β * γ) := rfl
  rw [e]
  have : (β * γ + 1) + 0 + β * γ = 2 * (β * γ) + 1 := by ring
  rw [this]
  exact hκ

include h hβ in
/-- The marginals of the weak reference with the pole are within `3κ/(n+1)` (total variation) of
the marginals of the calibrated reference `R_{n+1}`. -/
theorem marginal_tv_le (n : ℕ) (ht : ∀ x, |inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ 1)
    (hκ : KappaSmall β γ) (x : Torus d) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (i : Fin n) :
    tvDist ((Rpole h hβ n ht x t).map (fun y => y i))
      ((RN q μ Ψ β (n + 1)).map (fun X => X ((0 : Fin (n + 1)).succAbove i)))
      ≤ 3 * weakKappa (Vp h hβ n ht) β / ((n : ℝ) + 1) := by
  have hκ' := weakKappa_Vp_le h hβ n ht hκ
  have : Nonempty {A : Set (Torus d) // MeasurableSet A} := ⟨⟨∅, MeasurableSet.empty⟩⟩
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have hlam : lamN β n = β / ((n + 1 : ℕ) : ℝ) := rfl
  unfold tvDist
  refine ciSup_le fun A => ?_
  have h1 := pin_pole_event (Vp h hβ n ht) hβ.le (N := n + 1) (n := n) (Nat.succ_pos n) le_rfl hκ'
    x ht0 ht1 i A.2
  have h2 := rvh_pin_comparison (Vp h hβ n ht) hβ.le (N := n + 1) (n := n) (Nat.succ_pos n)
    (by simp) (fun e : Empty => e.elim) hκ' 0 i x A.2
  rw [RN_eq_pinned h hβ n ht]
  unfold Rpole
  rw [hlam]
  have h3 := abs_sub_le (((fieldLaw (Vp h hβ n ht) (psiPole (Vp h hβ n ht) (β / ((n + 1 : ℕ) : ℝ)) t x)
      (β / ((n + 1 : ℕ) : ℝ)) n).map (fun y => y i)).real A.1)
    (((pinnedLaw (Vp h hβ n ht) (β / ((n + 1 : ℕ) : ℝ)) n
      (pinsWith (fun e : Empty => e.elim) x)).map (fun y => y i)).real A.1)
    (((pinnedLaw (Vp h hβ n ht) (β / ((n + 1 : ℕ) : ℝ)) (n + 1)
      (fun e : Empty => e.elim)).map (fun y => y ((0 : Fin (n + 1)).succAbove i))).real A.1)
  rw [abs_sub_comm (((fieldLaw (Vp h hβ n ht) (psiPole (Vp h hβ n ht) (β / ((n + 1 : ℕ) : ℝ)) t x)
      (β / ((n + 1 : ℕ) : ℝ)) n).map (fun y => y i)).real A.1)
    (((pinnedLaw (Vp h hβ n ht) (β / ((n + 1 : ℕ) : ℝ)) n
      (pinsWith (fun e : Empty => e.elim) x)).map (fun y => y i)).real A.1)] at h3
  have hk : 3 * weakKappa (Vp h hβ n ht) β / ((n : ℝ) + 1)
      = weakKappa (Vp h hβ n ht) β / ((n + 1 : ℕ) : ℝ)
        + 2 * weakKappa (Vp h hβ n ht) β / ((n + 1 : ℕ) : ℝ) := by
    rw [hcast]; ring
  rw [hk]
  linarith

end Marginals2

section Mean

open HRS.External.Entropy

variable {d M : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {q gL : Torus d → ℝ}
  {Ψ : Torus d → EuclideanSpace ℝ (Fin M)} {γ : ℝ} (h : RefHyp μ q gL Ψ γ) {β : ℝ} (hβ : 0 < β)

include h hβ in
theorem Xibar_mul (n : ℕ) :
    ((n : ℝ) + 1) • Xibar q μ Ψ β (n + 1)
      = ∑ j : Fin (n + 1), ∫ X, Xi μ Ψ (X j) ∂(RN q μ Ψ β (n + 1)) := by
  have := h.isProb_RN (N := n + 1) hβ.le
  unfold Xibar empXi
  rw [integral_smul, smul_smul]
  have hint : ∀ j : Fin (n + 1), Integrable (fun X : Config d (n + 1) => Xi μ Ψ (X j))
      (RN q μ Ψ β (n + 1)) := fun j =>
    Integrable.of_bound (h.measurable_Xi.comp (measurable_pi_apply j)).aestronglyMeasurable
      (2 * Real.sqrt (gL 0)) (Filter.Eventually.of_forall fun X => h.norm_Xi_le _)
  rw [integral_finsetSum _ fun j _ => hint j]
  have : ((n : ℝ) + 1) * (1 / (((n + 1 : ℕ) : ℝ))) = 1 := by
    push_cast
    field_simp
  rw [this, one_smul]

end Mean

section Mean2

open HRS.External.Entropy

variable {d M : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {q gL : Torus d → ℝ}
  {Ψ : Torus d → EuclideanSpace ℝ (Fin M)} {γ : ℝ} (h : RefHyp μ q gL Ψ γ) {β : ℝ} (hβ : 0 < β)

include h hβ in
/-- **Mean comparison** (the pole and the pin only move the mean statistic by `O(1)`). -/
theorem mean_norm_le (n : ℕ) (ht : ∀ x, |inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ 1)
    (hκ : KappaSmall β γ) (x : Torus d) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖∫ y, (∑ i, Xi μ Ψ (y i) + (Xi μ Ψ x - ((n : ℝ) + 1) • Xibar q μ Ψ β (n + 1)))
        ∂(Rpole h hβ n ht x t)‖ ≤ 10 * Real.sqrt (gL 0) := by
  have := isProb_Rpole h hβ n ht x ht0 ht1
  have := h.isProb_RN (N := n + 1) hβ.le
  set ν := Rpole h hβ n ht x t with hν
  set ρN := RN q μ Ψ β (n + 1) with hρN
  set r := Real.sqrt (gL 0) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hκ' := weakKappa_Vp_le h hβ n ht hκ
  have hκ0 := weakKappa_nonneg (Vp h hβ n ht) hβ.le
  set κ := weakKappa (Vp h hβ n ht) β with hκdef
  have hXm := h.measurable_Xi
  have hXb : ∀ z, ‖Xi μ Ψ z‖ ≤ 2 * r := fun z => h.norm_Xi_le z
  -- integrability
  have hint : ∀ i : Fin n, Integrable (fun y : Config d n => Xi μ Ψ (y i)) ν := fun i =>
    Integrable.of_bound (hXm.comp (measurable_pi_apply i)).aestronglyMeasurable (2 * r)
      (Filter.Eventually.of_forall fun y => hXb _)
  have hintN : ∀ j : Fin (n + 1), Integrable (fun X : Config d (n + 1) => Xi μ Ψ (X j)) ρN :=
    fun j => Integrable.of_bound (hXm.comp (measurable_pi_apply j)).aestronglyMeasurable (2 * r)
      (Filter.Eventually.of_forall fun y => hXb _)
  -- the mean
  have hmean : ∫ y, (∑ i, Xi μ Ψ (y i) + (Xi μ Ψ x - ((n : ℝ) + 1) • Xibar q μ Ψ β (n + 1))) ∂ν
      = ∑ i : Fin n, (∫ y, Xi μ Ψ (y i) ∂ν
          - ∫ X, Xi μ Ψ (X ((0 : Fin (n + 1)).succAbove i)) ∂ρN)
        + (Xi μ Ψ x - ∫ X, Xi μ Ψ (X 0) ∂ρN) := by
    have e1 : ∫ y, (∑ i, Xi μ Ψ (y i) + (Xi μ Ψ x - ((n : ℝ) + 1) • Xibar q μ Ψ β (n + 1))) ∂ν
        = ∑ i, ∫ y, Xi μ Ψ (y i) ∂ν
          + (Xi μ Ψ x - ((n : ℝ) + 1) • Xibar q μ Ψ β (n + 1)) := by
      rw [integral_add (integrable_finsetSum _ fun i _ => hint i) (integrable_const _),
        integral_finsetSum _ fun i _ => hint i]
      simp
    rw [e1, Xibar_mul h hβ n, Fin.sum_univ_succAbove _ (0 : Fin (n + 1)), Finset.sum_sub_distrib]
    abel
  rw [hmean]
  -- each coordinate
  have hcoord : ∀ i : Fin n, ‖∫ y, Xi μ Ψ (y i) ∂ν
      - ∫ X, Xi μ Ψ (X ((0 : Fin (n + 1)).succAbove i)) ∂ρN‖ ≤ 2 * (2 * r) * (3 * κ / ((n : ℝ) + 1)) := by
    intro i
    have htv := marginal_tv_le h hβ n ht hκ x ht0 ht1 i
    have hnorm := RefSmall.norm_integral_sub_le_two_mul_tvDist (M := M)
      (ν.map (fun y => y i)) (ρN.map (fun X => X ((0 : Fin (n + 1)).succAbove i)))
      hXm (by positivity) hXb
    rw [integral_map (measurable_pi_apply i).aemeasurable hXm.aestronglyMeasurable,
      integral_map (measurable_pi_apply ((0 : Fin (n + 1)).succAbove i)).aemeasurable
        hXm.aestronglyMeasurable] at hnorm
    refine hnorm.trans ?_
    exact mul_le_mul_of_nonneg_left htv (by positivity)
  have hsum : ‖∑ i : Fin n, (∫ y, Xi μ Ψ (y i) ∂ν
      - ∫ X, Xi μ Ψ (X ((0 : Fin (n + 1)).succAbove i)) ∂ρN)‖ ≤ 6 * r := by
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i : Fin n, ‖∫ y, Xi μ Ψ (y i) ∂ν
          - ∫ X, Xi μ Ψ (X ((0 : Fin (n + 1)).succAbove i)) ∂ρN‖
        ≤ ∑ _i : Fin n, 2 * (2 * r) * (3 * κ / ((n : ℝ) + 1)) := Finset.sum_le_sum fun i _ => hcoord i
      _ = n * (2 * (2 * r) * (3 * κ / ((n : ℝ) + 1))) := by simp
      _ ≤ 6 * r := by
          have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
          have : (n : ℝ) * (2 * (2 * r) * (3 * κ / ((n : ℝ) + 1)))
              = (12 * r * κ) * ((n : ℝ) / ((n : ℝ) + 1)) := by
            field_simp
            ring
          rw [this]
          have h1 : (n : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
            rw [div_le_one hn1]; linarith
          have h2 : 0 ≤ 12 * r * κ := by positivity
          nlinarith
  have hrest : ‖Xi μ Ψ x - ∫ X, Xi μ Ψ (X 0) ∂ρN‖ ≤ 4 * r := by
    refine (norm_sub_le _ _).trans ?_
    have : ‖∫ X, Xi μ Ψ (X 0) ∂ρN‖ ≤ 2 * r := by
      have := norm_integral_le_of_norm_le_const (μ := ρN) (f := fun X : Config d (n + 1) => Xi μ Ψ (X 0))
        (C := 2 * r) (Filter.Eventually.of_forall fun X => hXb _)
      simpa using this
    linarith [hXb x]
  calc _ ≤ ‖∑ i : Fin n, (∫ y, Xi μ Ψ (y i) ∂ν
      - ∫ X, Xi μ Ψ (X ((0 : Fin (n + 1)).succAbove i)) ∂ρN)‖
      + ‖Xi μ Ψ x - ∫ X, Xi μ Ψ (X 0) ∂ρN‖ := norm_add_le _ _
    _ ≤ 10 * r := by linarith

end Mean2

section Esq

open HRS.External.Entropy

variable {d M : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {q gL : Torus d → ℝ}
  {Ψ : Torus d → EuclideanSpace ℝ (Fin M)} {γ : ℝ} (h : RefHyp μ q gL Ψ γ) {β : ℝ} (hβ : 0 < β)

theorem Wv_eq (n : ℕ) (x : Torus d) (Xb : EuclideanSpace ℝ (Fin M)) (y : Config d n) :
    ∑ i, Ψ (y i) + Ψ x - ((n : ℝ) + 1) • (∫ w, Ψ w ∂μ + Xb)
      = ∑ i, Xi μ Ψ (y i) + (Xi μ Ψ x - ((n : ℝ) + 1) • Xb) := by
  simp only [Xi]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ]
  module

include h hβ in
/-- **Second moment** `E_R |S + Ψ x - (n+1)(m + Ξ̄)|² ≤ 100 (n+1) g_L(0)`. -/
theorem Esq_le (n : ℕ) (hn : 1 ≤ n) (ht : ∀ x, |inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ 1)
    (hκ : KappaSmall β γ) (x : Torus d) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ∫ y, ‖∑ i, Ψ (y i) + Ψ x - ((n : ℝ) + 1) • (∫ w, Ψ w ∂μ + Xibar q μ Ψ β (n + 1))‖ ^ 2
        ∂(Rpole h hβ n ht x t) ≤ 100 * ((n : ℝ) + 1) * gL 0 := by
  have : NeZero n := ⟨by omega⟩
  have := isProb_Rpole h hβ n ht x ht0 ht1
  have hlam0 : 0 ≤ lamN β n := div_nonneg hβ.le (Nat.cast_nonneg _)
  have hψ := isField_psiPole (Vp h hβ n ht) hlam0 ht0 ht1 x
  have hκ' := weakKappa_Vp_le h hβ n ht hκ
  have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
  have hlam : lamN β n = β / ((n + 1 : ℕ) : ℝ) := rfl
  have hΛ : (Vp h hβ n ht).M' + lamN β n * (Vp h hβ n ht).γ + lamN β n * n * (Vp h hβ n ht).γ
      ≤ (Vp h hβ n ht).M' + β * (Vp h hβ n ht).γ := by
    have hmul : lamN β n * ((n : ℝ) + 1) = β := (lamN_mul (β := β) n).symm
    refine le_of_eq ?_
    calc (Vp h hβ n ht).M' + lamN β n * (Vp h hβ n ht).γ + lamN β n * n * (Vp h hβ n ht).γ
        = (Vp h hβ n ht).M' + (lamN β n * ((n : ℝ) + 1)) * (Vp h hβ n ht).γ := by ring
      _ = _ := by rw [hmul]
  have hΛ' : (Vp h hβ n ht).M' + lamN β n * (Vp h hβ n ht).γ + lamN β n * n * (Vp h hβ n ht).γ
      ≤ (Vp h hβ n ht).M' + β * (Vp h hβ n ht).γ := hΛ
  have hrow : ∀ i : Fin n, ∑ _j ∈ Finset.univ.erase i,
      4 * Real.exp ((Vp h hβ n ht).M + ((Vp h hβ n ht).M' + β * (Vp h hβ n ht).γ)) * lamN β n
        * (Vp h hβ n ht).γ ≤ 1 / 2 := by
    intro i
    rw [hlam, four_exp_eq]
    exact (row_sum_le_of_uniform (Nat.succ_pos n) (Nat.le_succ n)
      (weakKappa_nonneg (Vp h hβ n ht) hβ.le) i).trans hκ'
  have hΛ2 : (Vp h hβ n ht).M' + lamN β n * (Vp h hβ n ht).γ + lamN β n * (n : ℝ) * (Vp h hβ n ht).γ
      ≤ (Vp h hβ n ht).M' + β * (Vp h hβ n ht).γ := hΛ
  have hmain := field_second_moment_vec (V := Vp h hβ n ht) hψ hlam0
    (Λ := (Vp h hβ n ht).M' + β * (Vp h hβ n ht).γ) hΛ2 hrow h.Ψ_meas
    (r := Real.sqrt (gL 0)) (h.norm_Ψ_le)
    (Ψ x - ((n : ℝ) + 1) • (∫ w, Ψ w ∂μ + Xibar q μ Ψ β (n + 1)))
  have hg0 := h.gL_zero_nonneg
  have hr2 : Real.sqrt (gL 0) ^ 2 = gL 0 := Real.sq_sqrt hg0
  have e1 : ∀ y : Config d n, ∑ i, Ψ (y i) + Ψ x - ((n : ℝ) + 1) • (∫ w, Ψ w ∂μ + Xibar q μ Ψ β (n + 1))
      = ∑ i, Ψ (y i) + (Ψ x - ((n : ℝ) + 1) • (∫ w, Ψ w ∂μ + Xibar q μ Ψ β (n + 1))) :=
    fun y => by abel
  have e2 : ∀ y : Config d n, ∑ i, Ψ (y i) + (Ψ x - ((n : ℝ) + 1) • (∫ w, Ψ w ∂μ + Xibar q μ Ψ β (n + 1)))
      = ∑ i, Xi μ Ψ (y i) + (Xi μ Ψ x - ((n : ℝ) + 1) • Xibar q μ Ψ β (n + 1)) :=
    fun y => by rw [← e1, Wv_eq]
  simp_rw [e2] at hmain
  have hmain' : ∫ y : Config d n, ‖∑ i, Xi μ Ψ (y i) + (Xi μ Ψ x - ((n : ℝ) + 1) • Xibar q μ Ψ β (n + 1))‖ ^ 2
        ∂(Rpole h hβ n ht x t)
      ≤ 2 * n * ∫ y : Config d n, ‖Ψ (y 0)‖ ^ 2 ∂(Rpole h hβ n ht x t)
        + ‖∫ y : Config d n, (∑ i, Xi μ Ψ (y i) + (Xi μ Ψ x - ((n : ℝ) + 1) • Xibar q μ Ψ β (n + 1)))
            ∂(Rpole h hβ n ht x t)‖ ^ 2 := hmain
  have e3 : ∫ y : Config d n, ‖Ψ (y 0)‖ ^ 2 ∂(Rpole h hβ n ht x t) = gL 0 := by
    have : ∀ y : Config d n, ‖Ψ (y 0)‖ ^ 2 = gL 0 := fun y => (h.gL_zero (y 0)).symm
    simp_rw [this]
    simp
  rw [e3] at hmain'
  have hmean := mean_norm_le h hβ n ht hκ x ht0 ht1
  have hsq : ‖∫ y : Config d n, (∑ i, Xi μ Ψ (y i) + (Xi μ Ψ x - ((n : ℝ) + 1) • Xibar q μ Ψ β (n + 1)))
        ∂(Rpole h hβ n ht x t)‖ ^ 2 ≤ 100 * gL 0 := by
    calc _ ≤ (10 * Real.sqrt (gL 0)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hmean 2
      _ = 100 * gL 0 := by rw [mul_pow, hr2]; ring
  simp_rw [e1, e2]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith [mul_nonneg hn0 hg0]

end Esq

section Large

open HRS.External.Entropy

variable {d M : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {q gL : Torus d → ℝ}
  {Ψ : Torus d → EuclideanSpace ℝ (Fin M)} {γ : ℝ} (h : RefHyp μ q gL Ψ γ) {β : ℝ} (hβ : 0 < β)

include h hβ in
/-- **Density bound for the pole law** (`A:eq:bounded-transfer` with the pole present):
`P ≤ e^{52 β g_L(0)} R^{x,t}`. -/
theorem pole_le_Rpole (c : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (ht : ∀ x, |inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ 1) (hκ : KappaSmall β γ)
    (x : Torus d) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (Measure.pi fun _ : Fin n => μ).tilted (EPole (gTot gL q c) μ n (lamN β n) β t x) ≤
      ENNReal.ofReal (Real.exp (52 * β * gL 0)) • Rpole h hβ n ht x t := by
  rw [pole_tilted_eq h hβ c n ht x ht0 ht1]
  have h1 := tilted_aPole_le h hβ n ht x ht0 ht1
    (Esq := 100 * ((n : ℝ) + 1) * gL 0) (Esq_le h hβ n hn ht hκ x ht0 ht1)
  refine h1.trans ?_
  have hmul : lamN β n * ((n : ℝ) + 1) = β := (lamN_mul (β := β) n).symm
  have : 2 * β * gL 0 + lamN β n / 2 * (100 * ((n : ℝ) + 1) * gL 0) = 52 * β * gL 0 := by
    calc 2 * β * gL 0 + lamN β n / 2 * (100 * ((n : ℝ) + 1) * gL 0)
        = 2 * β * gL 0 + 50 * (lamN β n * ((n : ℝ) + 1)) * gL 0 := by ring
      _ = _ := by rw [hmul]; ring
  rw [this]

include h hβ in
/-- **The variance bound for the weak reference with a pole, transferred to the pole law.** -/
theorem pole_evariance_le (c : ℝ) (n : ℕ) (hn : 1 ≤ n)
    (ht : ∀ x, |inner ℝ (tN q μ Ψ β (n + 1)) (Xi μ Ψ x)| ≤ 1) (hκ : KappaSmall β γ)
    (x : Torus d) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (P : Measure (Config d n)) [IsProbabilityMeasure P]
    (hP : P = (Measure.pi fun _ : Fin n => μ).tilted (EPole (gTot gL q c) μ n (lamN β n) β t x))
    {f : Torus d → ℝ} (hf : Measurable f) :
    evariance (fun y : Config d n => ∑ i, f (y i)) P ≤
      ENNReal.ofReal (Real.exp (52 * β * gL 0)) * (2 * n *
        ∫⁻ z, ‖f z‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (β * γ +
          psiPole (Vp h hβ n ht) (lamN β n) t x z)) ∂μ) := by
  have : NeZero n := ⟨by omega⟩
  have := isProb_Rpole h hβ n ht x ht0 ht1
  have hle := pole_le_Rpole h hβ c n hn ht hκ x ht0 ht1
  rw [← hP] at hle
  have hF : Measurable fun y : Config d n => ∑ i, f (y i) :=
    Finset.measurable_sum _ fun j _ => hf.comp (measurable_pi_apply j)
  refine (evariance_le_of_le_smul hle hF).trans ?_
  gcongr
  have hlam0 : 0 ≤ lamN β n := div_nonneg hβ.le (Nat.cast_nonneg _)
  have hψ := isField_psiPole (Vp h hβ n ht) hlam0 ht0 ht1 x
  have hκ' := weakKappa_Vp_le h hβ n ht hκ
  have hmul : lamN β n * ((n : ℝ) + 1) = β := (lamN_mul (β := β) n).symm
  have hlam : lamN β n = β / ((n + 1 : ℕ) : ℝ) := rfl
  have hΛ : (Vp h hβ n ht).M' + lamN β n * (Vp h hβ n ht).γ + lamN β n * n * (Vp h hβ n ht).γ
      ≤ (Vp h hβ n ht).M' + β * (Vp h hβ n ht).γ := by
    refine le_of_eq ?_
    calc (Vp h hβ n ht).M' + lamN β n * (Vp h hβ n ht).γ + lamN β n * n * (Vp h hβ n ht).γ
        = (Vp h hβ n ht).M' + (lamN β n * ((n : ℝ) + 1)) * (Vp h hβ n ht).γ := by ring
      _ = _ := by rw [hmul]
  have hrow : ∀ i : Fin n, ∑ _j ∈ Finset.univ.erase i,
      4 * Real.exp ((Vp h hβ n ht).M + ((Vp h hβ n ht).M' + β * (Vp h hβ n ht).γ)) * lamN β n
        * (Vp h hβ n ht).γ ≤ 1 / 2 := by
    intro i
    rw [hlam, four_exp_eq]
    exact (row_sum_le_of_uniform (Nat.succ_pos n) (Nat.le_succ n)
      (weakKappa_nonneg (Vp h hβ n ht) hβ.le) i).trans hκ'
  have hvar := field_linear_variance_symm (V := Vp h hβ n ht) hψ hlam0 hΛ hrow f hf
  refine hvar.trans ?_
  gcongr
  -- the marginal bound
  set π0 := (Rpole h hβ n ht x t).map (fun y => y 0) with hπ0
  have : IsProbabilityMeasure π0 := inferInstance
  refine (evariance_le_lintegral_sub π0 hf.aestronglyMeasurable 0).trans ?_
  have hdom : π0 ≤ μ.withDensity (fun z => ENNReal.ofReal (Real.exp
      ((Vp h hβ n ht).M' + β * (Vp h hβ n ht).γ + psiPole (Vp h hβ n ht) (lamN β n) t x z))) := by
    rw [Measure.le_iff]
    intro A hA
    rw [withDensity_apply _ hA]
    exact field_marginal_le (V := Vp h hβ n ht) hψ hlam0 hΛ ⟨0, by omega⟩ hA
  have hM' : (Vp h hβ n ht).M' = 0 := rfl
  have hγ : (Vp h hβ n ht).γ = γ := rfl
  rw [hM', hγ, zero_add] at hdom
  calc ∫⁻ z, ‖f z - 0‖ₑ ^ 2 ∂π0
      ≤ ∫⁻ z, ‖f z - 0‖ₑ ^ 2 ∂(μ.withDensity (fun z => ENNReal.ofReal (Real.exp
          (β * γ + psiPole (Vp h hβ n ht) (lamN β n) t x z)))) := lintegral_mono' hdom le_rfl
    _ = ∫⁻ z, ENNReal.ofReal (Real.exp (β * γ + psiPole (Vp h hβ n ht) (lamN β n) t x z))
          * ‖f z - 0‖ₑ ^ 2 ∂μ := by
        rw [lintegral_withDensity_eq_lintegral_mul₀]
        · rfl
        · exact (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
            (measurable_const.add hψ.measurable))).aemeasurable
        · exact ((hf.sub_const 0).enorm.pow_const 2).aemeasurable
    _ = _ := by
        refine lintegral_congr fun z => ?_
        rw [sub_zero, mul_comm]

end Large

/-! ### Stage 5: the Riesz kernel -/

section Riesz

open HRS.External.Entropy

theorem tiltMeasure_tiltMeasure {α : Type*} [MeasurableSpace α] {P : Measure α}
    [IsProbabilityMeasure P] (w1 w2 : α → ℝ) (hm1 : Measurable w1) (hm2 : Measurable w2)
    (W1 W2 : ℝ) (h1 : ∀ a, w1 a ≤ W1) (h2 : ∀ a, w2 a ≤ W2) :
    tiltMeasure (tiltMeasure P w1) w2 = P.tilted (fun a => w1 a + w2 a) := by
  have hint : Integrable (fun a => Real.exp (w1 a)) P :=
    integrable_of_abs_le (Real.measurable_exp.comp hm1) (Real.exp W1) fun a => by
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.2 (h1 a)
  have e1 := RefSmall.tiltMeasure_eq_tilted P w1 hm1 W1 h1
  have : IsProbabilityMeasure (P.tilted w1) := isProbabilityMeasure_tilted hint
  rw [e1, RefSmall.tiltMeasure_eq_tilted (P.tilted w1) w2 hm2 W2 h2, tilted_tilted hint]
  rfl

variable {d : ℕ} {s : ℝ}

/-- The pole law is the tilt of `μ^{⊗n}` by `EPole`. -/
theorem poleLaw_eq_tilted (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) (n : ℕ) (lam : ℝ) (hlam : 0 ≤ lam) (x : Torus d) {t : ℝ}
    (ht : 0 ≤ t) :
    poleLaw (periodicRiesz d s) (withDensityReal ρ) n lam β x t
      = (Measure.pi fun _ : Fin n => withDensityReal ρ).tilted
          (EPole (periodicRiesz d s) (withDensityReal ρ) n lam β t x) := by
  have hμ := PoleCavityAux.isProbabilityMeasure_mu hρ
  obtain ⟨W, hW⟩ := PoleCavityAux.cavity_weight_le hd hs0 hsd β hρ n lam hlam
  have hg := PoleCavityAux.measurable_periodicRiesz hd hs0 hsd
  obtain ⟨B, hB⟩ := periodicRiesz_ge (d := d) hd hs0 hsd
  have hB' : ∀ z, -(max B 0) ≤ periodicRiesz d s z := fun z =>
    (neg_le_neg (le_max_left _ _)).trans (hB z)
  have hm1 : Measurable fun Y : Config d n => -lam * pairSum (periodicRiesz d s) Y
      + β * ∑ i, convMeasure (periodicRiesz d s) (withDensityReal ρ) (Y i) :=
    ((PoleCavityAux.measurable_pairSum hg).const_mul _).add
      ((Finset.measurable_sum _ fun i _ =>
        (PoleCavityAux.measurable_convMeasure hg _).comp (measurable_pi_apply i)).const_mul _)
  have hm2 : Measurable fun Y : Config d n => -(t * lam) * ∑ i, periodicRiesz d s (x - Y i) :=
    (Finset.measurable_sum _ fun i _ =>
      hg.comp (measurable_const.sub (measurable_pi_apply i))).const_mul _
  unfold poleLaw cavityLaw
  rw [tiltMeasure_tiltMeasure (P := Measure.pi fun _ : Fin n => withDensityReal ρ)
    (fun Y : Config d n => -lam * pairSum (periodicRiesz d s) Y
      + β * ∑ i, convMeasure (periodicRiesz d s) (withDensityReal ρ) (Y i))
    (fun Y : Config d n => -(t * lam) * ∑ i, periodicRiesz d s (x - Y i)) hm1 hm2
    W ((t * lam) * (max B 0 * n)) hW (fun Y => by
      have h1 := PoleCavityAux.sum_ge_of_ge (periodicRiesz d s) hB' x Y
      have := mul_le_mul_of_nonneg_left (neg_le_neg h1) (mul_nonneg ht hlam)
      linarith)]
  rfl

end Riesz

section RieszAE

open HRS.External.Entropy

variable {d : ℕ}

theorem ae_ne_pt {μ : Measure (Torus d)} (hatom : ∀ z : Torus d, μ {z} = 0) (y : Torus d) :
    ∀ᵐ z ∂μ, z ≠ y := by
  rw [ae_iff]
  simpa using hatom y

theorem ae_pi_ne_coord {μ : Measure (Torus d)} [IsProbabilityMeasure μ]
    (hatom : ∀ z : Torus d, μ {z} = 0) (n : ℕ) (x : Torus d) :
    ∀ᵐ Y ∂(Measure.pi fun _ : Fin n => μ), ∀ i, Y i ≠ x := by
  rw [ae_all_iff]
  intro i
  have : NullSingletonClass μ := ⟨hatom⟩
  have := Measure.pi_hyperplane (fun _ : Fin n => μ) i x
  rw [ae_iff]
  simpa using this

theorem EPole_ae_eq {g gS : Torus d → ℝ} (hgS : ∀ z, z ≠ 0 → g z = gS z)
    {μ : Measure (Torus d)} [IsProbabilityMeasure μ] (hatom : ∀ z : Torus d, μ {z} = 0)
    (n : ℕ) (lam β t : ℝ) (x : Torus d) :
    EPole g μ n lam β t x =ᵐ[Measure.pi fun _ : Fin n => μ] EPole gS μ n lam β t x := by
  filter_upwards [ae_distinct_pi hatom n, ae_pi_ne_coord hatom n x] with Y hY hx
  have h1 : pairSum g Y = pairSum gS Y := by
    unfold pairSum
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
    have hij : i < j := (Finset.mem_filter.1 hj).2
    exact hgS _ (sub_ne_zero.2 (hY i j hij.ne))
  have h2 : ∀ y : Torus d, convMeasure g μ y = convMeasure gS μ y := by
    intro y
    unfold convMeasure
    refine integral_congr_ae ?_
    filter_upwards [ae_ne_pt hatom y] with z hz
    exact hgS _ (sub_ne_zero.2 hz.symm)
  have h3 : ∑ i, g (x - Y i) = ∑ i, gS (x - Y i) :=
    Finset.sum_congr rfl fun i _ => hgS _ (sub_ne_zero.2 (hx i).symm)
  unfold EPole
  rw [h1, h3]
  simp_rw [h2]

end RieszAE

section RieszLarge

open HRS.External.Entropy HeatSplit

variable {d : ℕ} {s : ℝ}

/-- **The variance clause for large `N`** (the calibration field `t_N·Ξ` is small): the pole law
of the Riesz kernel satisfies `Var_P(∑ f(y_i)) ≤ C n ∫ |f|² e^{-tλ g(x-y)} dμ` with `C` independent
of `n, x, t, f`. -/
theorem riesz_pole_variance_large (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (L : ℕ) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {Λ : ℝ}
    (hρΛ : ∀ y, ρ y ≤ Λ) {M : ℕ} (Ψ : Torus d → EuclideanSpace ℝ (Fin M))
    (hΨ : ∀ x y, (weakSplit d s τ L).gL (x - y) = inner ℝ (Ψ x) (Ψ y))
    {β : ℝ} (hβ : 0 < β) (hκ : KappaSmall β (Λ * (weakSplit d s τ L).c))
    (n : ℕ) (hn : 1 ≤ n)
    (ht : ∀ x, |inner ℝ (tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β (n + 1))
      (Xi (withDensityReal ρ) Ψ x)| ≤ 1)
    (x : Torus d) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {f : Torus d → ℝ} (hf : Measurable f) :
    evariance (fun Y : Config d n => ∑ i, f (Y i))
        (poleLaw (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β x t) ≤
      ENNReal.ofReal (2 * Real.exp (52 * β * (weakSplit d s τ L).gL 0) *
          Real.exp (2 * β * (Λ * (weakSplit d s τ L).c) + 1 + β * (weakSplit d s τ L).gL 0) * n) *
        ∫⁻ y, ‖f y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-(t * (β / ((n + 1 : ℕ) : ℝ))) *
          periodicRiesz d s (x - y))) ∂(withDensityReal ρ) := by
  have hμ := PoleCavityAux.isProbabilityMeasure_mu hρ
  have hlam0 : 0 ≤ β / ((n + 1 : ℕ) : ℝ) := div_nonneg hβ.le (Nat.cast_nonneg _)
  set sp := weakSplit d s τ L with hsp
  have h := refHyp_weakSplit hd hs0 hsd hτ hτ1 L hρ.density hρΛ Ψ hΨ
  obtain ⟨-, -, hsplit, -, -, -, -, -, -, hc0, -⟩ := weakSplit_spec hd hs0 hsd hτ hτ1 L
  have hatom := atomless_withDensityReal (by omega : 1 ≤ d) ρ
  -- the pole law as a tilt
  have hP : poleLaw (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β x t
      = (Measure.pi fun _ : Fin n => withDensityReal ρ).tilted
          (EPole (gTot sp.gL sp.q sp.c) (withDensityReal ρ) n (lamN β n) β t x) := by
    rw [poleLaw_eq_tilted hd hs0 hsd β hρ n _ hlam0 x ht0]
    exact tilted_congr (EPole_ae_eq (gS := gTot sp.gL sp.q sp.c) (fun z hz => hsplit z hz) hatom n _ β t x)
  have : IsProbabilityMeasure
      (poleLaw (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β x t) :=
    PoleCavityAux.pole_isProb hd hs0 hsd β hρ n _ hlam0 x t ht0
  have hmain := pole_evariance_le h hβ sp.c n hn ht hκ x ht0 ht1 _ hP hf
  set γ := Λ * sp.c with hγ
  have hr2 : Real.sqrt (sp.gL 0) * Real.sqrt (sp.gL 0) = sp.gL 0 :=
    Real.mul_self_sqrt h.gL_zero_nonneg
  have hgLle : ∀ w : Torus d, ∀ a b : Torus d, w = a - b → sp.gL w ≤ sp.gL 0 := by
    intro w a b hw
    rw [hw, h.gL_eq]
    calc inner ℝ (Ψ a) (Ψ b) ≤ ‖Ψ a‖ * ‖Ψ b‖ := real_inner_le_norm _ _
      _ ≤ Real.sqrt (sp.gL 0) * Real.sqrt (sp.gL 0) :=
          mul_le_mul (h.norm_Ψ_le a) (h.norm_Ψ_le b) (norm_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := hr2
  have hlamle : β / ((n + 1 : ℕ) : ℝ) ≤ β := by
    rw [div_le_iff₀ (by positivity)]
    have : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    nlinarith
  have hpt : ∀ z : Torus d, z ≠ x →
      β * γ + psiPole (Vp h hβ n ht) (lamN β n) t x z ≤
        2 * β * γ + 1 + β * sp.gL 0 + (-(t * (β / ((n + 1 : ℕ) : ℝ))) * periodicRiesz d s (x - z)) := by
    intro z hz
    have h1 : β * convMeasure sp.q (withDensityReal ρ) z ≤ β * γ :=
      mul_le_mul_of_nonneg_left (h.conv_le z) hβ.le
    have h2 : inner ℝ (tN sp.q (withDensityReal ρ) Ψ β (n + 1)) (Xi (withDensityReal ρ) Ψ z) ≤ 1 :=
      (le_abs_self _).trans (ht z)
    have hsz := hsplit (x - z) (sub_ne_zero.2 (Ne.symm hz))
    have hqe : sp.q (z - x) = sp.q (x - z) := by
      rw [← h.q_even (x - z), neg_sub]
    have hgl := hgLle (x - z) x z rfl
    have htl : t * (β / ((n + 1 : ℕ) : ℝ)) ≤ β := by
      calc t * (β / ((n + 1 : ℕ) : ℝ)) ≤ 1 * β := mul_le_mul ht1 hlamle (by positivity) (by norm_num)
        _ = β := one_mul _
    have htl0 : 0 ≤ t * (β / ((n + 1 : ℕ) : ℝ)) := mul_nonneg ht0 hlam0
    have h3 : -(t * (β / ((n + 1 : ℕ) : ℝ))) * sp.q (z - x)
        ≤ β * sp.gL 0 + (-(t * (β / ((n + 1 : ℕ) : ℝ))) * periodicRiesz d s (x - z)) := by
      rw [hqe]
      have hq : sp.q (x - z) = periodicRiesz d s (x - z) - sp.gL (x - z) + sp.c := by
        rw [hsz]; ring
      rw [hq]
      have a1 := mul_le_mul_of_nonneg_left hgl htl0
      have a2 := mul_nonneg htl0 hc0
      have a3 := mul_le_mul_of_nonneg_right htl h.gL_zero_nonneg
      nlinarith
    have : psiPole (Vp h hβ n ht) (lamN β n) t x z
        = β * convMeasure sp.q (withDensityReal ρ) z
          + inner ℝ (tN sp.q (withDensityReal ρ) Ψ β (n + 1)) (Xi (withDensityReal ρ) Ψ z)
          + -(t * (β / ((n + 1 : ℕ) : ℝ))) * sp.q (z - x) := by
      simp only [psiPole, Vp, weakPot, lamN]
      ring
    rw [this]
    linarith
  have hint : ∫⁻ z, ‖f z‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (β * γ +
        psiPole (Vp h hβ n ht) (lamN β n) t x z)) ∂(withDensityReal ρ)
      ≤ ENNReal.ofReal (Real.exp (2 * β * γ + 1 + β * sp.gL 0)) *
        ∫⁻ y, ‖f y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-(t * (β / ((n + 1 : ℕ) : ℝ))) *
          periodicRiesz d s (x - y))) ∂(withDensityReal ρ) := by
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_ne_pt hatom x] with z hz
    have h1 := hpt z hz
    have h2 : ENNReal.ofReal (Real.exp (β * γ + psiPole (Vp h hβ n ht) (lamN β n) t x z))
        ≤ ENNReal.ofReal (Real.exp (2 * β * γ + 1 + β * sp.gL 0)) *
          ENNReal.ofReal (Real.exp (-(t * (β / ((n + 1 : ℕ) : ℝ))) * periodicRiesz d s (x - z))) := by
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← Real.exp_add]
      exact Real.exp_le_exp.2 (by linarith)
    calc ‖f z‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (β * γ + psiPole (Vp h hβ n ht) (lamN β n) t x z))
        ≤ ‖f z‖ₑ ^ 2 * (ENNReal.ofReal (Real.exp (2 * β * γ + 1 + β * sp.gL 0)) *
          ENNReal.ofReal (Real.exp (-(t * (β / ((n + 1 : ℕ) : ℝ))) * periodicRiesz d s (x - z)))) := by
          gcongr
      _ = _ := by ring
  refine hmain.trans ?_
  calc ENNReal.ofReal (Real.exp (52 * β * sp.gL 0)) * (2 * n * ∫⁻ z, ‖f z‖ₑ ^ 2 * ENNReal.ofReal
        (Real.exp (β * γ + psiPole (Vp h hβ n ht) (lamN β n) t x z)) ∂(withDensityReal ρ))
      ≤ ENNReal.ofReal (Real.exp (52 * β * sp.gL 0)) * (2 * n * (ENNReal.ofReal
        (Real.exp (2 * β * γ + 1 + β * sp.gL 0)) * ∫⁻ y, ‖f y‖ₑ ^ 2 * ENNReal.ofReal
          (Real.exp (-(t * (β / ((n + 1 : ℕ) : ℝ))) * periodicRiesz d s (x - y))) ∂(withDensityReal ρ))) := by
        gcongr
    _ = _ := by
        have e : ENNReal.ofReal (2 * Real.exp (52 * β * sp.gL 0) *
            Real.exp (2 * β * γ + 1 + β * sp.gL 0) * n)
            = ENNReal.ofReal (Real.exp (52 * β * sp.gL 0)) * (2 * n *
              ENNReal.ofReal (Real.exp (2 * β * γ + 1 + β * sp.gL 0))) := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_mul (by norm_num)]
          simp
          ring
        rw [e]
        ring

end RieszLarge

/-! ### Stage 6: smallness of the calibration field (glue to `ReferenceSmallness`) -/

section Glue

variable {d M : ℕ} {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {q gL : Torus d → ℝ}
  {Ψ : Torus d → EuclideanSpace ℝ (Fin M)} {γ : ℝ} (h : RefHyp μ q gL Ψ γ) {β : ℝ}

include h in
/-- The two definitions of the weak reference `R⁰_N` agree. -/
theorem R0_eq_R0small (hβ : 0 ≤ β) (N : ℕ) : R0 q μ β N = RefSmall.R0small q β μ N := by
  have hfun : (fun X : Config d N => β * ∑ i, convMeasure q μ (X i) - (β / N) * pairSum q X)
      = E0 q μ β N := by
    funext X
    unfold E0
    rw [PoleCavityAux.pairSum_eq h.q_even, Finset.mul_sum]
    have h2 : ∀ i : Fin N, ∑ j ∈ Finset.univ.erase i, q (X i - X j) = ∑ j, q (X i - X j) - q 0 := by
      intro i
      rw [Finset.sum_erase_eq_sub (Finset.mem_univ i)]
      simp
    simp_rw [h2]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold RefSmall.R0small
  show _ = tiltMeasure (Measure.pi fun _ : Fin N => μ)
    (fun X : Config d N => β * ∑ i, convMeasure q μ (X i) - (β / N) * pairSum q X)
  rw [hfun, RefSmall.tiltMeasure_eq_tilted _ _ (h.measurable_E0 β N) (β * N * γ) (h.E0_le hβ N)]
  rfl

include h in
theorem integral_empXi_R0 (hβ : 0 ≤ β) {N : ℕ} (hN : 0 < N) :
    ∫ X, empXi μ Ψ X ∂(R0 q μ β N) = RefSmall.meanFeature (Xi μ Ψ) (RefSmall.R0small q β μ N) := by
  rw [← R0_eq_R0small h hβ N]
  unfold RefSmall.meanFeature
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  beta_reduce
  rw [RefSmall.integral_empirical_vec hN X h.measurable_Xi]
  unfold empXi
  rw [one_div]

end Glue

section GlueRiesz

open HeatSplit

variable {d : ℕ} {s : ℝ}

/-- **Smallness of the calibration field** `sup_x |t_n · Ξ(x)| ≤ 1` for `n` large
(`EXT-5` plugged into the calibration of `EXT-4`). -/
theorem exists_small_calib (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {τ : ℝ} (hτ : 0 < τ)
    (hτ1 : τ ≤ 1) (L : ℕ) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {Λ : ℝ} (hΛ1 : 1 ≤ Λ)
    (hΛ : ∀ x, ρ x ≤ Λ) {M : ℕ} (Ψ : Torus d → EuclideanSpace ℝ (Fin M))
    (hΨ : ∀ x y, (weakSplit d s τ L).gL (x - y) = inner ℝ (Ψ x) (Ψ y)) {β : ℝ} (hβ : 0 < β) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ x : Torus d,
      |inner ℝ (tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β n) (Xi (withDensityReal ρ) Ψ x)| ≤ 1 := by
  have := isProb_withDensityReal hρ
  have h := refHyp_weakSplit hd hs0 hsd hτ hτ1 L hρ hΛ Ψ hΨ
  exact RefSmall.sup_calibration_field_le_one hd hs0 hsd hτ L hρ hΛ1 hΛ hβ.le h.measurable_Xi
    (B := 2 * Real.sqrt ((weakSplit d s τ L).gL 0)) (fun x => h.norm_Xi_le x) h.integral_Xi
    (fun n => tN (weakSplit d s τ L).q (withDensityReal ρ) Ψ β n) (fun n hn => by
      have := h.tN_norm_le hβ (N := n) hn
      rwa [integral_empXi_R0 h hβ.le hn] at this)

end GlueRiesz

/-! ### Stage 7: choice of the split parameters, the crude bound and the final assembly -/

section Final

open HeatSplit HRS.External.Entropy

variable {d : ℕ} {s : ℝ}

theorem kappaSmall_of_le {β γ : ℝ} (hβ : 0 < β) (hγ : 0 ≤ γ)
    (h : β * γ ≤ 1 / (16 * Real.exp 3)) : KappaSmall β γ := by
  unfold KappaSmall
  have hu0 : 0 ≤ β * γ := mul_nonneg hβ.le hγ
  have he3 : 1 ≤ Real.exp 3 := Real.one_le_exp (by norm_num)
  have hu1 : β * γ ≤ 1 := h.trans (by
    rw [div_le_one (by positivity)]
    linarith)
  have h1 : Real.exp (2 * (β * γ) + 1) ≤ Real.exp 3 := Real.exp_le_exp.2 (by linarith)
  have h2 : 4 * Real.exp (2 * (β * γ) + 1) * (β * γ) ≤ 4 * Real.exp 3 * (1 / (16 * Real.exp 3)) := by
    gcongr
  have h3 : 4 * Real.exp 3 * (1 / (16 * Real.exp 3)) = 1 / 4 := by
    field_simp
    norm_num
  linarith

/-- Choice of the split: `κ` small, features, density bound. -/
theorem exists_split_params (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    ∃ (τ : ℝ) (L : ℕ) (Λ : ℝ) (M : ℕ) (Ψ : Torus d → EuclideanSpace ℝ (Fin M)),
      0 < τ ∧ τ ≤ 1 ∧ 1 ≤ Λ ∧ (∀ y, ρ y ≤ Λ) ∧
      (∀ x y, (weakSplit d s τ L).gL (x - y) = inner ℝ (Ψ x) (Ψ y)) ∧
      KappaSmall β (Λ * (weakSplit d s τ L).c) := by
  obtain ⟨Λ0, hΛ0, hΛ0b⟩ := PoleCavityAux.exists_density_bound hρ
  set Λ := max Λ0 1 with hΛ
  have hΛpos : 0 < Λ := lt_max_of_lt_right one_pos
  have hΛ1 : 1 ≤ Λ := le_max_right _ _
  have hΛb : ∀ y, ρ y ≤ Λ := fun y => (hΛ0b y).trans (le_max_left _ _)
  set u : ℝ := 1 / (16 * Real.exp 3) with hu
  have hu0 : 0 < u := by positivity
  obtain ⟨τ, hτ, hτ1, L₀, hL₀⟩ := weakSplit_small hd hs0 hsd (ε := u / (β * Λ)) (by positivity)
  obtain ⟨M, Ψ, -, hΨ, -⟩ := RefSmall.exists_continuous_features_weakSplit hd hs0 hsd hτ L₀
  refine ⟨τ, L₀, Λ, M, Ψ, hτ, hτ1, hΛ1, hΛb, hΨ, ?_⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, hc0, -⟩ := weakSplit_spec hd hs0 hsd hτ hτ1 L₀
  have hc := hL₀ L₀ le_rfl
  refine kappaSmall_of_le hβ (mul_nonneg hΛpos.le hc0) ?_
  calc β * (Λ * (weakSplit d s τ L₀).c) ≤ β * (Λ * (u / (β * Λ))) := by gcongr
    _ = u := by field_simp

end Final

section Crude

open HRS.External.Entropy

variable {d : ℕ} {s : ℝ}

/-- Crude bound (Cauchy-Schwarz and the one-coordinate density bound), valid for all `N ≥ 2`
with a constant `K n²`. -/
theorem riesz_pole_variance_crude (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ, 1 ≤ n → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ f : Torus d → ℝ, Measurable f →
        evariance (fun Y : Config d n => ∑ i, f (Y i))
            (poleLaw (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β x t) ≤
          ENNReal.ofReal (K * (n : ℝ) ^ 2) *
            ∫⁻ y, ‖f y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-(t * (β / ((n + 1 : ℕ) : ℝ))) *
              periodicRiesz d s (x - y))) ∂(withDensityReal ρ) := by
  have hμ := PoleCavityAux.isProbabilityMeasure_mu hρ
  obtain ⟨B, Cc, hB, hK⟩ := PoleCavityAux.kerData_periodicRiesz hd hs0 hsd hρ
  refine ⟨Real.exp (PoleCavityAux.Kbound (periodicRiesz d s) B Cc β 1), Real.exp_pos _, ?_⟩
  intro n hn x t ht f hf
  have hN0 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hl : 0 ≤ β / ((n + 1 : ℕ) : ℝ) := by positivity
  have hlb : β / ((n + 1 : ℕ) : ℝ) ≤ β := by
    rw [div_le_iff₀ hN0]
    have : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
    nlinarith
  have hln : β / ((n + 1 : ℕ) : ℝ) * (n : ℝ) ≤ β := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hN0]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  have : IsProbabilityMeasure
      (poleLaw (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β x t) :=
    PoleCavityAux.pole_isProb hd hs0 hsd β hρ n _ hl x t ht.1
  set P := poleLaw (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β x t with hP
  have hF : Measurable fun Y : Config d n => ∑ i, f (Y i) :=
    Finset.measurable_sum _ fun j _ => hf.comp (measurable_pi_apply j)
  refine (evariance_le_lintegral_sub P hF.aestronglyMeasurable 0).trans ?_
  -- Cauchy-Schwarz
  have hCS : ∀ Y : Config d n, ‖∑ i, f (Y i) - 0‖ₑ ^ 2 ≤ (n : ℝ≥0∞) * ∑ i, ‖f (Y i)‖ₑ ^ 2 := by
    intro Y
    rw [sub_zero]
    have h1 : (∑ i, f (Y i)) ^ 2 ≤ (n : ℝ) * ∑ i, f (Y i) ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin n => f (Y i))
      simpa using this
    have e1 : ‖∑ i, f (Y i)‖ₑ ^ 2 = ENNReal.ofReal ((∑ i, f (Y i)) ^ 2) := by
      rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
    have e2 : ∀ i, ‖f (Y i)‖ₑ ^ 2 = ENNReal.ofReal (f (Y i) ^ 2) := fun i => by
      rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
    rw [e1]
    simp_rw [e2]
    calc ENNReal.ofReal ((∑ i, f (Y i)) ^ 2) ≤ ENNReal.ofReal ((n : ℝ) * ∑ i, f (Y i) ^ 2) :=
          ENNReal.ofReal_le_ofReal h1
      _ = (n : ℝ≥0∞) * ∑ i, ENNReal.ofReal (f (Y i) ^ 2) := by
          rw [ENNReal.ofReal_mul (Nat.cast_nonneg n), ENNReal.ofReal_natCast,
            ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
  refine (lintegral_mono hCS).trans ?_
  rw [lintegral_const_mul' _ _ (by simp), lintegral_finsetSum Finset.univ
    (f := fun (i : Fin n) (Y : Config d n) => ‖f (Y i)‖ₑ ^ 2)
    (fun i _ => ((hf.comp (measurable_pi_apply i)).enorm.pow_const 2))]
  have hone : ∀ i : Fin n, ∫⁻ Y, ‖f (Y i)‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal (Real.exp
      (PoleCavityAux.Kbound (periodicRiesz d s) B Cc β 1)) *
      ∫⁻ y, ‖f y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-(t * (β / ((n + 1 : ℕ) : ℝ))) *
        periodicRiesz d s (x - y))) ∂(withDensityReal ρ) := by
    intro i
    have hle := PoleCavityAux.pole_one_le hK hB i hβ.le ht.1 ht.2 hl hlb hln x
    have hm : Measurable fun Y : Config d n => Y i := measurable_pi_apply i
    calc ∫⁻ Y, ‖f (Y i)‖ₑ ^ 2 ∂P = ∫⁻ z, ‖f z‖ₑ ^ 2 ∂(P.map fun Y : Config d n => Y i) := by
          rw [lintegral_map (hf.enorm.pow_const 2) hm]
      _ ≤ ∫⁻ z, ‖f z‖ₑ ^ 2 ∂(withDensityReal ρ |>.withDensity (fun y => ENNReal.ofReal
            (Real.exp (PoleCavityAux.Kbound (periodicRiesz d s) B Cc β 1)) *
            ENNReal.ofReal (Real.exp (-(t * (β / ((n + 1 : ℕ) : ℝ))) * periodicRiesz d s (x - y))))) :=
          lintegral_mono' hle le_rfl
      _ = _ := by
          rw [lintegral_withDensity_eq_lintegral_mul₀]
          · rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
            refine lintegral_congr fun z => ?_
            simp only [Pi.mul_apply]
            ring
          · exact ((measurable_const.mul (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
              ((hK.meas.comp (measurable_const.sub measurable_id)).const_mul _))))).aemeasurable
          · exact (hf.enorm.pow_const 2).aemeasurable
  calc (n : ℝ≥0∞) * ∑ i : Fin n, ∫⁻ Y, ‖f (Y i)‖ₑ ^ 2 ∂P
      ≤ (n : ℝ≥0∞) * ∑ _i : Fin n, ENNReal.ofReal (Real.exp
        (PoleCavityAux.Kbound (periodicRiesz d s) B Cc β 1)) *
        ∫⁻ y, ‖f y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-(t * (β / ((n + 1 : ℕ) : ℝ))) *
          periodicRiesz d s (x - y))) ∂(withDensityReal ρ) := by
        gcongr with i _
        exact hone i
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_pow (Nat.cast_nonneg n),
          ENNReal.ofReal_natCast]
        ring

end Crude

section Main

open HRS.External.Entropy HeatSplit

variable {d : ℕ} {s : ℝ}

/-- **The variance clause of Lemma 4.1** (`A:eq:pole-variance`), in the form of
`PoleCavityAux.pole_variance_clause`. -/
theorem pole_variance_clause_final (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ f : Torus d → ℝ, Measurable f →
        evariance (fun Y : Config d (N - 1) => ∑ i, f (Y i))
            (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ≤
          ENNReal.ofReal (C * ((N - 1 : ℕ) : ℝ)) *
            ∫⁻ y, ‖f y‖ₑ ^ 2 *
              ENNReal.ofReal (Real.exp (-(t * (β / N)) * periodicRiesz d s (x - y)))
              ∂(withDensityReal ρ) := by
  obtain ⟨τ, L, Λ, M, Ψ, hτ, hτ1, hΛ1, hΛ, hΨ, hκ⟩ := exists_split_params hd hs0 hsd hβ hρ
  obtain ⟨n₀, hn₀⟩ := exists_small_calib hd hs0 hsd hτ hτ1 L hρ.density hΛ1 hΛ Ψ hΨ hβ
  obtain ⟨K, hK0, hKb⟩ := riesz_pole_variance_crude hd hs0 hsd β hβ hρ
  set C₁ : ℝ := 2 * Real.exp (52 * β * (weakSplit d s τ L).gL 0) *
    Real.exp (2 * β * (Λ * (weakSplit d s τ L).c) + 1 + β * (weakSplit d s τ L).gL 0) with hC₁
  have hC₁pos : 0 < C₁ := by positivity
  refine ⟨max C₁ (K * n₀), lt_max_of_lt_left hC₁pos, ?_⟩
  intro N hN x t ht f hf
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 1 ≤ n := by omega
  show evariance (fun Y : Config d n => ∑ i, f (Y i))
      (poleLaw (periodicRiesz d s) (withDensityReal ρ) n (β / ((n + 1 : ℕ) : ℝ)) β x t) ≤
    ENNReal.ofReal (max C₁ (K * n₀) * (n : ℝ)) *
      ∫⁻ y, ‖f y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-(t * (β / ((n + 1 : ℕ) : ℝ))) *
        periodicRiesz d s (x - y))) ∂(withDensityReal ρ)
  by_cases hlarge : n₀ ≤ n + 1
  · have h1 := riesz_pole_variance_large hd hs0 hsd hτ hτ1 L hρ hΛ Ψ hΨ hβ hκ n hn
      (hn₀ (n + 1) hlarge) x ht.1 ht.2 hf
    refine h1.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) this
  · have h1 := hKb n hn x t ht f hf
    refine h1.trans (mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _)
    have hn1 : (n : ℝ) ≤ n₀ := by exact_mod_cast (by omega : n ≤ n₀)
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    calc K * (n : ℝ) ^ 2 = (K * n) * n := by ring
      _ ≤ (K * n₀) * n := by gcongr
      _ ≤ max C₁ (K * n₀) * n := mul_le_mul_of_nonneg_right (le_max_right _ _) hn0

end Main

end PoleVar

end HRS.External

/-! ### Lemma 4.1 (`M:A:lem:pole`): the three clauses

The theorems below keep their original names and statements; they were moved here from
`PoleCavity.lean` because the proof of the variance clause needs `HeatSplit`/`CalibratedReference`,
which import `PoleCavity`. -/

namespace HRS

variable {d : ℕ} {s : ℝ}

namespace PoleCavityAux

/-- The variance clause of Lemma 4.1 (`A:eq:pole-variance`); see the route comment of this file. -/
theorem pole_variance_clause (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ f : Torus d → ℝ, Measurable f →
        evariance (fun Y : Config d (N - 1) => ∑ i, f (Y i))
            (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ≤
          ENNReal.ofReal (C * ((N - 1 : ℕ) : ℝ)) *
            ∫⁻ y, ‖f y‖ₑ ^ 2 *
              ENNReal.ofReal (Real.exp (-(t * (β / N)) * periodicRiesz d s (x - y)))
              ∂(withDensityReal ρ) := by
  exact HRS.External.PoleVar.pole_variance_clause_final hd hs0 hsd β hβ ρ hρ

end PoleCavityAux

/-- Lemma 4.1 `M:A:lem:pole` (source lines 3564-3577), `A:eq:pole-variance`,
`A:eq:pole-density-one`, `A:eq:pole-density-two`: uniformly in `N ≥ 2`, `x ∈ 𝕋^d`,
`0 ≤ t ≤ 1`, with `n = N - 1`, `λ = β/N`,
`Var_{P_n^{x,t}}[∑_i f(y_i)] ≤ C n ∫ |f|² e^{-tλ g(x-y)} dμ(y)`,
`d(P_n^{x,t})^{(1)}/dμ (y) ≤ C e^{-tλ g(x-y)}` and
`d(P_n^{x,t})^{(2)}/dμ^{⊗2} (y,z) ≤ C e^{-tλ (g(x-y) + g(x-z))}`.
The two-particle density is stated for every ordered pair of distinct coordinates. The last
sentence of the source (the same for the weak calibrated reference) concerns a proof-internal
object and is not specified. -/
theorem pole_variance_density (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      (∀ f : Torus d → ℝ, Measurable f →
        evariance (fun Y : Config d (N - 1) => ∑ i, f (Y i))
            (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ≤
          ENNReal.ofReal (C * ((N - 1 : ℕ) : ℝ)) *
            ∫⁻ y, ‖f y‖ₑ ^ 2 *
              ENNReal.ofReal (Real.exp (-(t * (β / N)) * periodicRiesz d s (x - y)))
              ∂(withDensityReal ρ)) ∧
      (firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ≪
          withDensityReal ρ ∧
        ∀ᵐ y ∂(withDensityReal ρ),
          (firstMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)).rnDeriv
              (withDensityReal ρ) y ≤
            ENNReal.ofReal (C * Real.exp (-(t * (β / N)) * periodicRiesz d s (x - y)))) ∧
      (∀ i j : Fin (N - 1), i ≠ j →
        twoMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) i j ≪
            (withDensityReal ρ).prod (withDensityReal ρ) ∧
          ∀ᵐ p ∂((withDensityReal ρ).prod (withDensityReal ρ)),
            (twoMarginal (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t)
                i j).rnDeriv ((withDensityReal ρ).prod (withDensityReal ρ)) p ≤
              ENNReal.ofReal (C * Real.exp (-(t * (β / N)) *
                (periodicRiesz d s (x - p.1) + periodicRiesz d s (x - p.2))))) := by
  obtain ⟨C1, hC1, h1⟩ := PoleCavityAux.pole_density_clauses hd hs0 hsd β hβ ρ hρ
  obtain ⟨C2, hC2, h2⟩ := PoleCavityAux.pole_variance_clause hd hs0 hsd β hβ ρ hρ
  refine ⟨max C1 C2, lt_max_of_lt_left hC1, fun N hN x t ht => ⟨?_, ?_, ?_⟩⟩
  · intro f hf
    refine (h2 N hN x t ht f hf).trans ?_
    gcongr
    exact le_max_right _ _
  · obtain ⟨hac, hle⟩ := (h1 N hN x t ht).1
    refine ⟨hac, hle.mono fun y hy => hy.trans ?_⟩
    gcongr
    exact le_max_left _ _
  · intro i j hij
    obtain ⟨hac, hle⟩ := (h1 N hN x t ht).2 i j hij
    refine ⟨hac, hle.mono fun y hy => hy.trans ?_⟩
    gcongr
    exact le_max_left _ _

end HRS

end
