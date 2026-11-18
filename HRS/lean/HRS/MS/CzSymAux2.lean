import HRS.MS.CzSymAux1
import HRS.Commutator.Whole.LocalAuxKR

/-!
# SYM-LIN, part 2 (Gaussian side)
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap

noncomputable section

namespace HRS.CZ.Sym

open HRS.Commutator.Whole

variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- the Fourier transform `𝓕[e^{-t|·|²}](ξ) = (π/t)^{d/2} e^{-π²|ξ|²/t}` of the Gaussian, as a function -/
def symlin_E (d : ℕ) (t : ℝ) (ξ : EuclideanSpace ℝ (Fin d)) : ℂ :=
  (((Real.pi / t) ^ ((d : ℝ) / 2) * Real.exp (-(Real.pi ^ 2 * ‖ξ‖ ^ 2 / t)) : ℝ) : ℂ)

lemma symlin_E_eq {t : ℝ} (ht : 0 < t) :
    𝓕 (fun v : 𝔼 => ((Real.exp (-(t * ‖v‖ ^ 2)) : ℝ) : ℂ)) = symlin_E d t := by
  funext ξ
  rw [gauss_fourier_real ht ξ]
  simp [symlin_E]

lemma symlin_E_differentiable (t : ℝ) : Differentiable ℝ (symlin_E d t) := by
  have hn : Differentiable ℝ (fun ξ : 𝔼 => ‖ξ‖ ^ 2) := fun ξ =>
    (hasStrictFDerivAt_norm_sq ξ).hasFDerivAt.differentiableAt
  have h00 : Differentiable ℝ (fun ξ : 𝔼 => Real.pi ^ 2 * ‖ξ‖ ^ 2) := hn.const_mul (Real.pi ^ 2)
  have h01 : Differentiable ℝ (fun ξ : 𝔼 => Real.pi ^ 2 * ‖ξ‖ ^ 2 / t) := by
    simpa only [div_eq_mul_inv] using h00.mul_const t⁻¹
  have h0 : Differentiable ℝ (fun ξ : 𝔼 => -(Real.pi ^ 2 * ‖ξ‖ ^ 2 / t)) := h01.fun_neg
  have h1 : Differentiable ℝ (fun ξ : 𝔼 => Real.exp (-(Real.pi ^ 2 * ‖ξ‖ ^ 2 / t))) :=
    Real.differentiable_exp.comp h0
  have h : Differentiable ℝ (fun ξ : 𝔼 => (((Real.pi / t) ^ ((d : ℝ) / 2) *
      Real.exp (-(Real.pi ^ 2 * ‖ξ‖ ^ 2 / t)) : ℝ))) := h1.const_mul _
  exact Complex.ofRealCLM.differentiable.comp h

lemma symlin_E_fderiv_apply {t : ℝ} (ξ : 𝔼) (i : Fin d) :
    fderiv ℝ (symlin_E d t) ξ (EuclideanSpace.single i (1 : ℝ)) =
      ((-(2 * Real.pi ^ 2 / t * ξ i) : ℝ) : ℂ) * symlin_E d t ξ := by
  have h1 : HasFDerivAt (fun ξ : 𝔼 => ‖ξ‖ ^ 2) ((2 : ℕ) • innerSL ℝ ξ) ξ :=
    (hasStrictFDerivAt_norm_sq ξ).hasFDerivAt
  have h2 := ((h1.const_mul (Real.pi ^ 2 / t)).neg).exp
  have h3 := h2.const_mul ((Real.pi / t) ^ ((d : ℝ) / 2))
  have h4 := Complex.ofRealCLM.hasFDerivAt.comp ξ h3
  have e : symlin_E d t = ⇑Complex.ofRealCLM ∘ fun y : 𝔼 => (Real.pi / t) ^ ((d : ℝ) / 2) *
      Real.exp ((-fun y : 𝔼 => Real.pi ^ 2 / t * ‖y‖ ^ 2) y) := by
    funext ξ
    simp only [symlin_E, Function.comp_apply, Pi.neg_apply]
    congr 3
    ring
  rw [e, h4.fderiv]
  simp [EuclideanSpace.inner_single_right]
  ring

lemma symlin_E_norm_le {t : ℝ} (ht : 0 < t) (ξ : 𝔼) :
    ‖symlin_E d t ξ‖ ≤ (Real.pi / t) ^ ((d : ℝ) / 2) := by
  unfold symlin_E
  rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have : Real.exp (-(Real.pi ^ 2 * ‖ξ‖ ^ 2 / t)) ≤ 1 :=
    Real.exp_le_one_iff.2 (by
      have : 0 ≤ Real.pi ^ 2 * ‖ξ‖ ^ 2 / t := by positivity
      linarith)
  calc (Real.pi / t) ^ ((d : ℝ) / 2) * Real.exp (-(Real.pi ^ 2 * ‖ξ‖ ^ 2 / t))
      ≤ (Real.pi / t) ^ ((d : ℝ) / 2) * 1 := by gcongr
    _ = _ := mul_one _

lemma symlin_E_continuous (t : ℝ) : Continuous (symlin_E d t) :=
  (symlin_E_differentiable t).continuous

/-- `‖ξ‖ e^{-a‖ξ‖²}` is bounded -/
lemma symlin_norm_gauss_bdd {a : ℝ} (ha : 0 < a) (ξ : 𝔼) :
    ‖ξ‖ * Real.exp (-(a * ‖ξ‖ ^ 2)) ≤ 1 + 1 / a := by
  have h1 : ‖ξ‖ ≤ 1 + ‖ξ‖ ^ 2 := by nlinarith [norm_nonneg ξ, sq_nonneg (‖ξ‖ - 1)]
  have h2 : Real.exp (-(a * ‖ξ‖ ^ 2)) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖ξ‖])
  have h3 : a * ‖ξ‖ ^ 2 * Real.exp (-(a * ‖ξ‖ ^ 2)) ≤ 1 := by
    have h := Real.add_one_le_exp (a * ‖ξ‖ ^ 2)
    have h4 : 0 < Real.exp (-(a * ‖ξ‖ ^ 2)) := Real.exp_pos _
    have h5 : Real.exp (a * ‖ξ‖ ^ 2) * Real.exp (-(a * ‖ξ‖ ^ 2)) = 1 := by
      rw [← Real.exp_add]; simp
    nlinarith
  have h6 : ‖ξ‖ ^ 2 * Real.exp (-(a * ‖ξ‖ ^ 2)) ≤ 1 / a := by
    rw [le_div_iff₀ ha]; nlinarith
  calc ‖ξ‖ * Real.exp (-(a * ‖ξ‖ ^ 2)) ≤ (1 + ‖ξ‖ ^ 2) * Real.exp (-(a * ‖ξ‖ ^ 2)) := by
        gcongr
    _ = Real.exp (-(a * ‖ξ‖ ^ 2)) + ‖ξ‖ ^ 2 * Real.exp (-(a * ‖ξ‖ ^ 2)) := by ring
    _ ≤ 1 + 1 / a := add_le_add h2 h6

lemma symlin_integrable_fderiv (G : 𝓢(𝔼, ℂ)) (i : Fin d) :
    Integrable (fun ξ : 𝔼 => fderiv ℝ G ξ (EuclideanSpace.single i (1 : ℝ))) := by
  have := SchwartzMap.integrable (μ := (volume : Measure 𝔼))
    (LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ)) G : SchwartzMap 𝔼 ℂ)
  have hL : (⇑(LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ)) G) : 𝔼 → ℂ) =
      fun ξ => fderiv ℝ G ξ (EuclideanSpace.single i (1 : ℝ)) :=
    funext (SchwartzMap.lineDerivOp_apply_eq_fderiv (EuclideanSpace.single i (1 : ℝ)) G)
  rwa [hL] at this

/-- integration by parts of the Gaussian transform against a Schwartz function -/
lemma symlin_E_ibp {t : ℝ} (ht : 0 < t) (G : 𝓢(𝔼, ℂ)) (i : Fin d) :
    ∫ ξ : 𝔼, symlin_E d t ξ * fderiv ℝ G ξ (EuclideanSpace.single i (1 : ℝ)) =
      -∫ ξ : 𝔼, (((-(2 * Real.pi ^ 2 / t * ξ i) : ℝ) : ℂ) * symlin_E d t ξ) * G ξ := by
  have hcE := symlin_E_continuous (d := d) t
  have hGi : Integrable (fun ξ : 𝔼 => G ξ) := G.integrable
  have hdG := symlin_integrable_fderiv G i
  have hbd : ∀ ξ : 𝔼, ‖symlin_E d t ξ‖ ≤ (Real.pi / t) ^ ((d : ℝ) / 2) := symlin_E_norm_le ht
  have h1 : Integrable (fun ξ : 𝔼 => fderiv ℝ (symlin_E d t) ξ (EuclideanSpace.single i (1 : ℝ)) * G ξ) := by
    have hfun : (fun ξ : 𝔼 => fderiv ℝ (symlin_E d t) ξ (EuclideanSpace.single i (1 : ℝ)) * G ξ) =
        fun ξ : 𝔼 => (((-(2 * Real.pi ^ 2 / t * ξ i) : ℝ) : ℂ) * symlin_E d t ξ) * G ξ := by
      funext ξ; rw [symlin_E_fderiv_apply]
    rw [hfun]
    have ha : 0 < Real.pi ^ 2 / t := by positivity
    refine Integrable.mono' (g := fun ξ : 𝔼 => (2 * Real.pi ^ 2 / t) * ((Real.pi / t) ^ ((d : ℝ) / 2) *
      (1 + 1 / (Real.pi ^ 2 / t))) * ‖G ξ‖) (hGi.norm.const_mul _) ?_ (Eventually.of_forall fun ξ => ?_)
    · refine Continuous.aestronglyMeasurable ?_
      have : Continuous (fun ξ : 𝔼 => ξ i) := (EuclideanSpace.proj i : 𝔼 →L[ℝ] ℝ).continuous
      exact ((Complex.continuous_ofReal.comp (by fun_prop)).mul hcE).mul G.continuous
    · rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_neg, abs_mul]
      have hxi : |ξ i| ≤ ‖ξ‖ := by simpa using PiLp.norm_apply_le ξ i
      have hE : ‖symlin_E d t ξ‖ = (Real.pi / t) ^ ((d : ℝ) / 2) * Real.exp (-(Real.pi ^ 2 / t * ‖ξ‖ ^ 2)) := by
        unfold symlin_E
        rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
        congr 3; ring
      have hb := symlin_norm_gauss_bdd ha ξ
      have : |2 * Real.pi ^ 2 / t| = 2 * Real.pi ^ 2 / t := abs_of_pos (by positivity)
      rw [this, hE]
      have hc : 0 ≤ (Real.pi / t) ^ ((d : ℝ) / 2) := by positivity
      calc 2 * Real.pi ^ 2 / t * |ξ i| * ((Real.pi / t) ^ ((d : ℝ) / 2) * Real.exp (-(Real.pi ^ 2 / t * ‖ξ‖ ^ 2))) * ‖G ξ‖
          ≤ 2 * Real.pi ^ 2 / t * ‖ξ‖ * ((Real.pi / t) ^ ((d : ℝ) / 2) * Real.exp (-(Real.pi ^ 2 / t * ‖ξ‖ ^ 2))) * ‖G ξ‖ := by
            gcongr
        _ = (2 * Real.pi ^ 2 / t) * ((Real.pi / t) ^ ((d : ℝ) / 2) * (‖ξ‖ * Real.exp (-(Real.pi ^ 2 / t * ‖ξ‖ ^ 2)))) * ‖G ξ‖ := by ring
        _ ≤ (2 * Real.pi ^ 2 / t) * ((Real.pi / t) ^ ((d : ℝ) / 2) * (1 + 1 / (Real.pi ^ 2 / t))) * ‖G ξ‖ := by
            gcongr
  have h2 : Integrable (fun ξ : 𝔼 => symlin_E d t ξ * fderiv ℝ G ξ (EuclideanSpace.single i (1 : ℝ))) := by
    refine Integrable.mono' (g := fun ξ : 𝔼 => (Real.pi / t) ^ ((d : ℝ) / 2) *
      ‖fderiv ℝ G ξ (EuclideanSpace.single i (1 : ℝ))‖) (hdG.norm.const_mul _) ?_
      (Eventually.of_forall fun ξ => ?_)
    · exact (hcE.aestronglyMeasurable).mul hdG.aestronglyMeasurable
    · rw [norm_mul]
      gcongr
      exact hbd ξ
  have h3 : Integrable (fun ξ : 𝔼 => symlin_E d t ξ * G ξ) := by
    refine Integrable.mono' (g := fun ξ : 𝔼 => (Real.pi / t) ^ ((d : ℝ) / 2) * ‖G ξ‖)
      (hGi.norm.const_mul _) ?_ (Eventually.of_forall fun ξ => ?_)
    · exact hcE.aestronglyMeasurable.mul G.continuous.aestronglyMeasurable
    · rw [norm_mul]
      gcongr
      exact hbd ξ
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure 𝔼))
    (f := symlin_E d t) (g := ⇑G) (v := EuclideanSpace.single i (1 : ℝ)) h1 h2 h3
    (fun x _ => (symlin_E_differentiable t) x) (fun x _ => G.differentiableAt)
  rw [key]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  rw [symlin_E_fderiv_apply]

/-- pairing of the odd Gaussian `z_i e^{-t|z|²}` with `𝓕 G`: `∫ z_i e^{-t|z|²} 𝓕G(z) dz
= -(iπ/t) ∫ ξ_i (π/t)^{d/2} e^{-π²|ξ|²/t} G(ξ) dξ` -/
lemma symlin_odd_gauss_pair {t : ℝ} (ht : 0 < t) (G : 𝓢(𝔼, ℂ)) (i : Fin d) :
    ∫ z : 𝔼, ((z i * Real.exp (-(t * ‖z‖ ^ 2)) : ℝ) : ℂ) * 𝓕 (⇑G) z =
      ∫ ξ : 𝔼, (-(Complex.I * ((Real.pi / t : ℝ) : ℂ)) * ((ξ i : ℝ) : ℂ)) *
        symlin_E d t ξ * G ξ := by
  set D : 𝔼 → ℂ := fun ξ => fderiv ℝ G ξ (EuclideanSpace.single i (1 : ℝ)) with hD
  set g : 𝔼 → ℂ := fun v => ((Real.exp (-(t * ‖v‖ ^ 2)) : ℝ) : ℂ) with hg
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  have hI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    have := Complex.I_ne_zero
    simp [Real.pi_ne_zero]
  have h1 : ∀ z : 𝔼, ((z i * Real.exp (-(t * ‖z‖ ^ 2)) : ℝ) : ℂ) * 𝓕 (⇑G) z =
      (1 / (2 * (Real.pi : ℂ) * Complex.I)) * (g z * 𝓕 D z) := by
    intro z
    have hF := cmxMY_fourier_partial G i z
    rw [← hD] at hF
    rw [hF, hg]
    simp only
    push_cast
    field_simp
  simp_rw [h1]
  rw [integral_const_mul, integral_mul_fourier_eq g D (integrable_gauss_real ht)
    (symlin_integrable_fderiv G i)]
  have hFg : 𝓕 g = symlin_E d t := symlin_E_eq ht
  rw [hFg, hD, symlin_E_ibp ht G i, ← integral_neg, ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  simp only
  push_cast
  field_simp
  simp only [Complex.I_sq]
  ring

/-- `‖ξ‖^s ‖G ξ‖` is integrable for `-d < s ≤ k` -/
lemma symlin_integrable_rpow_mul (hd : 1 ≤ d) {s : ℝ} (hs : -(d : ℝ) < s) (k : ℕ) (hk : s ≤ k)
    (G : 𝓢(𝔼, ℂ)) : Integrable (fun ξ : 𝔼 => ‖ξ‖ ^ s * ‖G ξ‖) := by
  have hloc : IntegrableOn (fun x : 𝔼 => ‖x‖ ^ s) (ball 0 1) := by
    refine integrableOn_ball_of_norm_le_rpow (μ := volume) (f := fun x : 𝔼 => ‖x‖ ^ s)
      (C := 1) (α := -s) (r := 1) (by rw [finrank_euclideanSpace_fin]; exact hd) ?_ ?_ ?_
    · rw [finrank_euclideanSpace_fin]; linarith
    · exact Eventually.of_forall fun x => by
        rw [neg_neg, one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x) s)]
    · exact ((measurable_norm.pow_const s)).aestronglyMeasurable
  have hind : Integrable (Set.indicator (ball (0 : 𝔼) 1) fun x : 𝔼 => ‖x‖ ^ s) :=
    (integrable_indicator_iff measurableSet_ball).2 hloc
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x : 𝔼, ‖G x‖ ≤ M :=
    ⟨(SchwartzMap.seminorm ℝ 0 0 G : ℝ), fun x => SchwartzMap.norm_le_seminorm ℝ G x⟩
  refine Integrable.mono' ((hind.const_mul M).add (SchwartzMap.integrable_pow_mul volume G k))
    ?_ (Eventually.of_forall fun x => ?_)
  · exact ((measurable_norm.pow_const s).mul G.continuous.norm.measurable).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg x) s) (norm_nonneg _))]
    have h2 : 0 ≤ ‖x‖ ^ s := Real.rpow_nonneg (norm_nonneg x) s
    have h3 : 0 ≤ ‖G x‖ := norm_nonneg _
    have h5 : 0 ≤ ‖x‖ ^ k * ‖G x‖ := by positivity
    by_cases hx : x ∈ ball (0 : 𝔼) 1
    · have hind_x : (Set.indicator (ball (0 : 𝔼) 1) fun y : 𝔼 => ‖y‖ ^ s) x = ‖x‖ ^ s :=
        Set.indicator_of_mem hx _
      have h4 : ‖x‖ ^ s * ‖G x‖ ≤ ‖x‖ ^ s * M := mul_le_mul_of_nonneg_left (hM x) h2
      show ‖x‖ ^ s * ‖G x‖ ≤ M * (Set.indicator (ball (0 : 𝔼) 1) fun y : 𝔼 => ‖y‖ ^ s) x + ‖x‖ ^ k * ‖G x‖
      rw [hind_x]
      linarith [mul_comm M (‖x‖ ^ s)]
    · have hind_x : (Set.indicator (ball (0 : 𝔼) 1) fun y : 𝔼 => ‖y‖ ^ s) x = 0 :=
        Set.indicator_of_notMem hx _
      have hx1 : 1 ≤ ‖x‖ := by
        simp only [mem_ball, dist_zero_right, not_lt] at hx
        exact hx
      have h4 : ‖x‖ ^ s ≤ ‖x‖ ^ k := by
        rw [← Real.rpow_natCast]
        exact Real.rpow_le_rpow_of_exponent_le hx1 hk
      show ‖x‖ ^ s * ‖G x‖ ≤ M * (Set.indicator (ball (0 : 𝔼) 1) fun y : 𝔼 => ‖y‖ ^ s) x + ‖x‖ ^ k * ‖G x‖
      rw [hind_x, mul_zero, zero_add]
      exact mul_le_mul_of_nonneg_right h4 h3

/-- inner `t`-integral of the subordinated odd kernel, in `ℝ≥0∞` -/
lemma symlin_inner_lintegral {γ : ℝ} (hγ : 0 < γ) (i : Fin d) (z : 𝔼) (c : ℂ) :
    ∫⁻ t in Ioi (0 : ℝ), ‖((t ^ (γ / 2 - 1) * (z i * Real.exp (-(t * ‖z‖ ^ 2))) : ℝ) : ℂ) * c‖ₑ =
      ENNReal.ofReal (Real.Gamma (γ / 2) * (|z i| * ‖z‖ ^ (-γ)) * ‖c‖) := by
  by_cases hz : z = 0
  · subst hz
    simp
  · have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hr : 0 < ‖z‖ ^ 2 := by positivity
    have hpt : ∀ t ∈ Ioi (0 : ℝ), ‖((t ^ (γ / 2 - 1) * (z i * Real.exp (-(t * ‖z‖ ^ 2))) : ℝ) : ℂ) * c‖ₑ =
        ENNReal.ofReal ((t ^ (γ / 2 - 1) * Real.exp (-(t * ‖z‖ ^ 2))) * (|z i| * ‖c‖)) := by
      intro t ht
      have ht' : (0 : ℝ) < t := ht
      rw [← ofReal_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg (Real.rpow_nonneg ht'.le _), abs_of_pos (Real.exp_pos _)]
      congr 1
      ring
    rw [setLIntegral_congr_fun measurableSet_Ioi hpt]
    have hint : IntegrableOn (fun t : ℝ => (t ^ (γ / 2 - 1) * Real.exp (-(t * ‖z‖ ^ 2))) * (|z i| * ‖c‖))
        (Ioi 0) := (integrableOn_gamma_kernel' (by linarith) hr).mul_const _
    have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
        (fun t : ℝ => (t ^ (γ / 2 - 1) * Real.exp (-(t * ‖z‖ ^ 2))) * (|z i| * ‖c‖)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht' : (0 : ℝ) < t := ht
      exact mul_nonneg (mul_nonneg (Real.rpow_nonneg ht'.le _) (Real.exp_pos _).le)
        (mul_nonneg (abs_nonneg _) (norm_nonneg _))
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_mul_const,
      integral_gauss_subordination hγ z hz]
    congr 1
    ring

lemma symlin_odd_gauss_integral {γ : ℝ} (hγ : 0 < γ) (i : Fin d) (z : 𝔼) (c : ℂ) :
    ∫ t in Ioi (0 : ℝ), ((t ^ (γ / 2 - 1) * (z i * Real.exp (-(t * ‖z‖ ^ 2))) : ℝ) : ℂ) * c =
      (((Real.Gamma (γ / 2) * (z i * ‖z‖ ^ (-γ)) : ℝ)) : ℂ) * c := by
  by_cases hz : z = 0
  · subst hz
    simp
  · have h1 : ∀ t : ℝ, ((t ^ (γ / 2 - 1) * (z i * Real.exp (-(t * ‖z‖ ^ 2))) : ℝ) : ℂ) * c =
        ((z i : ℝ) : ℂ) * (((t ^ (γ / 2 - 1) * Real.exp (-(t * ‖z‖ ^ 2)) : ℝ) : ℂ) * c) := by
      intro t; push_cast; ring
    simp_rw [h1]
    rw [integral_const_mul, integral_mul_const, integral_complex_ofReal,
      integral_gauss_subordination hγ z hz]
    push_cast
    ring

/-- the symmetrised difference of a Schwartz function is `O(|z|)` and integrable against `K` -/
lemma symlin_integrable_KH (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) (i : Fin d)
    (W : 𝓢(𝔼, ℂ)) :
    Integrable (fun z : 𝔼 => ((symlin_K d θ i z : ℝ) : ℂ) * ((W z - W (-z)) / 2)) := by
  obtain ⟨M, hM0, hM⟩ := symlin_schwartz_lip W
  have hc : Continuous (fun z : 𝔼 => (W z - W (-z)) / 2) :=
    ((W.continuous.sub (W.continuous.comp continuous_neg))).div_const 2
  have hi : Integrable (fun z : 𝔼 => (W z - W (-z)) / 2) :=
    ((W.integrable.sub (W.integrable.comp_neg))).div_const 2
  have hb : ∀ z : 𝔼, ‖(W z - W (-z)) / 2‖ ≤ M * ‖z‖ := by
    intro z
    have h1 := hM z (-z)
    have h2 : ‖z - -z‖ = 2 * ‖z‖ := by
      have : z - -z = (2 : ℝ) • z := by rw [two_smul]; abel
      rw [this, norm_smul]; simp
    rw [h2] at h1
    rw [norm_div, show ‖(2 : ℂ)‖ = 2 by simp]
    linarith
  have h := symlin_integrable_K_smul hd hθ0 hθ2 i hc.aestronglyMeasurable hi hM0 hb
  refine h.congr (Eventually.of_forall fun z => ?_)
  simp [Complex.real_smul]

lemma symlin_integrable_fub1 (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) (i : Fin d)
    (W : 𝓢(𝔼, ℂ)) :
    Integrable (Function.uncurry fun (z : 𝔼) (t : ℝ) =>
      ((t ^ (((d : ℝ) + θ) / 2 - 1) * (z i * Real.exp (-(t * ‖z‖ ^ 2))) : ℝ) : ℂ) *
        ((W z - W (-z)) / 2))
      ((volume : Measure 𝔼).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hγ : 0 < (d : ℝ) + θ := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hHc : Continuous (fun z : 𝔼 => (W z - W (-z)) / 2) :=
    ((W.continuous.sub (W.continuous.comp continuous_neg))).div_const 2
  have hmeas : AEStronglyMeasurable (Function.uncurry fun (z : 𝔼) (t : ℝ) =>
      ((t ^ (((d : ℝ) + θ) / 2 - 1) * (z i * Real.exp (-(t * ‖z‖ ^ 2))) : ℝ) : ℂ) *
        ((W z - W (-z)) / 2))
      ((volume : Measure 𝔼).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    apply Measurable.aestronglyMeasurable
    refine Measurable.mul ?_ ?_
    · refine Complex.measurable_ofReal.comp (Measurable.mul ?_ (Measurable.mul ?_ ?_))
      · exact measurable_snd.pow_const _
      · exact ((EuclideanSpace.proj i : 𝔼 →L[ℝ] ℝ).continuous.measurable).comp measurable_fst
      · exact Real.continuous_exp.measurable.comp
          ((measurable_snd.mul (measurable_fst.norm.pow_const 2)).neg)
    · exact hHc.measurable.comp measurable_fst
  refine ⟨hmeas, ?_⟩
  unfold HasFiniteIntegral
  rw [lintegral_prod _ hmeas.enorm]
  have hinner : ∀ z : 𝔼, ∫⁻ t in Ioi (0 : ℝ), ‖((t ^ (((d : ℝ) + θ) / 2 - 1) *
      (z i * Real.exp (-(t * ‖z‖ ^ 2))) : ℝ) : ℂ) * ((W z - W (-z)) / 2)‖ₑ =
      ENNReal.ofReal (Real.Gamma (((d : ℝ) + θ) / 2)) *
        ENNReal.ofReal (‖((symlin_K d θ i z : ℝ) : ℂ) * ((W z - W (-z)) / 2)‖) := by
    intro z
    rw [symlin_inner_lintegral hγ i z, ← ENNReal.ofReal_mul (Real.Gamma_pos_of_pos (by linarith)).le]
    congr 1
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have : |symlin_K d θ i z| = |z i| * ‖z‖ ^ (-((d : ℝ) + θ)) := by
      rw [symlin_K, abs_div, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
        Real.rpow_neg (norm_nonneg _), div_eq_mul_inv]
    rw [this]
    ring
  refine lt_of_eq_of_lt (lintegral_congr hinner) ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  have h := (symlin_integrable_KH hd hθ0 hθ2 i W).hasFiniteIntegral
  unfold HasFiniteIntegral at h
  refine lt_of_le_of_lt (le_of_eq ?_) h
  apply lintegral_congr
  intro z
  rw [← ofReal_norm]

/-- the constant `C₀ = π^{d/2+θ-1} Γ(1-θ/2) / Γ((d+θ)/2)` -/
def symlin_C0 (d : ℕ) (θ : ℝ) : ℝ :=
  Real.pi ^ ((d : ℝ) / 2 + θ - 1) * Real.Gamma (1 - θ / 2) / Real.Gamma (((d : ℝ) + θ) / 2)

/-- the symbol `m₀(ξ) = -i C₀ ξ_i |ξ|^{θ-2}` -/
def symlin_m0 (d : ℕ) (θ : ℝ) (i : Fin d) (ξ : EuclideanSpace ℝ (Fin d)) : ℂ :=
  -(Complex.I * ((symlin_C0 d θ : ℝ) : ℂ)) * ((ξ i : ℝ) : ℂ) * ((‖ξ‖ ^ (θ - 2) : ℝ) : ℂ)

lemma symlin_kernel_pt {θ : ℝ} {t : ℝ} (ht : 0 < t) :
    t ^ (((d : ℝ) + θ) / 2 - 1) * (Real.pi / t) * (Real.pi / t) ^ ((d : ℝ) / 2) =
      Real.pi ^ (1 + (d : ℝ) / 2) * t ^ (-(1 - θ / 2) - 1) := by
  rw [Real.div_rpow Real.pi_pos.le ht.le, Real.rpow_add Real.pi_pos, Real.rpow_one]
  have e : t ^ (-(1 - θ / 2) - 1) = t ^ (((d : ℝ) + θ) / 2 - 1) / t / t ^ ((d : ℝ) / 2) := by
    have h1 : -(1 - θ / 2) - 1 = (((d : ℝ) + θ) / 2 - 1 - 1) - (d : ℝ) / 2 := by ring
    rw [h1, Real.rpow_sub ht, Real.rpow_sub ht, Real.rpow_one]
  rw [e]
  have : t ^ ((d : ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos ht _).ne'
  field_simp

lemma symlin_const_identity {θ : ℝ} (hθ2 : θ < 2) (ξ : 𝔼) :
    Real.pi ^ (1 + (d : ℝ) / 2) * (Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-(1 - θ / 2)) =
      Real.pi ^ ((d : ℝ) / 2 + θ - 1) * ‖ξ‖ ^ (θ - 2) := by
  have hπ : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have hn : (0 : ℝ) ≤ ‖ξ‖ := norm_nonneg ξ
  rw [Real.mul_rpow (by positivity) (by positivity)]
  have h1 : (Real.pi ^ 2 : ℝ) ^ (-(1 - θ / 2)) = Real.pi ^ (-(2 - θ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hπ]
    congr 1
    push_cast
    ring
  have h2 : (‖ξ‖ ^ 2) ^ (-(1 - θ / 2)) = ‖ξ‖ ^ (θ - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn]
    congr 1
    push_cast
    ring
  rw [h1, h2]
  have h3 : Real.pi ^ (1 + (d : ℝ) / 2) * Real.pi ^ (-(2 - θ)) = Real.pi ^ ((d : ℝ) / 2 + θ - 1) := by
    rw [← Real.rpow_add Real.pi_pos]
    congr 1
    ring
  rw [← mul_assoc, h3]

/-- the integrand of the second Fubini exchange -/
def symlin_F3 (d : ℕ) (θ : ℝ) (i : Fin d) (G : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)) (t : ℝ)
    (ξ : EuclideanSpace ℝ (Fin d)) : ℂ :=
  ((t ^ (((d : ℝ) + θ) / 2 - 1) : ℝ) : ℂ) *
    ((-(Complex.I * ((Real.pi / t : ℝ) : ℂ)) * ((ξ i : ℝ) : ℂ)) * symlin_E d t ξ * G ξ)

lemma symlin_F3_eq {θ : ℝ} (i : Fin d) (G : 𝓢(𝔼, ℂ)) {t : ℝ} (ht : 0 < t) (ξ : 𝔼) :
    symlin_F3 d θ i G t ξ = (-(Complex.I * (ξ i : ℂ) * G ξ)) *
      (((Real.pi ^ (1 + (d : ℝ) / 2) * (t ^ (-(1 - θ / 2) - 1) *
        Real.exp (-(Real.pi ^ 2 * ‖ξ‖ ^ 2 / t))) : ℝ) : ℂ)) := by
  have hk := symlin_kernel_pt (d := d) (θ := θ) ht
  have key : t ^ (((d : ℝ) + θ) / 2 - 1) * (Real.pi / t) * (ξ i) *
      ((Real.pi / t) ^ ((d : ℝ) / 2) * Real.exp (-(Real.pi ^ 2 * ‖ξ‖ ^ 2 / t))) =
      Real.pi ^ (1 + (d : ℝ) / 2) * (t ^ (-(1 - θ / 2) - 1) *
        Real.exp (-(Real.pi ^ 2 * ‖ξ‖ ^ 2 / t))) * ξ i := by
    calc _ = (t ^ (((d : ℝ) + θ) / 2 - 1) * (Real.pi / t) * (Real.pi / t) ^ ((d : ℝ) / 2)) *
          Real.exp (-(Real.pi ^ 2 * ‖ξ‖ ^ 2 / t)) * ξ i := by ring
      _ = _ := by rw [hk]; ring
  have key' : ((t ^ (((d : ℝ) + θ) / 2 - 1) * (Real.pi / t) * (ξ i) *
      ((Real.pi / t) ^ ((d : ℝ) / 2) * Real.exp (-(Real.pi ^ 2 * ‖ξ‖ ^ 2 / t))) : ℝ) : ℂ) =
      ((Real.pi ^ (1 + (d : ℝ) / 2) * (t ^ (-(1 - θ / 2) - 1) *
        Real.exp (-(Real.pi ^ 2 * ‖ξ‖ ^ 2 / t))) * ξ i : ℝ) : ℂ) := by rw [key]
  simp only [symlin_F3, symlin_E]
  calc _ = (-(Complex.I * G ξ)) * ((t ^ (((d : ℝ) + θ) / 2 - 1) * (Real.pi / t) * (ξ i) *
      ((Real.pi / t) ^ ((d : ℝ) / 2) * Real.exp (-(Real.pi ^ 2 * ‖ξ‖ ^ 2 / t))) : ℝ) : ℂ) := by
        simp only [Complex.ofReal_mul]; ring
    _ = _ := by
        rw [key']; simp only [Complex.ofReal_mul]; ring

/-- the `t`-integral of the transformed kernel: for every `ξ` -/
lemma symlin_t_integral {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) (i : Fin d) (G : 𝓢(𝔼, ℂ)) (ξ : 𝔼) :
    ∫ t in Ioi (0 : ℝ), symlin_F3 d θ i G t ξ =
      ((Real.Gamma (((d : ℝ) + θ) / 2) : ℝ) : ℂ) * symlin_m0 d θ i ξ * G ξ := by
  have hβ : 0 < 1 - θ / 2 := by linarith
  have hγ : 0 < Real.Gamma (((d : ℝ) + θ) / 2) := Real.Gamma_pos_of_pos (by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith)
  by_cases hξ : ξ = 0
  · subst hξ
    simp [symlin_m0, symlin_F3]
  · have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    have hc : 0 < Real.pi ^ 2 * ‖ξ‖ ^ 2 := by positivity
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => symlin_F3_eq i G (show (0 : ℝ) < t from ht) ξ),
      integral_const_mul, integral_complex_ofReal,
      integral_const_mul, (integrableOn_and_integral_inv_kernel hβ hc).2]
    have E1 : Real.pi ^ (1 + (d : ℝ) / 2) * ((Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-(1 - θ / 2)) *
        Real.Gamma (1 - θ / 2)) = Real.Gamma (((d : ℝ) + θ) / 2) * symlin_C0 d θ * ‖ξ‖ ^ (θ - 2) := by
      rw [← mul_assoc, symlin_const_identity hθ2 ξ, symlin_C0]
      field_simp
    rw [E1]
    simp only [symlin_m0, Complex.ofReal_mul]
    ring

lemma symlin_F3_lintegral {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) (i : Fin d) (G : 𝓢(𝔼, ℂ)) (ξ : 𝔼) :
    ∫⁻ t in Ioi (0 : ℝ), ‖symlin_F3 d θ i G t ξ‖ₑ =
      ENNReal.ofReal (Real.pi ^ ((d : ℝ) / 2 + θ - 1) * Real.Gamma (1 - θ / 2) *
        (‖ξ‖ ^ (θ - 2) * |ξ i| * ‖G ξ‖)) := by
  have hβ : 0 < 1 - θ / 2 := by linarith
  by_cases hξ : ξ = 0
  · subst hξ
    simp [symlin_F3]
  · have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    have hc : 0 < Real.pi ^ 2 * ‖ξ‖ ^ 2 := by positivity
    have hpt : ∀ t ∈ Ioi (0 : ℝ), ‖symlin_F3 d θ i G t ξ‖ₑ = ENNReal.ofReal
        ((Real.pi ^ (1 + (d : ℝ) / 2) * (t ^ (-(1 - θ / 2) - 1) *
          Real.exp (-(Real.pi ^ 2 * ‖ξ‖ ^ 2 / t)))) * (|ξ i| * ‖G ξ‖)) := by
      intro t ht
      have ht' : (0 : ℝ) < t := ht
      rw [symlin_F3_eq i G ht' ξ, ← ofReal_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity), norm_neg, norm_mul, norm_mul, Complex.norm_I,
        Complex.norm_real, Real.norm_eq_abs]
      congr 1
      ring
    rw [setLIntegral_congr_fun measurableSet_Ioi hpt]
    have hint : IntegrableOn (fun t : ℝ => (Real.pi ^ (1 + (d : ℝ) / 2) * (t ^ (-(1 - θ / 2) - 1) *
        Real.exp (-(Real.pi ^ 2 * ‖ξ‖ ^ 2 / t)))) * (|ξ i| * ‖G ξ‖)) (Ioi 0) :=
      ((integrableOn_and_integral_inv_kernel hβ hc).1.const_mul _).mul_const _
    have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] (fun t : ℝ =>
        (Real.pi ^ (1 + (d : ℝ) / 2) * (t ^ (-(1 - θ / 2) - 1) *
          Real.exp (-(Real.pi ^ 2 * ‖ξ‖ ^ 2 / t)))) * (|ξ i| * ‖G ξ‖)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht' : (0 : ℝ) < t := ht
      exact mul_nonneg (mul_nonneg (by positivity) (mul_nonneg (Real.rpow_nonneg ht'.le _)
        (Real.exp_pos _).le)) (mul_nonneg (abs_nonneg _) (norm_nonneg _))
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_mul_const, integral_const_mul,
      (integrableOn_and_integral_inv_kernel hβ hc).2]
    congr 1
    rw [← mul_assoc (Real.pi ^ (1 + (d : ℝ) / 2)), symlin_const_identity hθ2 ξ]
    ring

lemma symlin_integrable_fub2 (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) (i : Fin d)
    (G : 𝓢(𝔼, ℂ)) :
    Integrable (Function.uncurry fun (t : ℝ) (ξ : 𝔼) => symlin_F3 d θ i G t ξ)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  have hmeas : AEStronglyMeasurable (Function.uncurry fun (t : ℝ) (ξ : 𝔼) => symlin_F3 d θ i G t ξ)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    apply Measurable.aestronglyMeasurable
    unfold symlin_F3 symlin_E
    refine Measurable.mul ?_ (Measurable.mul (Measurable.mul (Measurable.mul ?_ ?_) ?_) ?_)
    · exact Complex.measurable_ofReal.comp ((measurable_fst).pow_const _)
    · exact (measurable_const.mul (Complex.measurable_ofReal.comp
        ((measurable_const.div measurable_fst)))).neg
    · exact Complex.measurable_ofReal.comp (((EuclideanSpace.proj i : 𝔼 →L[ℝ] ℝ).continuous.measurable).comp measurable_snd)
    · refine Complex.measurable_ofReal.comp (Measurable.mul ?_ ?_)
      · exact (measurable_const.div measurable_fst).pow_const _
      · exact Real.continuous_exp.measurable.comp
          ((measurable_const.mul (measurable_snd.norm.pow_const 2)).div measurable_fst).neg
    · exact G.continuous.measurable.comp measurable_snd
  refine ⟨hmeas, ?_⟩
  unfold HasFiniteIntegral
  rw [lintegral_prod_symm _ hmeas.enorm]
  refine lt_of_eq_of_lt (lintegral_congr (fun ξ => symlin_F3_lintegral hθ0 hθ2 i G ξ)) ?_
  have hs : -(d : ℝ) < θ - 1 := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hI := symlin_integrable_rpow_mul hd hs 1 (by norm_num; linarith) G
  have hI2 : Integrable (fun ξ : 𝔼 => ‖ξ‖ ^ (θ - 2) * |ξ i| * ‖G ξ‖) := by
    refine hI.mono' ?_ (Eventually.of_forall fun ξ => ?_)
    · refine (((measurable_norm.pow_const _).mul ?_).mul G.continuous.norm.measurable).aestronglyMeasurable
      exact ((EuclideanSpace.proj i : 𝔼 →L[ℝ] ℝ).continuous.measurable).abs
    · rw [Real.norm_of_nonneg (by positivity)]
      by_cases hξ : ξ = 0
      · subst hξ
        simp
        exact mul_nonneg (Real.rpow_nonneg le_rfl _) (norm_nonneg _)
      · have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
        have hxi : |ξ i| ≤ ‖ξ‖ := by simpa using PiLp.norm_apply_le ξ i
        calc ‖ξ‖ ^ (θ - 2) * |ξ i| * ‖G ξ‖ ≤ ‖ξ‖ ^ (θ - 2) * ‖ξ‖ * ‖G ξ‖ := by gcongr
          _ = ‖ξ‖ ^ (θ - 1) * ‖G ξ‖ := by
            congr 1
            have : θ - 1 = (θ - 2) + 1 := by ring
            rw [this, Real.rpow_add hn, Real.rpow_one]
  have hfin := (hI2.const_mul (Real.pi ^ ((d : ℝ) / 2 + θ - 1) * Real.Gamma (1 - θ / 2))).hasFiniteIntegral
  unfold HasFiniteIntegral at hfin
  refine lt_of_le_of_lt (le_of_eq ?_) hfin
  apply lintegral_congr
  intro ξ
  have hΓ : 0 ≤ Real.Gamma (1 - θ / 2) := (Real.Gamma_pos_of_pos (by linarith)).le
  rw [← ofReal_norm, Real.norm_of_nonneg (mul_nonneg (mul_nonneg (by positivity) hΓ) (by positivity))]

lemma symlin_odd_trick {f W : 𝔼 → ℂ} (hf : ∀ z, f (-z) = -f z)
    (h1 : Integrable (fun z => f z * W z)) :
    ∫ z, f z * ((W z - W (-z)) / 2) = ∫ z, f z * W z := by
  have h2 : Integrable (fun z => f z * W (-z)) := by
    have := h1.comp_neg
    refine (this.neg).congr (ae_of_all _ fun z => ?_)
    simp [hf]
  have hn : ∫ z, f z * W (-z) = -∫ z, f z * W z := by
    have := integral_neg_eq_self (fun z => f z * W z) (volume : Measure 𝔼)
    rw [← this, ← integral_neg]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp [hf]
  have hpt : ∀ z, f z * ((W z - W (-z)) / 2) = (f z * W z - f z * W (-z)) / 2 := fun z => by ring
  simp_rw [hpt]
  rw [integral_div, integral_sub h1 h2, hn]
  ring

lemma symlin_integrable_gaussodd_mul {t : ℝ} (ht : 0 < t) (i : Fin d) (W : 𝓢(𝔼, ℂ)) :
    Integrable (fun z : 𝔼 => ((z i * Real.exp (-(t * ‖z‖ ^ 2)) : ℝ) : ℂ) * W z) := by
  refine Integrable.mono' (g := fun z : 𝔼 => (1 + 1 / t) * ‖W z‖) (W.integrable.norm.const_mul _) ?_
    (Eventually.of_forall fun z => ?_)
  · refine Continuous.aestronglyMeasurable ?_
    have : Continuous (fun ξ : 𝔼 => ξ i) := (EuclideanSpace.proj i : 𝔼 →L[ℝ] ℝ).continuous
    exact (Complex.continuous_ofReal.comp (by fun_prop)).mul W.continuous
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hxi : |z i| ≤ ‖z‖ := by simpa using PiLp.norm_apply_le z i
    have hb := symlin_norm_gauss_bdd ht z
    calc |z i| * Real.exp (-(t * ‖z‖ ^ 2)) * ‖W z‖ ≤ ‖z‖ * Real.exp (-(t * ‖z‖ ^ 2)) * ‖W z‖ := by
          gcongr
      _ ≤ (1 + 1 / t) * ‖W z‖ := by gcongr

/-- Lemma A: the odd principal value of the kernel `z_i |z|^{-d-θ}` against `𝓕 G`
(`G` Schwartz, `0 < θ < 2`) is `∫ m₀ G`, `m₀ = -i C₀ ξ_i |ξ|^{θ-2}` -/
theorem symlin_lemmaA (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) (i : Fin d)
    (G : 𝓢(𝔼, ℂ)) :
    ∫ z : 𝔼, ((symlin_K d θ i z : ℝ) : ℂ) * ((𝓕 (⇑G) z - 𝓕 (⇑G) (-z)) / 2) =
      ∫ ξ : 𝔼, symlin_m0 d θ i ξ * G ξ := by
  set W : 𝓢(𝔼, ℂ) := 𝓕 G with hWdef
  have hW : (⇑W : 𝔼 → ℂ) = 𝓕 (⇑G) := SchwartzMap.fourier_coe G
  rw [← hW]
  have hγ : 0 < (d : ℝ) + θ := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  set Γ : ℝ := Real.Gamma (((d : ℝ) + θ) / 2) with hΓdef
  have hΓ : 0 < Γ := Real.Gamma_pos_of_pos (by linarith)
  -- step 3
  have step3 : (Γ : ℂ) * ∫ z : 𝔼, ((symlin_K d θ i z : ℝ) : ℂ) * ((W z - W (-z)) / 2) =
      ∫ z : 𝔼, ∫ t in Ioi (0 : ℝ), ((t ^ (((d : ℝ) + θ) / 2 - 1) * (z i * Real.exp (-(t * ‖z‖ ^ 2))) : ℝ) : ℂ) *
        ((W z - W (-z)) / 2) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only
    rw [symlin_odd_gauss_integral hγ i z, ← mul_assoc]
    congr 1
    rw [symlin_K, Real.rpow_neg (norm_nonneg _), div_eq_mul_inv]
    push_cast
    ring
  refine mul_left_cancel₀ (Complex.ofReal_ne_zero.2 hΓ.ne') ?_
  rw [step3]
  -- step 4
  rw [integral_integral_swap (symlin_integrable_fub1 hd hθ0 hθ2 i W)]
  -- step 5
  have step5 : ∀ t ∈ Ioi (0 : ℝ), ∫ z : 𝔼, ((t ^ (((d : ℝ) + θ) / 2 - 1) * (z i * Real.exp (-(t * ‖z‖ ^ 2))) : ℝ) : ℂ) *
        ((W z - W (-z)) / 2) = ∫ ξ : 𝔼, symlin_F3 d θ i G t ξ := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have h1 : ∀ z : 𝔼, ((t ^ (((d : ℝ) + θ) / 2 - 1) * (z i * Real.exp (-(t * ‖z‖ ^ 2))) : ℝ) : ℂ) *
        ((W z - W (-z)) / 2) = ((t ^ (((d : ℝ) + θ) / 2 - 1) : ℝ) : ℂ) *
          (((z i * Real.exp (-(t * ‖z‖ ^ 2)) : ℝ) : ℂ) * ((W z - W (-z)) / 2)) := fun z => by
      simp only [Complex.ofReal_mul]; ring
    simp_rw [h1]
    rw [integral_const_mul]
    unfold symlin_F3
    rw [symlin_odd_trick (f := fun z : 𝔼 => ((z i * Real.exp (-(t * ‖z‖ ^ 2)) : ℝ) : ℂ))
      (W := W) (fun z => by simp [norm_neg]) (symlin_integrable_gaussodd_mul ht' i W), hW,
      symlin_odd_gauss_pair ht' G i, ← integral_const_mul]
  rw [setIntegral_congr_fun measurableSet_Ioi step5]
  -- step 6
  rw [integral_integral_swap (symlin_integrable_fub2 hd hθ0 hθ2 i G)]
  have step6 : ∀ ξ : 𝔼, ∫ t in Ioi (0 : ℝ), symlin_F3 d θ i G t ξ = (Γ : ℂ) * (symlin_m0 d θ i ξ * G ξ) := by
    intro ξ
    rw [symlin_t_integral hθ0 hθ2 i G ξ]
    ring
  simp_rw [step6]
  rw [integral_const_mul]

end HRS.CZ.Sym
