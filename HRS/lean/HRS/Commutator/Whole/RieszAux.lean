import HRS.Commutator.Whole.Defs

/-!
# Helpers for the Fourier transform of the Riesz potential (packet X-RP)

Gaussian subordination `Γ(γ/2) |x|^{-γ} = ∫_0^∞ t^{γ/2-1} e^{-t|x|²} dt`, the Gaussian Fourier
transform (Mathlib `fourier_gaussian_innerProductSpace`), the multiplication formula, and the
substitution `t ↦ 1/t` on `(0,∞)` (Mathlib `integral_comp_rpow_Ioi` with exponent `-1`).
-/

open MeasureTheory Filter Topology Metric Real Set
open scoped ENNReal NNReal FourierTransform ContDiff

noncomputable section

namespace HRS.Commutator.Whole

variable {d : ℕ}

/-- Integrability of `t ↦ t^(a-1) e^{-rt}` on `(0,∞)`. -/
lemma integrableOn_gamma_kernel {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ (a - 1) * Real.exp (-(r * t))) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := a - 1) (b := r)
    (by linarith) one_pos hr
  refine h.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp [Real.rpow_one, neg_mul]

/-- The substitution `t ↦ 1/t` on `(0,∞)`: `∫ t^{-β-1} e^{-c/t} = c^{-β} Γ(β)`. -/
lemma integrableOn_and_integral_inv_kernel {β c : ℝ} (hβ : 0 < β) (hc : 0 < c) :
    IntegrableOn (fun t : ℝ => t ^ (-β - 1) * Real.exp (-(c / t))) (Ioi 0) ∧
      ∫ t in Ioi 0, t ^ (-β - 1) * Real.exp (-(c / t)) = c ^ (-β) * Real.Gamma β := by
  set f : ℝ → ℝ := fun y => y ^ (β - 1) * Real.exp (-(c * y)) with hf
  have hfi : IntegrableOn f (Ioi 0) := integrableOn_gamma_kernel hβ hc
  have hp : (-1 : ℝ) ≠ 0 := by norm_num
  have hpt : ∀ x : ℝ, 0 < x → (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • f (x ^ (-1 : ℝ))
      = x ^ (-β - 1) * Real.exp (-(c / x)) := by
    intro x hx
    simp only [hf, smul_eq_mul, abs_neg, abs_one, one_mul]
    have e1 : x ^ ((-1 : ℝ) - 1) * (x ^ (-1 : ℝ)) ^ (β - 1) = x ^ (-β - 1) := by
      rw [← Real.rpow_mul hx.le, ← Real.rpow_add hx]
      congr 1
      ring
    have e2 : x ^ (-1 : ℝ) = x⁻¹ := Real.rpow_neg_one x
    calc x ^ ((-1 : ℝ) - 1) * ((x ^ (-1 : ℝ)) ^ (β - 1) * Real.exp (-(c * x ^ (-1 : ℝ))))
        = (x ^ ((-1 : ℝ) - 1) * (x ^ (-1 : ℝ)) ^ (β - 1)) * Real.exp (-(c * x ^ (-1 : ℝ))) := by
          ring
      _ = x ^ (-β - 1) * Real.exp (-(c / x)) := by
          rw [e1, e2, div_eq_mul_inv]
  have hI := (integrableOn_Ioi_comp_rpow_iff f hp).2 hfi
  have hint := integral_comp_rpow_Ioi f hp
  constructor
  · refine hI.congr_fun (fun x hx => ?_) measurableSet_Ioi
    exact hpt x hx
  · have h1 : ∫ x in Ioi 0, (|(-1 : ℝ)| * x ^ ((-1 : ℝ) - 1)) • f (x ^ (-1 : ℝ))
        = ∫ t in Ioi 0, t ^ (-β - 1) * Real.exp (-(c / t)) :=
      setIntegral_congr_fun measurableSet_Ioi (fun x hx => hpt x hx)
    rw [← h1, hint]
    simp only [hf]
    rw [integral_rpow_mul_exp_neg_mul_Ioi hβ hc]
    rw [one_div, Real.inv_rpow hc.le, Real.rpow_neg hc.le]

/-- Gaussian subordination: `∫_{t>0} t^{γ/2-1} e^{-t|x|²} dt = |x|^{-γ} Γ(γ/2)` for `x ≠ 0`. -/
lemma integral_gauss_subordination {γ : ℝ} (hγ : 0 < γ) (x : Euc d) (hx : x ≠ 0) :
    ∫ t in Ioi (0 : ℝ), t ^ (γ / 2 - 1) * Real.exp (-(t * ‖x‖ ^ 2))
      = ‖x‖ ^ (-γ) * Real.Gamma (γ / 2) := by
  have hr : 0 < ‖x‖ ^ 2 := by
    have : 0 < ‖x‖ := norm_pos_iff.2 hx
    positivity
  have h := integral_rpow_mul_exp_neg_mul_Ioi (a := γ / 2) (r := ‖x‖ ^ 2) (by linarith) hr
  have hmul : ∀ t : ℝ, Real.exp (-(t * ‖x‖ ^ 2)) = Real.exp (-(‖x‖ ^ 2 * t)) := fun t => by
    rw [mul_comm]
  simp only [hmul]
  rw [h]
  congr 1
  rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg x),
    ← Real.rpow_neg (norm_nonneg x)]
  congr 1
  push_cast
  ring

/-- `|x|^s φ(x)` is integrable for Schwartz `φ` when `-d < s ≤ 0`. -/
lemma integrable_norm_rpow_mul_schwartz (hd : 1 ≤ d) {s : ℝ} (hs1 : -(d : ℝ) < s) (hs2 : s ≤ 0)
    (f : SchwartzMap (Euc d) ℂ) :
    Integrable (fun x : Euc d => ‖x‖ ^ s * ‖f x‖) := by
  have hloc : IntegrableOn (fun x : Euc d => ‖x‖ ^ s) (ball 0 1) := by
    refine integrableOn_ball_of_norm_le_rpow (μ := volume) (f := fun x : Euc d => ‖x‖ ^ s)
      (C := 1) (α := -s) (r := 1) (by rw [finrank_euclideanSpace_fin]; exact hd) ?_ ?_ ?_
    · rw [finrank_euclideanSpace_fin]; linarith
    · exact Eventually.of_forall fun x => by
        rw [neg_neg, one_mul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg x) s)]
    · exact ((measurable_norm.pow_const s)).aestronglyMeasurable
  have hind : Integrable (Set.indicator (ball (0 : Euc d) 1) fun x : Euc d => ‖x‖ ^ s) :=
    (integrable_indicator_iff measurableSet_ball).2 hloc
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ x : Euc d, ‖f x‖ ≤ M :=
    ⟨(SchwartzMap.seminorm ℝ 0 0 f : ℝ), fun x => SchwartzMap.norm_le_seminorm ℝ f x⟩
  refine Integrable.mono' ((hind.const_mul M).add f.integrable.norm) ?_
    (Eventually.of_forall fun x => ?_)
  · exact ((measurable_norm.pow_const s).mul f.continuous.norm.measurable).aestronglyMeasurable
  · rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (norm_nonneg x) s) (norm_nonneg _))]
    have h2 : 0 ≤ ‖x‖ ^ s := Real.rpow_nonneg (norm_nonneg x) s
    have h3 : 0 ≤ ‖f x‖ := norm_nonneg _
    by_cases hx : x ∈ ball (0 : Euc d) 1
    · have hind_x : (Set.indicator (ball (0 : Euc d) 1) fun y : Euc d => ‖y‖ ^ s) x = ‖x‖ ^ s :=
        Set.indicator_of_mem hx _
      have h4 : ‖x‖ ^ s * ‖f x‖ ≤ ‖x‖ ^ s * M := mul_le_mul_of_nonneg_left (hM x) h2
      show ‖x‖ ^ s * ‖f x‖ ≤ M * (Set.indicator (ball (0 : Euc d) 1) fun y : Euc d => ‖y‖ ^ s) x + ‖f x‖
      rw [hind_x]
      linarith [mul_comm M (‖x‖ ^ s)]
    · have hind_x : (Set.indicator (ball (0 : Euc d) 1) fun y : Euc d => ‖y‖ ^ s) x = 0 :=
        Set.indicator_of_notMem hx _
      have hx1 : 1 ≤ ‖x‖ := by
        simp only [mem_ball, dist_zero_right, not_lt] at hx
        exact hx
      have h4 : ‖x‖ ^ s ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 hs2
      have h5 : ‖x‖ ^ s * ‖f x‖ ≤ ‖f x‖ := mul_le_of_le_one_left h3 h4
      show ‖x‖ ^ s * ‖f x‖ ≤ M * (Set.indicator (ball (0 : Euc d) 1) fun y : Euc d => ‖y‖ ^ s) x + ‖f x‖
      rw [hind_x]
      linarith

/-- Integrability of the real Gaussian `e^{-t|v|²}` (as a complex function) on `ℝ^d`. -/
lemma integrable_gauss_real {t : ℝ} (ht : 0 < t) :
    Integrable (fun v : Euc d => ((Real.exp (-(t * ‖v‖ ^ 2)) : ℝ) : ℂ)) := by
  have hb : 0 < ((t : ℂ)).re := by simpa using ht
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := Euc d) hb 0 0
  refine h.congr (Eventually.of_forall fun v => ?_)
  simp only [zero_mul, add_zero, Complex.ofReal_exp]
  congr 1
  push_cast
  ring

/-- Fourier transform of the real Gaussian: `𝓕[e^{-t|·|²}](ξ) = (π/t)^{d/2} e^{-π²|ξ|²/t}`. -/
lemma gauss_fourier_real {t : ℝ} (ht : 0 < t) (ξ : Euc d) :
    𝓕 (fun v : Euc d => ((Real.exp (-(t * ‖v‖ ^ 2)) : ℝ) : ℂ)) ξ
      = (((π / t) ^ ((d : ℝ) / 2) : ℝ) : ℂ) * ((Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)) : ℝ) : ℂ) := by
  have hb : 0 < ((t : ℂ)).re := by simpa using ht
  have h := fourier_gaussian_innerProductSpace (b := (t : ℂ)) hb ξ
  have hfun : (fun v : Euc d => ((Real.exp (-(t * ‖v‖ ^ 2)) : ℝ) : ℂ))
      = fun v : Euc d => Complex.exp (-(t : ℂ) * ((‖v‖ : ℝ) : ℂ) ^ 2) := by
    funext v
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hfun, h, finrank_euclideanSpace_fin]
  have e1 : (((π / t) ^ ((d : ℝ) / 2) : ℝ) : ℂ) = ((π : ℂ) / (t : ℂ)) ^ ((d : ℂ) / 2) := by
    rw [Complex.ofReal_cpow (by positivity)]
    push_cast
    rfl
  have e2 : ((Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)) : ℝ) : ℂ)
      = Complex.exp (-(π : ℂ) ^ 2 * ((‖ξ‖ : ℝ) : ℂ) ^ 2 / (t : ℂ)) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [e1, e2]

/-- Almost every point of `ℝ^d` (`d ≥ 1`) is nonzero. -/
lemma ae_ne_zero_euc (hd : 1 ≤ d) : ∀ᵐ x : Euc d ∂volume, x ≠ 0 := by
  haveI : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by rw [finrank_euclideanSpace_fin]; omega)
  have h0 : volume ({0} : Set (Euc d)) = 0 := measure_singleton _
  rw [ae_iff]
  simpa using h0

lemma integrableOn_gamma_kernel' {a r : ℝ} (ha : 0 < a) (hr : 0 < r) :
    IntegrableOn (fun t : ℝ => t ^ (a - 1) * Real.exp (-(t * r))) (Ioi 0) := by
  refine (integrableOn_gamma_kernel ha hr).congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only
  rw [mul_comm t r]

lemma enorm_real_mul_eq {r : ℝ} (hr : 0 ≤ r) (z : ℂ) :
    ‖((r : ℝ) : ℂ) * z‖ₑ = ENNReal.ofReal (r * ‖z‖) := by
  rw [← ofReal_norm, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr]

/-- Integrability of `(x,t) ↦ t^{γ/2-1} e^{-t|x|²} Φ(x)` (Tonelli in the order `x` outer). -/
lemma riesz_integrable_left (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) (hγd : γ < d)
    (Φ : SchwartzMap (Euc d) ℂ) :
    Integrable (Function.uncurry fun (x : Euc d) (t : ℝ) =>
      ((t ^ (γ / 2 - 1) * Real.exp (-(t * ‖x‖ ^ 2)) : ℝ) : ℂ) * Φ x)
      ((volume : Measure (Euc d)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  have hmeas : AEStronglyMeasurable (Function.uncurry fun (x : Euc d) (t : ℝ) =>
      ((t ^ (γ / 2 - 1) * Real.exp (-(t * ‖x‖ ^ 2)) : ℝ) : ℂ) * Φ x)
      ((volume : Measure (Euc d)).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    apply Measurable.aestronglyMeasurable
    refine Measurable.mul ?_ ?_
    · refine Complex.measurable_ofReal.comp (Measurable.mul ?_ ?_)
      · exact (measurable_snd.pow_const _)
      · exact Real.continuous_exp.measurable.comp
          ((measurable_snd.mul (measurable_fst.norm.pow_const 2)).neg)
    · exact Φ.continuous.measurable.comp measurable_fst
  refine ⟨hmeas, ?_⟩
  unfold HasFiniteIntegral
  rw [lintegral_prod _ hmeas.enorm]
  have hpoint : ∀ x : Euc d, x ≠ 0 → ∫⁻ t in Ioi (0 : ℝ),
      ‖((t ^ (γ / 2 - 1) * Real.exp (-(t * ‖x‖ ^ 2)) : ℝ) : ℂ) * Φ x‖ₑ
        = ENNReal.ofReal (Real.Gamma (γ / 2)) * ENNReal.ofReal (‖x‖ ^ (-γ) * ‖Φ x‖) := by
    intro x hx
    have hr : 0 < ‖x‖ ^ 2 := by
      have : 0 < ‖x‖ := norm_pos_iff.2 hx
      positivity
    have hnn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ t ^ (γ / 2 - 1) * Real.exp (-(t * ‖x‖ ^ 2)) :=
      fun t ht => mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le
    rw [setLIntegral_congr_fun measurableSet_Ioi (fun t ht => enorm_real_mul_eq (hnn t ht) _)]
    have hint : IntegrableOn (fun t : ℝ => (t ^ (γ / 2 - 1) * Real.exp (-(t * ‖x‖ ^ 2))) * ‖Φ x‖)
        (Ioi 0) :=
      (integrableOn_gamma_kernel' (by linarith) hr).mul_const _
    have hnn' : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
        (fun t : ℝ => (t ^ (γ / 2 - 1) * Real.exp (-(t * ‖x‖ ^ 2))) * ‖Φ x‖) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (hnn t ht) (norm_nonneg _)
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn']
    rw [integral_mul_const, integral_gauss_subordination hγ x hx]
    rw [← ENNReal.ofReal_mul (Real.Gamma_pos_of_pos (by linarith)).le]
    congr 1
    ring
  have hint := integrable_norm_rpow_mul_schwartz hd (s := -γ) (by linarith) (by linarith) Φ
  have hfin : ∫⁻ x : Euc d, ENNReal.ofReal (‖x‖ ^ (-γ) * ‖Φ x‖) < ⊤ := by
    have h := hint.hasFiniteIntegral
    unfold HasFiniteIntegral at h
    refine lt_of_le_of_lt (le_of_eq ?_) h
    apply lintegral_congr
    intro x
    rw [← ofReal_norm, Real.norm_of_nonneg (by positivity)]
  refine lt_of_eq_of_lt (b := ∫⁻ x : Euc d, ENNReal.ofReal (Real.Gamma (γ / 2))
      * ENNReal.ofReal (‖x‖ ^ (-γ) * ‖Φ x‖)) (lintegral_congr_ae ?_) ?_
  · filter_upwards [ae_ne_zero_euc hd] with x hx
    exact hpoint x hx
  · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

/-- Multiplication formula for the Fourier transform on `ℝ^d`: `∫ g · 𝓕φ = ∫ 𝓕g · φ`. -/
lemma integral_mul_fourier_eq (g φ : Euc d → ℂ) (hg : Integrable g) (hφ : Integrable φ) :
    ∫ x, g x * 𝓕 φ x = ∫ ξ, 𝓕 g ξ * φ ξ := by
  have hL : (innerₗ (Euc d)).flip = innerₗ (Euc d) := by
    ext v w
    simp
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip (e := 𝐞) (μ := volume)
    (ν := volume) (L := innerₗ (Euc d)) (f := g) (g := φ) continuous_fourierChar
    continuous_inner hg hφ
  simp only [smul_eq_mul] at h
  rw [hL] at h
  exact h.symm

/-- The inner `x`-integral in the Riesz identity, after the multiplication formula. -/
lemma riesz_inner {γ t : ℝ} (ht : 0 < t) (φ : SchwartzMap (Euc d) ℂ) :
    ∫ x, ((t ^ (γ / 2 - 1) * Real.exp (-(t * ‖x‖ ^ 2)) : ℝ) : ℂ) * (𝓕 (⇑φ)) x
      = ((t ^ (γ / 2 - 1) : ℝ) : ℂ) * ∫ ξ, (((π / t) ^ ((d : ℝ) / 2) : ℝ) : ℂ)
          * ((Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)) : ℝ) : ℂ) * φ ξ := by
  have h1 : ∀ x : Euc d, ((t ^ (γ / 2 - 1) * Real.exp (-(t * ‖x‖ ^ 2)) : ℝ) : ℂ) * (𝓕 (⇑φ)) x
      = ((t ^ (γ / 2 - 1) : ℝ) : ℂ) * (((Real.exp (-(t * ‖x‖ ^ 2)) : ℝ) : ℂ) * (𝓕 (⇑φ)) x) := by
    intro x
    push_cast
    ring
  have hm : ∫ x : Euc d, ((Real.exp (-(t * ‖x‖ ^ 2)) : ℝ) : ℂ) * (𝓕 (⇑φ)) x
      = ∫ ξ : Euc d, 𝓕 (fun v : Euc d => ((Real.exp (-(t * ‖v‖ ^ 2)) : ℝ) : ℂ)) ξ * φ ξ :=
    integral_mul_fourier_eq _ _ (integrable_gauss_real ht) φ.integrable
  simp_rw [h1]
  rw [integral_const_mul, hm]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards with ξ
  rw [gauss_fourier_real ht ξ]

/-- Pointwise identity `t^{γ/2-1} (π/t)^{d/2} e^{-π²|ξ|²/t} = π^{d/2} t^{-β-1} e^{-c/t}`. -/
lemma riesz_kernel_pointwise {γ : ℝ} (hγd : γ < d) {t : ℝ} (ht : 0 < t) (ξ : Euc d) :
    t ^ (γ / 2 - 1) * (π / t) ^ ((d : ℝ) / 2) * Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t))
      = π ^ ((d : ℝ) / 2) * (t ^ (-(((d : ℝ) - γ) / 2) - 1)
          * Real.exp (-((π ^ 2 * ‖ξ‖ ^ 2) / t))) := by
  rw [Real.div_rpow Real.pi_pos.le ht.le]
  have e : t ^ (-(((d : ℝ) - γ) / 2) - 1) = t ^ (γ / 2 - 1) / t ^ ((d : ℝ) / 2) := by
    rw [← Real.rpow_sub ht]
    congr 1
    ring
  rw [e]
  ring

/-- The constant `π^{d/2} (π²|ξ|²)^{-β} = π^{γ-d/2} |ξ|^{γ-d}`, with `β = (d-γ)/2`. -/
lemma riesz_const_identity (γ : ℝ) (ξ : Euc d) :
    π ^ ((d : ℝ) / 2) * (π ^ 2 * ‖ξ‖ ^ 2) ^ (-(((d : ℝ) - γ) / 2))
      = π ^ (γ - (d : ℝ) / 2) * ‖ξ‖ ^ (γ - (d : ℝ)) := by
  have hπ : (0 : ℝ) ≤ π := Real.pi_pos.le
  have hn : (0 : ℝ) ≤ ‖ξ‖ := norm_nonneg ξ
  rw [Real.mul_rpow (by positivity) (by positivity)]
  have h1 : (π ^ 2 : ℝ) ^ (-(((d : ℝ) - γ) / 2)) = π ^ (-((d : ℝ) - γ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hπ]
    congr 1
    push_cast
    ring
  have h2 : (‖ξ‖ ^ 2) ^ (-(((d : ℝ) - γ) / 2)) = ‖ξ‖ ^ (γ - (d : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn]
    congr 1
    push_cast
    ring
  rw [h1, h2]
  have h3 : π ^ ((d : ℝ) / 2) * π ^ (-((d : ℝ) - γ)) = π ^ (γ - (d : ℝ) / 2) := by
    rw [← Real.rpow_add Real.pi_pos]
    congr 1
    ring
  rw [← mul_assoc, h3]

/-- The `t`-integral for fixed `ξ ≠ 0`. -/
lemma riesz_t_integral {γ : ℝ} (hγd : γ < d) {ξ : Euc d} (hξ : ξ ≠ 0) :
    ∫ t in Ioi (0 : ℝ), π ^ ((d : ℝ) / 2) * (t ^ (-(((d : ℝ) - γ) / 2) - 1)
        * Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)))
      = π ^ (γ - (d : ℝ) / 2) * ‖ξ‖ ^ (γ - (d : ℝ)) * Real.Gamma (((d : ℝ) - γ) / 2) := by
  have hβ : 0 < ((d : ℝ) - γ) / 2 := by linarith
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have hc : 0 < π ^ 2 * ‖ξ‖ ^ 2 := by positivity
  rw [integral_const_mul, (integrableOn_and_integral_inv_kernel hβ hc).2, ← mul_assoc,
    riesz_const_identity]

/-- Integrability of `(t,ξ) ↦ t^{γ/2-1}(π/t)^{d/2} e^{-π²|ξ|²/t} φ(ξ)` (Tonelli, `ξ` outer). -/
lemma riesz_integrable_right (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) (hγd : γ < d)
    (φ : SchwartzMap (Euc d) ℂ) :
    Integrable (Function.uncurry fun (t : ℝ) (ξ : Euc d) =>
      ((t ^ (γ / 2 - 1) : ℝ) : ℂ) * ((((π / t) ^ ((d : ℝ) / 2)) : ℝ) : ℂ)
        * ((Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)) : ℝ) : ℂ) * φ ξ)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
  have hmeas : AEStronglyMeasurable (Function.uncurry fun (t : ℝ) (ξ : Euc d) =>
      ((t ^ (γ / 2 - 1) : ℝ) : ℂ) * ((((π / t) ^ ((d : ℝ) / 2)) : ℝ) : ℂ)
        * ((Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)) : ℝ) : ℂ) * φ ξ)
      ((volume.restrict (Ioi (0 : ℝ))).prod volume) := by
    apply Measurable.aestronglyMeasurable
    refine Measurable.mul (Measurable.mul (Measurable.mul ?_ ?_) ?_) ?_
    · exact Complex.measurable_ofReal.comp (measurable_fst.pow_const _)
    · exact Complex.measurable_ofReal.comp ((measurable_const.div measurable_fst).pow_const _)
    · exact Complex.measurable_ofReal.comp (Real.continuous_exp.measurable.comp
        ((measurable_const.mul (measurable_snd.norm.pow_const 2)).div measurable_fst).neg)
    · exact φ.continuous.measurable.comp measurable_snd
  refine ⟨hmeas, ?_⟩
  unfold HasFiniteIntegral
  rw [lintegral_prod_symm _ hmeas.enorm]
  have hβ : 0 < ((d : ℝ) - γ) / 2 := by linarith
  have hlin : ∀ ξ : Euc d, ξ ≠ 0 → ∫⁻ t in Ioi (0 : ℝ),
      ‖((t ^ (γ / 2 - 1) : ℝ) : ℂ) * ((((π / t) ^ ((d : ℝ) / 2)) : ℝ) : ℂ)
        * ((Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)) : ℝ) : ℂ) * φ ξ‖ₑ
        = ENNReal.ofReal ((π ^ (γ - (d : ℝ) / 2) * ‖ξ‖ ^ (γ - (d : ℝ)) * Real.Gamma (((d : ℝ) - γ) / 2))
            * ‖φ ξ‖) := by
    intro ξ hξ
    have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    have hc : 0 < π ^ 2 * ‖ξ‖ ^ 2 := by positivity
    have hpt : ∀ t ∈ Ioi (0 : ℝ), ‖((t ^ (γ / 2 - 1) : ℝ) : ℂ) * ((((π / t) ^ ((d : ℝ) / 2)) : ℝ) : ℂ)
        * ((Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)) : ℝ) : ℂ) * φ ξ‖ₑ
          = ENNReal.ofReal ((π ^ ((d : ℝ) / 2) * (t ^ (-(((d : ℝ) - γ) / 2) - 1)
              * Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)))) * ‖φ ξ‖) := by
      intro t ht
      have ht' : (0 : ℝ) < t := ht
      have h2 : ((t ^ (γ / 2 - 1) : ℝ) : ℂ) * ((((π / t) ^ ((d : ℝ) / 2)) : ℝ) : ℂ)
          * ((Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)) : ℝ) : ℂ)
          = ((t ^ (γ / 2 - 1) * (π / t) ^ ((d : ℝ) / 2) * Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)) : ℝ) : ℂ) := by
        push_cast
        ring
      rw [h2, riesz_kernel_pointwise hγd ht' ξ, mul_assoc]
      rw [enorm_real_mul_eq (by positivity) (φ ξ)]
      congr 1
      ring
    rw [setLIntegral_congr_fun measurableSet_Ioi (fun t ht => hpt t ht)]
    have hint : IntegrableOn (fun t : ℝ => (π ^ ((d : ℝ) / 2) * (t ^ (-(((d : ℝ) - γ) / 2) - 1)
        * Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)))) * ‖φ ξ‖) (Ioi 0) :=
      ((integrableOn_and_integral_inv_kernel hβ hc).1.const_mul (π ^ ((d : ℝ) / 2))).mul_const _
    have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] (fun t : ℝ =>
        (π ^ ((d : ℝ) / 2) * (t ^ (-(((d : ℝ) - γ) / 2) - 1)
          * Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)))) * ‖φ ξ‖) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht' : (0 : ℝ) < t := ht
      have : 0 ≤ t ^ (-(((d : ℝ) - γ) / 2) - 1) * Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)) :=
        mul_nonneg (Real.rpow_nonneg ht'.le _) (Real.exp_pos _).le
      exact mul_nonneg (mul_nonneg (by positivity) this) (norm_nonneg _)
    rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, integral_mul_const, riesz_t_integral hγd hξ]
  have hint2 := integrable_norm_rpow_mul_schwartz hd (s := γ - (d : ℝ)) (by linarith) (by linarith) φ
  have hfin2 : ∫⁻ ξ : Euc d, ENNReal.ofReal (‖ξ‖ ^ (γ - (d : ℝ)) * ‖φ ξ‖) < ⊤ := by
    have h := hint2.hasFiniteIntegral
    unfold HasFiniteIntegral at h
    refine lt_of_le_of_lt (le_of_eq ?_) h
    apply lintegral_congr
    intro ξ
    rw [← ofReal_norm, Real.norm_of_nonneg (by positivity)]
  have hC : 0 ≤ π ^ (γ - (d : ℝ) / 2) * Real.Gamma (((d : ℝ) - γ) / 2) := by
    have := Real.Gamma_pos_of_pos hβ
    positivity
  refine lt_of_eq_of_lt (b := ∫⁻ ξ : Euc d, ENNReal.ofReal (π ^ (γ - (d : ℝ) / 2)
      * Real.Gamma (((d : ℝ) - γ) / 2)) * ENNReal.ofReal (‖ξ‖ ^ (γ - (d : ℝ)) * ‖φ ξ‖))
    (lintegral_congr_ae ?_) ?_
  · filter_upwards [ae_ne_zero_euc hd] with ξ hξ
    refine (hlin ξ hξ).trans ?_
    rw [← ENNReal.ofReal_mul hC]
    congr 1
    ring
  · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin2

/-- Gaussian subordination with a constant factor `z`. -/
lemma riesz_gamma_pointwise {γ : ℝ} (hγ : 0 < γ) (x : Euc d) (hx : x ≠ 0) (z : ℂ) :
    ∫ t in Ioi (0 : ℝ), ((t ^ (γ / 2 - 1) * Real.exp (-(t * ‖x‖ ^ 2)) : ℝ) : ℂ) * z
      = (((‖x‖ ^ (-γ) * Real.Gamma (γ / 2)) : ℝ) : ℂ) * z := by
  rw [integral_mul_const, integral_complex_ofReal, integral_gauss_subordination hγ x hx]

/-- The first Fubini exchange in the Riesz identity. -/
lemma riesz_swap_left (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) (hγd : γ < d)
    (Φ : SchwartzMap (Euc d) ℂ) :
    ∫ x : Euc d, ∫ t in Ioi (0 : ℝ), ((t ^ (γ / 2 - 1) * Real.exp (-(t * ‖x‖ ^ 2)) : ℝ) : ℂ) * Φ x
      = ∫ t in Ioi (0 : ℝ), ∫ x : Euc d, ((t ^ (γ / 2 - 1) * Real.exp (-(t * ‖x‖ ^ 2)) : ℝ) : ℂ) * Φ x :=
  integral_integral_swap (riesz_integrable_left hd hγ hγd Φ)

/-- The second Fubini exchange in the Riesz identity. -/
lemma riesz_swap_right (hd : 1 ≤ d) {γ : ℝ} (hγ : 0 < γ) (hγd : γ < d)
    (φ : SchwartzMap (Euc d) ℂ) :
    ∫ t in Ioi (0 : ℝ), ∫ ξ : Euc d, ((t ^ (γ / 2 - 1) : ℝ) : ℂ) * ((((π / t) ^ ((d : ℝ) / 2)) : ℝ) : ℂ)
        * ((Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)) : ℝ) : ℂ) * φ ξ
      = ∫ ξ : Euc d, ∫ t in Ioi (0 : ℝ), ((t ^ (γ / 2 - 1) : ℝ) : ℂ) * ((((π / t) ^ ((d : ℝ) / 2)) : ℝ) : ℂ)
        * ((Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)) : ℝ) : ℂ) * φ ξ :=
  integral_integral_swap (riesz_integrable_right hd hγ hγd φ)

/-- The `t`-integral of the second kernel, for `ξ ≠ 0`. -/
lemma riesz_t_integral_kernel {γ : ℝ} (hγd : γ < d) {ξ : Euc d} (hξ : ξ ≠ 0) (φ : SchwartzMap (Euc d) ℂ) :
    ∫ t in Ioi (0 : ℝ), ((t ^ (γ / 2 - 1) : ℝ) : ℂ) * ((((π / t) ^ ((d : ℝ) / 2)) : ℝ) : ℂ)
        * ((Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)) : ℝ) : ℂ) * φ ξ
      = (((π ^ (γ - (d : ℝ) / 2) * Real.Gamma (((d : ℝ) - γ) / 2)) * ‖ξ‖ ^ (γ - (d : ℝ)) : ℝ) : ℂ)
        * φ ξ := by
  have hpt : ∀ t ∈ Ioi (0 : ℝ), ((t ^ (γ / 2 - 1) : ℝ) : ℂ) * ((((π / t) ^ ((d : ℝ) / 2)) : ℝ) : ℂ)
      * ((Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)) : ℝ) : ℂ) * φ ξ
        = ((π ^ ((d : ℝ) / 2) * (t ^ (-(((d : ℝ) - γ) / 2) - 1)
            * Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t))) : ℝ) : ℂ) * φ ξ := by
    intro t ht
    have ht' : (0 : ℝ) < t := ht
    have h2 : ((t ^ (γ / 2 - 1) : ℝ) : ℂ) * ((((π / t) ^ ((d : ℝ) / 2)) : ℝ) : ℂ)
        * ((Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)) : ℝ) : ℂ)
        = ((t ^ (γ / 2 - 1) * (π / t) ^ ((d : ℝ) / 2) * Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h2, riesz_kernel_pointwise hγd ht' ξ]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => hpt t ht)]
  have hβ : 0 < ((d : ℝ) - γ) / 2 := by linarith
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have hc : 0 < π ^ 2 * ‖ξ‖ ^ 2 := by positivity
  have hint := (integrableOn_and_integral_inv_kernel hβ hc).1.const_mul (π ^ ((d : ℝ) / 2))
  rw [integral_mul_const, integral_complex_ofReal, riesz_t_integral hγd hξ]
  congr 1
  congr 1
  ring

/-- Stein V Lemma 1 in the form of `riesz_potential_fourier` (proof by Gaussian subordination). -/
theorem riesz_potential_aux (hd : 1 ≤ d) (γ : ℝ) (hγ : 0 < γ) (hγd : γ < d)
    (φ : SchwartzMap (Euc d) ℂ) :
    (Real.pi ^ (-γ / 2) * Real.Gamma (γ / 2) : ℝ) *
        ∫ x : Euc d, ((‖x‖ ^ (-γ) : ℝ) : ℂ) * 𝓕 (⇑φ) x =
      (Real.pi ^ (-((d : ℝ) - γ) / 2) * Real.Gamma (((d : ℝ) - γ) / 2) : ℝ) *
        ∫ ξ : Euc d, ((‖ξ‖ ^ (γ - d) : ℝ) : ℂ) * φ ξ := by
  have hβ : 0 < ((d : ℝ) - γ) / 2 := by linarith
  have hmain : ((Real.Gamma (γ / 2) : ℝ) : ℂ) * ∫ x : Euc d, ((‖x‖ ^ (-γ) : ℝ) : ℂ) * 𝓕 (⇑φ) x
      = (((Real.pi ^ (γ - (d : ℝ) / 2) * Real.Gamma (((d : ℝ) - γ) / 2)) : ℝ) : ℂ)
        * ∫ ξ : Euc d, ((‖ξ‖ ^ (γ - (d : ℝ)) : ℝ) : ℂ) * φ ξ := by
    have e1 : ((Real.Gamma (γ / 2) : ℝ) : ℂ) * ∫ x : Euc d, ((‖x‖ ^ (-γ) : ℝ) : ℂ) * 𝓕 (⇑φ) x
        = ∫ x : Euc d, ∫ t in Ioi (0 : ℝ),
            ((t ^ (γ / 2 - 1) * Real.exp (-(t * ‖x‖ ^ 2)) : ℝ) : ℂ) * 𝓕 (⇑φ) x := by
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [ae_ne_zero_euc hd] with x hx
      rw [riesz_gamma_pointwise hγ x hx]
      push_cast
      ring
    have hsw := riesz_swap_left hd hγ hγd (𝓕 φ)
    rw [SchwartzMap.fourier_coe] at hsw
    rw [e1, hsw]
    have e2 : ∫ t in Ioi (0 : ℝ), ∫ x : Euc d,
          ((t ^ (γ / 2 - 1) * Real.exp (-(t * ‖x‖ ^ 2)) : ℝ) : ℂ) * 𝓕 (⇑φ) x
        = ∫ t in Ioi (0 : ℝ), ∫ ξ : Euc d, ((t ^ (γ / 2 - 1) : ℝ) : ℂ)
            * ((((π / t) ^ ((d : ℝ) / 2)) : ℝ) : ℂ) * ((Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)) : ℝ) : ℂ)
            * φ ξ := by
      refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
      rw [riesz_inner ht φ, ← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun ξ : Euc d => ?_))
      ring
    rw [e2, riesz_swap_right hd hγ hγd φ]
    have e3 : ∫ ξ : Euc d, ∫ t in Ioi (0 : ℝ), ((t ^ (γ / 2 - 1) : ℝ) : ℂ)
            * ((((π / t) ^ ((d : ℝ) / 2)) : ℝ) : ℂ) * ((Real.exp (-(π ^ 2 * ‖ξ‖ ^ 2 / t)) : ℝ) : ℂ)
            * φ ξ
        = ∫ ξ : Euc d, (((Real.pi ^ (γ - (d : ℝ) / 2) * Real.Gamma (((d : ℝ) - γ) / 2)) : ℝ) : ℂ)
            * ((((‖ξ‖ ^ (γ - (d : ℝ))) : ℝ) : ℂ) * φ ξ) := by
      refine integral_congr_ae ?_
      filter_upwards [ae_ne_zero_euc hd] with ξ hξ
      rw [riesz_t_integral_kernel hγd hξ φ]
      push_cast
      ring
    rw [e3, integral_const_mul]
  have hpow : Real.pi ^ (-γ / 2) * Real.pi ^ (γ - (d : ℝ) / 2)
      = Real.pi ^ (-((d : ℝ) - γ) / 2) := by
    rw [← Real.rpow_add Real.pi_pos]
    congr 1
    ring
  have hfin : (((Real.pi ^ (-γ / 2) * Real.Gamma (γ / 2) : ℝ)) : ℂ) * ∫ x : Euc d, ((‖x‖ ^ (-γ) : ℝ) : ℂ) * 𝓕 (⇑φ) x
      = (((Real.pi ^ (-((d : ℝ) - γ) / 2) * Real.Gamma (((d : ℝ) - γ) / 2)) : ℝ) : ℂ)
        * ∫ ξ : Euc d, ((‖ξ‖ ^ (γ - d) : ℝ) : ℂ) * φ ξ := by
    calc (((Real.pi ^ (-γ / 2) * Real.Gamma (γ / 2) : ℝ)) : ℂ) * ∫ x : Euc d, ((‖x‖ ^ (-γ) : ℝ) : ℂ) * 𝓕 (⇑φ) x
        = ((Real.pi ^ (-γ / 2) : ℝ) : ℂ) * (((Real.Gamma (γ / 2) : ℝ)) : ℂ)
            * ∫ x : Euc d, ((‖x‖ ^ (-γ) : ℝ) : ℂ) * 𝓕 (⇑φ) x := by
          push_cast
          ring
      _ = ((Real.pi ^ (-γ / 2) : ℝ) : ℂ) * ((((Real.pi ^ (γ - (d : ℝ) / 2) * Real.Gamma (((d : ℝ) - γ) / 2)) : ℝ) : ℂ)
            * ∫ ξ : Euc d, ((‖ξ‖ ^ (γ - (d : ℝ)) : ℝ) : ℂ) * φ ξ) := by
          rw [← hmain]
          ring
      _ = (((Real.pi ^ (-((d : ℝ) - γ) / 2) * Real.Gamma (((d : ℝ) - γ) / 2)) : ℝ) : ℂ)
          * ∫ ξ : Euc d, ((‖ξ‖ ^ (γ - d) : ℝ) : ℂ) * φ ξ := by
          rw [← hpow]
          push_cast
          ring
  exact hfin

end HRS.Commutator.Whole
