import HRS.MC.SEdgeB14
import HRS.MC.SEdgeU0
import HRS.MC.SEdgeU1
import HRS.MC.SEdgeU3

/-!
# Packet U4: assembly of `static_edge_char` (relocated proof of `static_edge_char_proof`).

For `p = 1`, the real and imaginary parts of `E exp(i t W_N)` are `E cos(t W_N)` and `E sin(t W_N)`; by
`static_edge` (B14) the scaled remainders `sed_Uerr` of `cos(t .)`, `sin(t .)` tend to `0` for each `t`,
by U3 they are equi-Lipschitz on `[-T, T]`, hence uniformly small (U1, composed with the clamp onto
`[-T, T]`); U0 identifies the Gaussian integrals.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.U4

open HRS HRS.Sec7 HRS.MC.SEdge HRS.MC.SEdge.U2 HRS.MC.SEdge.U3

/-! ### Gaussian integrals -/

lemma u4_iter3 : iteratedDeriv 3 (u2h true) = Real.sin ∧ iteratedDeriv 3 (u2h false) = -Real.cos := by
  constructor
  · funext x
    simp [u2h, iteratedDeriv_succ, Real.deriv_cos', Real.deriv_sin]
  · funext x
    simp [u2h, iteratedDeriv_succ, Real.deriv_cos', Real.deriv_sin]

lemma u4_gauss_d3 (v : ℝ) (hv : 0 ≤ v) (t : ℝ) :
    (∫ z, iteratedFDeriv ℝ 3 (sed_Ucf true t) z ![stdVec 0, stdVec 0, stdVec 0]
        ∂(multivariateGaussian 0 (Matrix.of fun _ _ : Fin 1 => v))) = 0 ∧
    (∫ z, iteratedFDeriv ℝ 3 (sed_Ucf false t) z ![stdVec 0, stdVec 0, stdVec 0]
        ∂(multivariateGaussian 0 (Matrix.of fun _ _ : Fin 1 => v))) =
      -(t ^ 3 * Real.exp (-(v * t ^ 2) / 2)) := by
  obtain ⟨h1, h2⟩ := HRS.MC.SEdge.U0.sed_U0_gauss_char_proof v hv t
  constructor
  · simp_rw [u3_d3_form, u4_iter3.1]
    rw [integral_const_mul, h2, mul_zero]
  · simp_rw [u3_d3_form, u4_iter3.2]
    simp only [Pi.neg_apply]
    rw [integral_const_mul, integral_neg, h1]
    ring


/-! ### Pointwise convergence of the scaled remainder -/

section Pointwise

variable {d : ℕ} {s : ℝ} {β : ℝ} {ρ : Torus d → ℝ} {φ : Torus d → ℝ}

lemma u4_pointwise (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hβ : 0 ≤ β)
    (hρ : SmoothPosDensity ρ) (hφ : Torus.IsSmooth φ) (σ : Bool) (t : ℝ) :
    Tendsto (fun N : ℕ => sed_Uerr d s β ρ φ σ N t) atTop (𝓝 0) := by
  have h := HRS.MC.SEdge.B14.static_edge_assembly_proof hd hs0 hs β hβ ρ hρ 1 (fun _ => φ)
    (fun _ => hφ) (sed_Ucf σ t) (u3_Fmem σ t)
  dsimp only at h
  refine h.congr (fun N => ?_)
  simp only [sed_Uerr, sed_kappa, sed_Cmat, sed_Q, Fin.sum_univ_one]
  ring

end Pointwise

/-! ### The exact identity for fixed `N` and `t` -/

section Identity

variable {d : ℕ} {s : ℝ} {β : ℝ} {ρ : Torus d → ℝ} {φ : Torus d → ℝ}

lemma u4_ucf_cs (σ : Bool) (t : ℝ) {N : ℕ} (Q : Measure (Config d N)) (X : Config d N) :
    sed_Ucf σ t (centeredStat Q (fun _ : Fin 1 => φ) X) =
      if σ then Real.cos (t * sed_Y Q φ X) else Real.sin (t * sed_Y Q φ X) := by
  cases σ <;> simp [sed_Ucf, centeredStat, sed_Y]

lemma u4_identity (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hβ : 0 ≤ β)
    (hρ : SmoothPosDensity ρ) (hφ : Torus.IsSmooth φ) {N : ℕ} (hN : 1 ≤ N) (t : ℝ) :
    ∫ X, Complex.exp (Complex.I * (t : ℂ) * ((sed_Y (sed_Q d s N β ρ) φ X : ℝ) : ℂ))
        ∂(sed_Q d s N β ρ) -
      Complex.exp (-((sed_Cmat d s β ρ (fun _ : Fin 1 => φ) 0 0 : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2) *
        (1 + (Complex.I * (t : ℂ)) ^ 3 * ((sed_kappa d s β ρ (fun _ : Fin 1 => φ) 0 0 0 : ℝ) : ℂ) /
          (6 * (Real.sqrt N : ℂ))) =
    (((sed_Uerr d s β ρ φ true N t : ℝ) : ℂ) + Complex.I * ((sed_Uerr d s β ρ φ false N t : ℝ) : ℂ)) /
      (Real.sqrt N : ℂ) := by
  have hQ : IsProbabilityMeasure (sed_Q d s N β ρ) :=
    HRS.MC.SEdge.B4b.b4b_isProb hd hs0 hs hβ hρ N hN
  have hφ1 : ∀ a : Fin 1, Torus.IsSmooth ((fun _ : Fin 1 => φ) a) := fun _ => hφ
  have hCpsd := HRS.MC.SEdge.B11a.sed_B11a_cov_psd_proof hd hs0 hs hβ hρ hφ1
  set Cm : Matrix (Fin 1) (Fin 1) ℝ := sed_Cmat d s β ρ (fun _ : Fin 1 => φ) with hCm
  have hv0 : 0 ≤ Cm 0 0 := hCpsd.diag_nonneg
  have hCmeq : Matrix.of (fun _ _ : Fin 1 => Cm 0 0) = Cm := by
    ext i j; fin_cases i; fin_cases j; rfl
  have hφc : Continuous φ := HRS.Q66.q66_cont_of_smooth hφ
  obtain ⟨hYm, MY, hMY⟩ := HRS.MC.SEdge.B12.b12_Y_facts hN hφc.measurable
    (HRS.Q66.q66_bound_of_smooth hφ) (sed_Q d s N β ρ)
  have hic : Integrable (fun X => Real.cos (t * sed_Y (sed_Q d s N β ρ) φ X)) (sed_Q d s N β ρ) :=
    Integrable.of_bound (C := 1)
      (Real.continuous_cos.measurable.comp (measurable_const.mul hYm)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact Real.abs_cos_le_one _)
  have his : Integrable (fun X => Real.sin (t * sed_Y (sed_Q d s N β ρ) φ X)) (sed_Q d s N β ρ) :=
    Integrable.of_bound (C := 1)
      (Real.continuous_sin.measurable.comp (measurable_const.mul hYm)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun X => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _)
  have hexp : ∀ X, Complex.exp (Complex.I * (t : ℂ) * ((sed_Y (sed_Q d s N β ρ) φ X : ℝ) : ℂ)) =
      ((Real.cos (t * sed_Y (sed_Q d s N β ρ) φ X) : ℝ) : ℂ) +
        Complex.I * ((Real.sin (t * sed_Y (sed_Q d s N β ρ) φ X) : ℝ) : ℂ) := by
    intro X
    rw [show Complex.I * (t : ℂ) * ((sed_Y (sed_Q d s N β ρ) φ X : ℝ) : ℂ) =
      ((t * sed_Y (sed_Q d s N β ρ) φ X : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
    ring
  simp_rw [hexp]
  rw [integral_add hic.ofReal (his.ofReal.const_mul _), integral_const_mul, integral_complex_ofReal,
    integral_complex_ofReal]
  obtain ⟨h1, h2⟩ := HRS.MC.SEdge.U0.sed_U0_gauss_char_proof (Cm 0 0) hv0 t
  obtain ⟨h3, h4⟩ := u4_gauss_d3 (Cm 0 0) hv0 t
  rw [hCmeq] at h1 h2 h3 h4
  have e1 : (∫ z, sed_Ucf true t z ∂(multivariateGaussian 0 Cm)) = Real.exp (-(Cm 0 0 * t ^ 2) / 2) := by
    simpa [sed_Ucf] using h1
  have e2 : (∫ z, sed_Ucf false t z ∂(multivariateGaussian 0 Cm)) = 0 := by
    simpa [sed_Ucf] using h2
  unfold sed_Uerr
  rw [e1, e2, h3, h4]
  simp only [u4_ucf_cs, ↓reduceIte, Bool.false_eq_true]
  have hsN : (Real.sqrt N : ℂ) ≠ 0 := by
    have : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN)
    exact_mod_cast this.ne'
  have hg : Complex.exp (-((Cm 0 0 : ℝ) : ℂ) * (t : ℂ) ^ 2 / 2) =
      ((Real.exp (-(Cm 0 0 * t ^ 2) / 2) : ℝ) : ℂ) := by
    rw [Complex.ofReal_exp]; congr 1; push_cast; ring
  rw [hg]
  have hI3 : (Complex.I * (t : ℂ)) ^ 3 = -(Complex.I * (t : ℂ) ^ 3) := by
    rw [mul_pow, pow_succ Complex.I 2, Complex.I_sq]; ring
  rw [hI3]
  generalize Real.exp (-(Cm 0 0 * t ^ 2) / 2) = g
  generalize (∫ X, Real.cos (t * sed_Y (sed_Q d s N β ρ) φ X) ∂(sed_Q d s N β ρ)) = Ec
  generalize (∫ X, Real.sin (t * sed_Y (sed_Q d s N β ρ) φ X) ∂(sed_Q d s N β ρ)) = Es
  generalize sed_kappa d s β ρ (fun _ : Fin 1 => φ) 0 0 0 = κ
  push_cast
  field_simp
  ring

end Identity


/-! ### Uniformity on `[-T, T]` -/

lemma u4_clamp_lip (T t t' : ℝ) :
    |max (-T) (min t T) - max (-T) (min t' T)| ≤ |t - t'| := by
  have h1 := abs_max_sub_max_le_max (-T) (min t T) (-T) (min t' T)
  have h2 := abs_min_sub_min_le_max t T t' T
  simp only [sub_self, abs_zero] at h1 h2
  rw [max_eq_right (abs_nonneg (min t T - min t' T))] at h1
  rw [max_eq_left (abs_nonneg (t - t'))] at h2
  exact h1.trans h2

lemma u4_clamp_mem {T : ℝ} (hT : 0 < T) (t : ℝ) : max (-T) (min t T) ∈ Set.Icc (-T) T :=
  ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩

lemma u4_clamp_self {T t : ℝ} (ht : t ∈ Set.Icc (-T) T) : max (-T) (min t T) = t := by
  rw [min_eq_left ht.2, max_eq_right ht.1]

section Uniform

variable {d : ℕ} {s : ℝ} {β : ℝ} {ρ : Torus d → ℝ} {φ : Torus d → ℝ}

lemma u4_uniform (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hβ : 0 ≤ β)
    (hρ : SmoothPosDensity ρ) (hφ : Torus.IsSmooth φ) (σ : Bool) (T : ℝ) (hT : 0 < T) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N → ∀ t ∈ Set.Icc (-T) T, |sed_Uerr d s β ρ φ σ N t| ≤ ε := by
  obtain ⟨L, hL⟩ := HRS.MC.SEdge.U3.sed_U3_equilip_proof hd hs0 hs hβ hρ hφ T hT σ
  set a : ℕ → ℝ → ℝ := fun n t => sed_Uerr d s β ρ φ σ (n + 1) (max (-T) (min t T)) with ha
  have hLa : ∀ (n : ℕ) (t t' : ℝ), ‖a n t - a n t'‖ ≤ max L 0 * |t - t'| := by
    intro n t t'
    rw [Real.norm_eq_abs]
    refine (hL (n + 1) (by omega) _ (u4_clamp_mem hT t) _ (u4_clamp_mem hT t')).trans ?_
    calc L * |max (-T) (min t T) - max (-T) (min t' T)|
        ≤ max L 0 * |max (-T) (min t T) - max (-T) (min t' T)| :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _)
      _ ≤ max L 0 * |t - t'| :=
          mul_le_mul_of_nonneg_left (u4_clamp_lip T t t') (le_max_right _ _)
  have hlim : ∀ t ∈ Set.Icc (-T) T, Tendsto (fun n => a n t) atTop (𝓝 ((fun _ : ℝ => (0 : ℝ)) t)) := by
    intro t ht
    simp only [ha, u4_clamp_self ht]
    exact (tendsto_add_atTop_iff_nat (f := fun N => sed_Uerr d s β ρ φ σ N t) 1).2
      (u4_pointwise hd hs0 hs hβ hρ hφ σ t)
  obtain ⟨N₀, hN₀⟩ := HRS.MC.SEdge.U1.sed_U1_uniform_of_equilip_proof hLa hlim ε hε
  refine ⟨N₀ + 1, fun N hN hN1 t ht => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have := hN₀ n (by omega) t ht
  simpa [ha, u4_clamp_self ht] using this

end Uniform

/-! ### The theorem -/

section Final

variable {d : ℕ}

theorem static_edge_char_assembly_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (β : ℝ)
    (hβ : 0 ≤ β) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (φ : Torus d → ℝ)
    (hφ : Torus.IsSmooth φ) :
    let μ := withDensityReal ρ
    let r : Torus d → ℝ := responseInverse (periodicRiesz d s) μ β φ
    let v : ℝ := ∫ x, φ x * r x ∂μ
    let κ : ℝ := ∫ x, r x ^ 3 ∂μ
    0 < v →
    ∀ T : ℝ, 0 < T → ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N → ∀ t : ℝ, t ∈ Set.Icc (-T) T →
      ‖∫ X, Complex.exp (Complex.I * (t : ℂ) *
            ((Real.sqrt N * (pair (empirical X) φ -
              ∫ Y, pair (empirical Y) φ ∂(modulatedGibbs (periodicRiesz d s) N β μ)) : ℝ) : ℂ))
          ∂(modulatedGibbs (periodicRiesz d s) N β μ) -
        Complex.exp (-(v : ℂ) * (t : ℂ) ^ 2 / 2) *
          (1 + (Complex.I * (t : ℂ)) ^ 3 * (κ : ℂ) / (6 * (Real.sqrt N : ℂ)))‖ ≤ ε / Real.sqrt N := by
  dsimp only
  intro _ T hT ε hε
  obtain ⟨N₁, hN₁⟩ := u4_uniform hd hs0 hs hβ hρ hφ true T hT (ε / 2) (by positivity)
  obtain ⟨N₂, hN₂⟩ := u4_uniform hd hs0 hs hβ hρ hφ false T hT (ε / 2) (by positivity)
  refine ⟨max N₁ N₂, fun N hN hN1 t ht => ?_⟩
  have hκ : (∫ x, responseInverse (periodicRiesz d s) (withDensityReal ρ) β φ x ^ 3
      ∂(withDensityReal ρ)) = sed_kappa d s β ρ (fun _ : Fin 1 => φ) 0 0 0 := by
    unfold sed_kappa
    congr 1; funext x; ring
  rw [hκ]
  have hid := u4_identity hd hs0 hs hβ hρ hφ hN1 t
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.2 (by exact_mod_cast hN1)
  have h1 := hN₁ N (le_trans (le_max_left _ _) hN) hN1 t ht
  have h2 := hN₂ N (le_trans (le_max_right _ _) hN) hN1 t ht
  calc _ = ‖(((sed_Uerr d s β ρ φ true N t : ℝ) : ℂ) +
        Complex.I * ((sed_Uerr d s β ρ φ false N t : ℝ) : ℂ)) / (Real.sqrt N : ℂ)‖ :=
        congrArg norm hid
    _ ≤ (ε / 2 + ε / 2) / Real.sqrt N := by
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hsN]
        gcongr
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [Complex.norm_real, Real.norm_eq_abs]; exact h1
        · rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]; exact h2
    _ = ε / Real.sqrt N := by ring_nf

end Final

end HRS.MC.SEdge.U4

end
