import HRS.MS.WadAux4
import HRS.Prob.Gaussian

/-!
# S8.3, packet D2 (part 3): Stein's identity with polynomial growth and gradient smoothing

* `s83_stein`: `E[w_i F(w)] = E[∂_i F(w)]` for the standard Gaussian of `Euc d`, `F ∈ C^1`, under the three
  integrability hypotheses (the Gaussian integration by parts of the Mehler smoothing).
* `s83_G_partial_stein`: for `g ∈ C^1` of weighted growth (`g`, `Dg` with `Wt M`) and `σ ≠ 0`,
  `∂_i (G_{c,σ} g)(x) = (c/σ) ∫ z_i g(cx+σz) dγ(z)`.
* `s83_G_partial_bound`: `|∂_i (G_{c,σ} g)(x)| ≤ (|c|/|σ|) C 2^M mom1 ⟨x⟩^M` where `C` bounds `g`: the smoothing
  estimate `‖∇P_τ g‖_M ≲ τ^{-1/2} ‖g‖_M`, which involves the weighted norm of `g` only.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

/-- Stein's identity for the standard Gaussian of `Euc d` (integrability form). -/
theorem s83_stein {F : Euc d → ℝ} (hF : ContDiff ℝ 1 F) (i : Fin d)
    (h1 : Integrable F (stdGaussian (Euc d)))
    (h2 : Integrable (fun w : Euc d => w i * F w) (stdGaussian (Euc d)))
    (h3 : Integrable (fun w : Euc d => fderiv ℝ F w (EuclideanSpace.single i 1))
      (stdGaussian (Euc d))) :
    ∫ w, w i * F w ∂(stdGaussian (Euc d)) =
      ∫ w, fderiv ℝ F w (EuclideanSpace.single i 1) ∂(stdGaussian (Euc d)) := by
  rw [← map_pi_eq_stdGaussian] at h1 h2 h3 ⊢
  rw [integral_map (by fun_prop) (by
      exact (((continuous_apply i).comp (PiLp.continuous_ofLp 2 _)).mul hF.continuous).aestronglyMeasurable),
    integral_map (by fun_prop) (by
      refine Continuous.aestronglyMeasurable ?_
      exact ((continuous_eval_const (EuclideanSpace.single i (1 : ℝ))).comp
        (hF.continuous_fderiv one_ne_zero)))]
  set Ft : (Fin d → ℝ) → ℝ := fun z => F (WithLp.toLp 2 z) with hFt
  set Ft' : (Fin d → ℝ) → ℝ := fun z => fderiv ℝ F (WithLp.toLp 2 z) (EuclideanSpace.single i 1)
    with hFt'
  have hd : ∀ z : Fin d → ℝ, HasDerivAt (fun x => Ft (Function.update z i x)) (Ft' z) (z i) := by
    intro z
    have hγ : HasDerivAt (fun x : ℝ => (WithLp.toLp 2 z : Euc d) +
        (x - z i) • EuclideanSpace.single i (1 : ℝ)) (EuclideanSpace.single i (1 : ℝ)) (z i) := by
      have := ((hasDerivAt_id (z i)).sub_const (z i)).smul_const (EuclideanSpace.single i (1 : ℝ))
      simpa using this.const_add (WithLp.toLp 2 z : Euc d)
    have hFd : HasFDerivAt F (fderiv ℝ F (WithLp.toLp 2 z)) ((WithLp.toLp 2 z : Euc d) +
        (z i - z i) • EuclideanSpace.single i (1 : ℝ)) := by
      have := (hF.differentiable one_ne_zero (WithLp.toLp 2 z)).hasFDerivAt
      simpa using this
    have := hFd.comp_hasDerivAt (z i) hγ
    have e : (fun x => Ft (Function.update z i x)) = F ∘ fun x : ℝ =>
        (WithLp.toLp 2 z : Euc d) + (x - z i) • EuclideanSpace.single i (1 : ℝ) := by
      funext x
      simp only [hFt, Function.comp]
      congr 1
      ext k
      by_cases hk : k = i
      · subst hk; simp
      · simp [Function.update, hk, EuclideanSpace.single_apply]
    rw [e]
    exact this
  have h1' : Integrable Ft (HRS.Contr.gpi d) := by
    have := (integrable_map_measure (μ := HRS.Contr.gpi d) (f := WithLp.toLp 2)
      (g := F) hF.continuous.aestronglyMeasurable (by fun_prop)).1 h1
    exact this
  have h2' : Integrable (fun z : Fin d → ℝ => z i * Ft z) (HRS.Contr.gpi d) := by
    have := (integrable_map_measure (μ := HRS.Contr.gpi d) (f := WithLp.toLp 2)
      (g := fun w : Euc d => w i * F w) (((continuous_apply i).comp (PiLp.continuous_ofLp 2 _)).mul
        hF.continuous).aestronglyMeasurable (by fun_prop)).1 h2
    exact this
  have h3' : Integrable Ft' (HRS.Contr.gpi d) := by
    have := (integrable_map_measure (μ := HRS.Contr.gpi d) (f := WithLp.toLp 2)
      (g := fun w : Euc d => fderiv ℝ F w (EuclideanSpace.single i 1))
      (((continuous_eval_const (EuclideanSpace.single i (1 : ℝ))).comp
        (hF.continuous_fderiv one_ne_zero)).aestronglyMeasurable) (by fun_prop)).1 h3
    exact this
  exact HRS.Contr.stein_pi i hd h1' h2' h3'

/-- The first-moment constant `∫ ‖z‖ (1 + σ₀‖z‖)^⌈M⌉ dγ`. -/
def mom1 (d : ℕ) (M σ₀ : ℝ) : ℝ := ∫ z : Euc d, ‖z‖ * (1 + σ₀ * ‖z‖) ^ ⌈M⌉₊ ∂(stdGaussian (Euc d))

theorem s83_int_mom1 {σ₀ : ℝ} (hσ : 0 ≤ σ₀) (N : ℕ) :
    Integrable (fun z : Euc d => ‖z‖ * (1 + σ₀ * ‖z‖) ^ N) (stdGaussian (Euc d)) := by
  refine s83_int_of_poly (C := (1 + σ₀) ^ N) (p := N + 1) (by fun_prop) fun z => ?_
  have h0 : 0 ≤ 1 + σ₀ * ‖z‖ := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg h0 _))]
  have h1 : (1 + σ₀ * ‖z‖) ^ N ≤ (1 + σ₀) ^ N * (1 + ‖z‖) ^ N := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ h0 ?_ N
    nlinarith [norm_nonneg z]
  calc ‖z‖ * (1 + σ₀ * ‖z‖) ^ N ≤ (1 + ‖z‖) * ((1 + σ₀) ^ N * (1 + ‖z‖) ^ N) :=
        mul_le_mul (by linarith) h1 (pow_nonneg h0 _) (by positivity)
    _ = (1 + σ₀) ^ N * (1 + ‖z‖) ^ (N + 1) := by ring

theorem s83_mom1_nonneg (M : ℝ) {σ₀ : ℝ} (hσ : 0 ≤ σ₀) : 0 ≤ mom1 d M σ₀ := by
  unfold mom1
  exact integral_nonneg fun z => mul_nonneg (norm_nonneg _) (pow_nonneg (by positivity) _)

/-- Polynomial bound of `f(cx+σz)` in `z`. -/
theorem s83_shift_poly {E : Type*} [NormedAddCommGroup E] {f : Euc d → E} {M C : ℝ} (hM : 0 ≤ M)
    (hw : Wt M C f) (c σ : ℝ) (x z : Euc d) :
    ‖f (c • x + σ • z)‖ ≤
      (C * 2 ^ M * jbracket (c • x) ^ M * (1 + |σ|) ^ ⌈M⌉₊) * (1 + ‖z‖) ^ ⌈M⌉₊ := by
  have hC := hw.nonneg
  refine (s83_wt_poly hM hw (c • x) (σ • z)).trans ?_
  have h1 : (1 + ‖σ • z‖) ^ ⌈M⌉₊ ≤ (1 + |σ|) ^ ⌈M⌉₊ * (1 + ‖z‖) ^ ⌈M⌉₊ := by
    rw [← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    rw [norm_smul, Real.norm_eq_abs]
    nlinarith [norm_nonneg z, abs_nonneg σ]
  have h0 : 0 ≤ C * 2 ^ M * jbracket (c • x) ^ M :=
    mul_nonneg (mul_nonneg hC (by positivity)) (Real.rpow_nonneg (s83_jb_pos _).le _)
  calc C * 2 ^ M * jbracket (c • x) ^ M * (1 + ‖σ • z‖) ^ ⌈M⌉₊
      ≤ C * 2 ^ M * jbracket (c • x) ^ M * ((1 + |σ|) ^ ⌈M⌉₊ * (1 + ‖z‖) ^ ⌈M⌉₊) :=
        mul_le_mul_of_nonneg_left h1 h0
    _ = _ := by ring

/-- **Stein form of the derivative** of a Gaussian average. -/
theorem s83_G_partial_stein {g : Euc d → ℝ} (hg : ContDiff ℝ 1 g) {M C C' : ℝ} (hM : 0 ≤ M)
    (hw : Wt M C g) (hw' : Wt M C' (fderiv ℝ g)) {c σ σ₀ : ℝ} (hc : |c| ≤ 1) (hσ : |σ| ≤ σ₀)
    (hσ0 : σ ≠ 0) (x : Euc d) (i : Fin d) :
    fderiv ℝ (s83_G c σ g) x (EuclideanSpace.single i 1) =
      c / σ * ∫ z, z i * g (c • x + σ • z) ∂(stdGaussian (Euc d)) := by
  have hD := s83_G_hasFDerivAt hg hM hw hw' hc hσ x
  rw [hD.fderiv]
  have hg' : Continuous (fderiv ℝ g) := hg.continuous_fderiv one_ne_zero
  -- Stein for `F z = g (c x + σ z)`
  set F : Euc d → ℝ := fun z => g (c • x + σ • z) with hF
  have hFd : ∀ z, HasFDerivAt F (σ • fderiv ℝ g (c • x + σ • z)) z := by
    intro z
    have h1 : HasFDerivAt (fun z : Euc d => c • x + σ • z) (σ • ContinuousLinearMap.id ℝ (Euc d)) z :=
      ((hasFDerivAt_id z).const_smul σ).const_add (c • x)
    have h2 := (hg.differentiable one_ne_zero (c • x + σ • z)).hasFDerivAt.comp z h1
    have e : (fderiv ℝ g (c • x + σ • z)).comp (σ • ContinuousLinearMap.id ℝ (Euc d)) =
        σ • fderiv ℝ g (c • x + σ • z) := by
      ext v; simp
    rw [e] at h2
    exact h2
  have hFC : ContDiff ℝ 1 F := hg.comp (contDiff_const.add (contDiff_id.const_smul σ))
  have hFder : ∀ z, fderiv ℝ F z (EuclideanSpace.single i 1) =
      σ * fderiv ℝ g (c • x + σ • z) (EuclideanSpace.single i 1) := fun z => by
    rw [(hFd z).fderiv]; simp
  have hI1 : Integrable F (stdGaussian (Euc d)) := s83_int_shift hg.continuous hM hw hσ x
  have hpolyF := s83_shift_poly hM hw c σ x
  have hpolyD := s83_shift_poly hM hw' c σ x
  have hI2 : Integrable (fun w : Euc d => w i * F w) (stdGaussian (Euc d)) := by
    refine s83_int_of_poly (C := C * 2 ^ M * jbracket (c • x) ^ M * (1 + |σ|) ^ ⌈M⌉₊)
      (p := ⌈M⌉₊ + 1)
      ((continuous_apply i |>.comp (PiLp.continuous_ofLp 2 _)).mul
        (hg.continuous.comp (continuous_const.add (continuous_const_smul σ)))).aestronglyMeasurable
      fun z => ?_
    rw [norm_mul]
    have hz : ‖z i‖ ≤ 1 + ‖z‖ := by
      have := PiLp.norm_apply_le z i
      linarith [norm_nonneg z]
    have hpF := hpolyF z
    have hK : 0 ≤ C * 2 ^ M * jbracket (c • x) ^ M * (1 + |σ|) ^ ⌈M⌉₊ := by
      have hC := hw.nonneg
      exact mul_nonneg (mul_nonneg (mul_nonneg hC (by positivity)) (Real.rpow_nonneg (s83_jb_pos _).le _))
        (by positivity)
    calc ‖z i‖ * ‖F z‖ ≤ (1 + ‖z‖) *
          ((C * 2 ^ M * jbracket (c • x) ^ M * (1 + |σ|) ^ ⌈M⌉₊) * (1 + ‖z‖) ^ ⌈M⌉₊) :=
          mul_le_mul hz hpF (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hI3 : Integrable (fun w : Euc d => fderiv ℝ F w (EuclideanSpace.single i 1))
      (stdGaussian (Euc d)) := by
    have hcont : Continuous fun w : Euc d => fderiv ℝ F w (EuclideanSpace.single i 1) :=
      (continuous_eval_const (EuclideanSpace.single i (1 : ℝ))).comp (hFC.continuous_fderiv one_ne_zero)
    refine s83_int_of_poly (C := |σ| * (C' * 2 ^ M * jbracket (c • x) ^ M * (1 + |σ|) ^ ⌈M⌉₊))
      (p := ⌈M⌉₊) hcont.aestronglyMeasurable fun z => ?_
    rw [hFder z, norm_mul, Real.norm_eq_abs]
    have h4 : ‖fderiv ℝ g (c • x + σ • z) (EuclideanSpace.single i 1)‖ ≤
        ‖fderiv ℝ g (c • x + σ • z)‖ := by
      have := (fderiv ℝ g (c • x + σ • z)).le_opNorm (EuclideanSpace.single i (1 : ℝ))
      simpa using this
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (h4.trans (hpolyD z)) (abs_nonneg σ)
  have hS := s83_stein hFC i hI1 hI2 hI3
  have hint : (∫ z, fderiv ℝ g (c • x + σ • z) ∂(stdGaussian (Euc d))) (EuclideanSpace.single i 1) =
      ∫ z, fderiv ℝ g (c • x + σ • z) (EuclideanSpace.single i 1) ∂(stdGaussian (Euc d)) := by
    have hI : Integrable (fun z : Euc d => fderiv ℝ g (c • x + σ • z)) (stdGaussian (Euc d)) :=
      s83_int_shift hg' hM hw' hσ x
    exact (ContinuousLinearMap.integral_apply hI _)
  show (c • s83_G c σ (fderiv ℝ g) x) (EuclideanSpace.single i 1) = _
  simp only [ContinuousLinearMap.smul_apply, s83_G]
  rw [hint]
  simp only [hFder] at hS
  rw [integral_const_mul] at hS
  simp only [hF] at hS
  rw [smul_eq_mul, hS]
  field_simp

/-- **Gradient smoothing of the Gaussian average**: `|∂_i G_{c,σ} g(x)| ≤ (|c|/|σ|) C 2^M mom1 ⟨x⟩^M`. -/
theorem s83_G_partial_bound {g : Euc d → ℝ} (hg : ContDiff ℝ 1 g) {M C C' : ℝ} (hM : 0 ≤ M)
    (hw : Wt M C g) (hw' : Wt M C' (fderiv ℝ g)) {c σ σ₀ : ℝ} (hc : |c| ≤ 1) (hσ : |σ| ≤ σ₀)
    (hσ0 : σ ≠ 0) (x : Euc d) (i : Fin d) :
    |fderiv ℝ (s83_G c σ g) x (EuclideanSpace.single i 1)| ≤
      |c| / |σ| * (C * 2 ^ M * mom1 d M σ₀) * jbracket x ^ M := by
  have hC := hw.nonneg
  have hσ00 : 0 ≤ σ₀ := (abs_nonneg _).trans hσ
  rw [s83_G_partial_stein hg hM hw hw' hc hσ hσ0 x i, abs_mul, abs_div]
  have h1 : |∫ z, z i * g (c • x + σ • z) ∂(stdGaussian (Euc d))| ≤
      C * 2 ^ M * jbracket x ^ M * mom1 d M σ₀ := by
    rw [← Real.norm_eq_abs]
    have hb : ∀ z : Euc d, ‖z i * g (c • x + σ • z)‖ ≤
        C * 2 ^ M * jbracket x ^ M * (‖z‖ * (1 + σ₀ * ‖z‖) ^ ⌈M⌉₊) := by
      intro z
      rw [norm_mul]
      have hz : ‖z i‖ ≤ ‖z‖ := PiLp.norm_apply_le z i
      have h2 := (hw (c • x + σ • z))
      have h3 := s83_jb_add_rpow hM (c • x) (σ • z)
      have h4 : jbracket (c • x) ^ M ≤ jbracket x ^ M := s83_jb_smul_le_rpow hM hc x
      have h5 := s83_jb_smul_poly hM hσ z
      have h6 : ‖g (c • x + σ • z)‖ ≤ C * 2 ^ M * jbracket x ^ M * (1 + σ₀ * ‖z‖) ^ ⌈M⌉₊ := by
        refine h2.trans ?_
        calc C * jbracket (c • x + σ • z) ^ M
            ≤ C * (2 ^ M * (jbracket (c • x) ^ M * jbracket (σ • z) ^ M)) :=
              mul_le_mul_of_nonneg_left h3 hC
          _ ≤ C * (2 ^ M * (jbracket x ^ M * (1 + σ₀ * ‖z‖) ^ ⌈M⌉₊)) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
                (mul_le_mul h4 h5 (Real.rpow_nonneg (s83_jb_pos _).le _)
                  (Real.rpow_nonneg (s83_jb_pos _).le _)) (by positivity)) hC
          _ = _ := by ring
      calc ‖z i‖ * ‖g (c • x + σ • z)‖ ≤ ‖z‖ * (C * 2 ^ M * jbracket x ^ M * (1 + σ₀ * ‖z‖) ^ ⌈M⌉₊) :=
            mul_le_mul hz h6 (norm_nonneg _) (norm_nonneg _)
        _ = _ := by ring
    have hbi : Integrable (fun z : Euc d => C * 2 ^ M * jbracket x ^ M *
        (‖z‖ * (1 + σ₀ * ‖z‖) ^ ⌈M⌉₊)) (stdGaussian (Euc d)) :=
      (s83_int_mom1 hσ00 ⌈M⌉₊).const_mul _
    refine (norm_integral_le_of_norm_le hbi (Eventually.of_forall hb)).trans ?_
    rw [integral_const_mul]
    unfold mom1
    exact le_of_eq (by ring)
  have hcs : |c| / |σ| * |∫ z, z i * g (c • x + σ • z) ∂(stdGaussian (Euc d))| ≤
      |c| / |σ| * (C * 2 ^ M * jbracket x ^ M * mom1 d M σ₀) :=
    mul_le_mul_of_nonneg_left h1 (by positivity)
  calc |c| / |σ| * |∫ z, z i * g (c • x + σ • z) ∂(stdGaussian (Euc d))|
      ≤ |c| / |σ| * (C * 2 ^ M * jbracket x ^ M * mom1 d M σ₀) := hcs
    _ = _ := by ring

end HRS.MS.Wad
