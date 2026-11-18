import HRS.MS.WadAux11
import HRS.MS.WadAux2

/-!
# S8.3, packet D2 (part 7): Lipschitz smoothing of the Gaussian average for merely continuous data

`s83_G_lip`: for `g` continuous with `|g| ≤ C⟨·⟩^M`, `0 < |σ| ≤ σ₀`, `|c| ≤ 1`:
`|G_{c,σ} g(x') - G_{c,σ} g(x)| ≤ C 2^M ⟨x⟩^M √(mom(2M,σ₀)) κ e^{κ²/2}`, `κ = (|c|/|σ|)‖x'-x‖`.
Proof: Cameron-Martin (`s83_cm_integral`) turns the difference into `∫ F (E_k - 1) dγ`; Cauchy-Schwarz and
`∫(E_k-1)² = e^{‖k‖²} - 1 ≤ ‖k‖² e^{‖k‖²}`.  This is the equicontinuity estimate behind the compactness of
`χ_R P_t` on `C_M`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

/-- Cauchy-Schwarz for `L²(γ)` functions. -/
theorem s83_cs {f h : Euc d → ℝ} (hf : Integrable (fun u => f u ^ 2) (stdGaussian (Euc d)))
    (hh : Integrable (fun u => h u ^ 2) (stdGaussian (Euc d)))
    (hfh : Integrable (fun u => f u * h u) (stdGaussian (Euc d))) :
    (∫ u, f u * h u ∂(stdGaussian (Euc d))) ^ 2 ≤
      (∫ u, f u ^ 2 ∂(stdGaussian (Euc d))) * ∫ u, h u ^ 2 ∂(stdGaussian (Euc d)) := by
  set A := ∫ u, f u ^ 2 ∂(stdGaussian (Euc d))
  set B := ∫ u, h u ^ 2 ∂(stdGaussian (Euc d))
  set I := ∫ u, f u * h u ∂(stdGaussian (Euc d))
  have key : ∀ t : ℝ, 0 ≤ A * t * t + (2 * I) * t + B := by
    intro t
    have h0 : 0 ≤ ∫ u, (t * f u + h u) ^ 2 ∂(stdGaussian (Euc d)) :=
      integral_nonneg fun u => sq_nonneg _
    have e : ∀ u : Euc d, (t * f u + h u) ^ 2 =
        (t * t) * f u ^ 2 + (2 * t) * (f u * h u) + h u ^ 2 := fun u => by ring
    simp only [e] at h0
    have i1 : Integrable (fun u : Euc d => t * t * f u ^ 2) (stdGaussian (Euc d)) := hf.const_mul _
    have i2 : Integrable (fun u : Euc d => 2 * t * (f u * h u)) (stdGaussian (Euc d)) := hfh.const_mul _
    have i3 : Integrable (fun u : Euc d => t * t * f u ^ 2 + 2 * t * (f u * h u))
        (stdGaussian (Euc d)) := i1.add i2
    rw [integral_add i3 hh, integral_add i1 i2, integral_const_mul, integral_const_mul] at h0
    nlinarith [h0]
  have key' : ∀ t : ℝ, 0 ≤ A * (t * t) + (2 * I) * t + B := fun t => by
    have := key t; nlinarith [this]
  have := discrim_le_zero key'
  unfold discrim at this
  nlinarith [this]

theorem s83_exp_sub_one_le (s : ℝ) (hs : 0 ≤ s) : Real.exp s - 1 ≤ s * Real.exp s := by
  have h := Real.add_one_le_exp (-s)
  have h2 : Real.exp (-s) * Real.exp s = 1 := by rw [← Real.exp_add]; simp
  nlinarith [Real.exp_pos s, h, h2, mul_le_mul_of_nonneg_right h (Real.exp_pos s).le]

theorem s83_rpow_sq {y : ℝ} (hy : 0 ≤ y) (M : ℝ) : (y ^ M) ^ 2 = y ^ (2 * M) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hy]; congr 1; push_cast; ring

theorem s83_amgm (a b : ℝ) : |a| * |b| ≤ 1 / 2 * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (|a| - |b|), sq_abs a, sq_abs b]

/-- **Lipschitz smoothing** of the Gaussian average of a continuous function of weighted growth. -/
theorem s83_G_lip {g : Euc d → ℝ} (hg : Continuous g) {M C : ℝ} (hM : 0 ≤ M) (hw : Wt M C g)
    {c σ σ₀ : ℝ} (hc : |c| ≤ 1) (hσ : |σ| ≤ σ₀) (hσ0 : σ ≠ 0) (x x' : Euc d) :
    |s83_G c σ g x' - s83_G c σ g x| ≤
      C * 2 ^ M * jbracket x ^ M * Real.sqrt (mom d (2 * M) σ₀) *
        ((|c| / |σ|) * ‖x' - x‖) * Real.exp (((|c| / |σ|) * ‖x' - x‖) ^ 2 / 2) := by
  have hC := hw.nonneg
  have hσ00 : 0 ≤ σ₀ := (abs_nonneg _).trans hσ
  set F : Euc d → ℝ := fun u => g (c • x + σ • u) with hF
  have hFc : Continuous F := hg.comp (continuous_const.add (continuous_const_smul σ))
  set k : Euc d := (c / σ) • (x' - x) with hk
  have hkn : ‖k‖ = (|c| / |σ|) * ‖x' - x‖ := by
    rw [hk, norm_smul, Real.norm_eq_abs, abs_div]
  have hshift : ∀ u : Euc d, c • x' + σ • u = c • x + σ • (u + k) := by
    intro u
    rw [hk, smul_add, smul_smul, mul_div_cancel₀ _ hσ0, smul_sub]
    abel
  have hGx' : s83_G c σ g x' = ∫ u, F (u + k) ∂(stdGaussian (Euc d)) := by
    unfold s83_G; simp only [hshift, hF]
  have hGx : s83_G c σ g x = ∫ u, F u ∂(stdGaussian (Euc d)) := rfl
  -- pointwise bound for `F`
  set K0 : ℝ := C * 2 ^ M * jbracket x ^ M with hK0
  have hK00 : 0 ≤ K0 :=
    mul_nonneg (mul_nonneg hC (by positivity)) (Real.rpow_nonneg (s83_jb_pos x).le _)
  have hFb : ∀ u, |F u| ≤ K0 * jbracket (σ • u) ^ M := by
    intro u
    have h1 := hw (c • x + σ • u)
    have h2 := s83_jb_add_rpow hM (c • x) (σ • u)
    have h3 : jbracket (c • x) ^ M ≤ jbracket x ^ M := s83_jb_smul_le_rpow hM hc x
    have h4 : 0 ≤ jbracket (σ • u) ^ M := Real.rpow_nonneg (s83_jb_pos _).le _
    rw [Real.norm_eq_abs] at h1
    refine h1.trans ?_
    calc C * jbracket (c • x + σ • u) ^ M ≤ C * (2 ^ M * (jbracket (c • x) ^ M * jbracket (σ • u) ^ M)) :=
          mul_le_mul_of_nonneg_left h2 hC
      _ ≤ C * (2 ^ M * (jbracket x ^ M * jbracket (σ • u) ^ M)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 h4)
            (by positivity)) hC
      _ = K0 * jbracket (σ • u) ^ M := by rw [hK0]; ring
  have hFsq : ∀ u, F u ^ 2 ≤ K0 ^ 2 * jbracket (σ • u) ^ (2 * M) := by
    intro u
    have := hFb u
    have h0 : 0 ≤ jbracket (σ • u) ^ M := Real.rpow_nonneg (s83_jb_pos _).le _
    calc F u ^ 2 = |F u| ^ 2 := (sq_abs _).symm
      _ ≤ (K0 * jbracket (σ • u) ^ M) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = K0 ^ 2 * jbracket (σ • u) ^ (2 * M) := by
          rw [mul_pow, s83_rpow_sq (s83_jb_pos _).le]
  have hM2 : 0 ≤ 2 * M := by linarith
  have hint2 : Integrable (fun u : Euc d => jbracket (σ • u) ^ (2 * M)) (stdGaussian (Euc d)) :=
    s83_int_jb_smul hM2 hσ
  have hF2 : Integrable (fun u => F u ^ 2) (stdGaussian (Euc d)) := by
    refine (hint2.const_mul (K0 ^ 2)).mono' (hFc.pow 2).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hFsq u
  have hFi : Integrable F (stdGaussian (Euc d)) :=
    ((s83_int_jb_smul (M := M) hM hσ).const_mul K0).mono' hFc.aestronglyMeasurable
      (Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hFb u)
  have hA : ∫ u, F u ^ 2 ∂(stdGaussian (Euc d)) ≤ K0 ^ 2 * mom d (2 * M) σ₀ := by
    calc ∫ u, F u ^ 2 ∂(stdGaussian (Euc d)) ≤ ∫ u, K0 ^ 2 * jbracket (σ • u) ^ (2 * M)
          ∂(stdGaussian (Euc d)) := integral_mono hF2 (hint2.const_mul _) hFsq
      _ = K0 ^ 2 * ∫ u, jbracket (σ • u) ^ (2 * M) ∂(stdGaussian (Euc d)) := integral_const_mul _ _
      _ ≤ K0 ^ 2 * mom d (2 * M) σ₀ :=
          mul_le_mul_of_nonneg_left (s83_int_jb_smul_le hM2 hσ) (sq_nonneg _)
  -- Cameron-Martin and Cauchy-Schwarz
  have hEc : Continuous (s83_E k) := by unfold s83_E; fun_prop
  have hE1 := s83_integrable_E k
  have hE2 := s83_integrable_E_sq k
  have hh2 : Integrable (fun u => (s83_E k u - 1) ^ 2) (stdGaussian (Euc d)) := by
    have e : ∀ u : Euc d, (s83_E k u - 1) ^ 2 = s83_E k u ^ 2 - 2 * s83_E k u + 1 := fun u => by ring
    simp only [e]
    exact (hE2.sub (hE1.const_mul 2)).add (integrable_const _)
  have hfh : Integrable (fun u => F u * (s83_E k u - 1)) (stdGaussian (Euc d)) := by
    refine ((hF2.add hh2).const_mul (1 / 2)).mono' (hFc.mul (hEc.sub continuous_const)).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact s83_amgm _ _
  have hEF : Integrable (fun u => s83_E k u * F u) (stdGaussian (Euc d)) := by
    refine ((hF2.add hE2).const_mul (1 / 2)).mono' ((hEc.mul hFc)).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have := s83_amgm (s83_E k u) (F u)
    simp only [Pi.add_apply]
    linarith [this]
  have hdiff : s83_G c σ g x' - s83_G c σ g x =
      ∫ u, F u * (s83_E k u - 1) ∂(stdGaussian (Euc d)) := by
    rw [hGx', hGx, s83_cm_integral hFc k, ← integral_sub hEF hFi]
    congr 1; funext u; ring
  have hCS := s83_cs hF2 hh2 hfh
  rw [s83_integral_E_sub_one_sq] at hCS
  have hB0 : 0 ≤ Real.exp (‖k‖ ^ 2) - 1 := by
    have := Real.add_one_le_exp (‖k‖ ^ 2)
    nlinarith [sq_nonneg ‖k‖]
  have hB1 := s83_exp_sub_one_le (‖k‖ ^ 2) (sq_nonneg _)
  have hA0 : 0 ≤ ∫ u, F u ^ 2 ∂(stdGaussian (Euc d)) := integral_nonneg fun u => sq_nonneg _
  have hmom : 0 ≤ mom d (2 * M) σ₀ := s83_mom_nonneg _ _ hσ00
  have hsq : (s83_G c σ g x' - s83_G c σ g x) ^ 2 ≤
      K0 ^ 2 * mom d (2 * M) σ₀ * (‖k‖ ^ 2 * Real.exp (‖k‖ ^ 2)) :=
    by
      rw [hdiff]
      exact hCS.trans (mul_le_mul hA hB1 hB0 (mul_nonneg (sq_nonneg _) hmom))
  set L : ℝ := K0 * Real.sqrt (mom d (2 * M) σ₀) * ‖k‖ * Real.exp (‖k‖ ^ 2 / 2) with hL
  have hL2 : L ^ 2 = K0 ^ 2 * mom d (2 * M) σ₀ * (‖k‖ ^ 2 * Real.exp (‖k‖ ^ 2)) := by
    have e1 : Real.sqrt (mom d (2 * M) σ₀) ^ 2 = mom d (2 * M) σ₀ := Real.sq_sqrt hmom
    have e2 : Real.exp (‖k‖ ^ 2 / 2) ^ 2 = Real.exp (‖k‖ ^ 2) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [hL]
    calc (K0 * Real.sqrt (mom d (2 * M) σ₀) * ‖k‖ * Real.exp (‖k‖ ^ 2 / 2)) ^ 2
        = K0 ^ 2 * Real.sqrt (mom d (2 * M) σ₀) ^ 2 * ‖k‖ ^ 2 * Real.exp (‖k‖ ^ 2 / 2) ^ 2 := by ring
      _ = _ := by rw [e1, e2]; ring
  have hL0 : 0 ≤ L := by
    rw [hL]; exact mul_nonneg (mul_nonneg (mul_nonneg hK00 (Real.sqrt_nonneg _)) (norm_nonneg _))
      (Real.exp_pos _).le
  have hsq' : (s83_G c σ g x' - s83_G c σ g x) ^ 2 ≤ L ^ 2 := by rw [hL2]; exact hsq
  have := abs_le_of_sq_le_sq hsq' hL0
  refine this.trans (le_of_eq ?_)
  rw [hL, hkn, hK0]

end HRS.MS.Wad
