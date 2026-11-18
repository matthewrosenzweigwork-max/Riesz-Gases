import HRS.MS.WadAux15
import HRS.MS.WadAux12
import HRS.MS.WadAux5

/-!
# S8.3, packet D2'' (Route A): `C¹` smoothing of the Gaussian average of merely continuous data

For `g` continuous with `|g| ≤ C⟨·⟩^M`, `σ ≠ 0`, `|σ| ≤ σ₀`, the map `x ↦ G_{c,σ} g (x)` is differentiable with
`D G g (x₀) = (c/σ) ⟨S(x₀), ·⟩`, `S(x₀) = ∫ g(c x₀ + σ u) u dγ(u)` (Stein), and `x ↦ S(x)` is continuous.
Proof: Cameron-Martin gives `G g(x) - G g(x₀) - ⟨D, x-x₀⟩ = ∫ F (E_k - 1 - ⟨·,k⟩) dγ`, `k = (c/σ)(x-x₀)`;
Cauchy-Schwarz and the exact Gaussian moment `∫(E_k - 1 - ⟨u,k⟩)² = e^{‖k‖²} - 1 - ‖k‖²` give the
`O(‖k‖²)` remainder.  This replaces the `C¹` hypothesis on the datum of `s83_G_hasFDerivAt`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s84_int_inner (k : Euc d) :
    Integrable (fun u : Euc d => ⟪u, k⟫) (stdGaussian (Euc d)) := by
  refine s83_int_of_poly (C := ‖k‖) (p := 1) (by fun_prop) fun u => ?_
  rw [Real.norm_eq_abs, pow_one]
  have := abs_real_inner_le_norm u k
  nlinarith [norm_nonneg u, norm_nonneg k]

theorem s84_integral_inner (k : Euc d) : ∫ u, ⟪u, k⟫ ∂(stdGaussian (Euc d)) = 0 := by
  have h := integral_strongDual_stdGaussian (E := Euc d) (innerSL ℝ k)
  simpa [innerSL_apply_apply ℝ, real_inner_comm] using h

/-- `∫ ⟨u,k⟩² dγ = ‖k‖²`. -/
theorem s84_int_inner_sq (k : Euc d) :
    ∫ u, ⟪u, k⟫ ^ 2 ∂(stdGaussian (Euc d)) = ‖k‖ ^ 2 := by
  have h := variance_dual_stdGaussian (E := Euc d) (innerSL ℝ k)
  have hm : AEMeasurable (⇑(innerSL ℝ k)) (stdGaussian (Euc d)) :=
    (innerSL ℝ k).continuous.aemeasurable
  have h0 : (stdGaussian (Euc d))[⇑(innerSL ℝ k)] = 0 := integral_strongDual_stdGaussian _
  rw [variance_of_integral_eq_zero hm h0, innerSL_apply_norm] at h
  simpa [innerSL_apply_apply ℝ, real_inner_comm] using h

theorem s84_int_inner_sq_integrable (k : Euc d) :
    Integrable (fun u : Euc d => ⟪u, k⟫ ^ 2) (stdGaussian (Euc d)) := by
  refine s83_int_of_poly (C := ‖k‖ ^ 2) (p := 2) (by fun_prop) fun u => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have := abs_real_inner_le_norm u k
  have h2 : ⟪u, k⟫ ^ 2 ≤ (‖u‖ * ‖k‖) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) this 2
  calc ⟪u, k⟫ ^ 2 ≤ (‖u‖ * ‖k‖) ^ 2 := h2
    _ = ‖k‖ ^ 2 * ‖u‖ ^ 2 := by ring
    _ ≤ ‖k‖ ^ 2 * (1 + ‖u‖) ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        nlinarith [norm_nonneg u]

/-- `∫ E_k(u) ⟨u,k⟩ dγ = ‖k‖²`. -/
theorem s84_int_E_inner (k : Euc d) :
    ∫ u, s83_E k u * ⟪u, k⟫ ∂(stdGaussian (Euc d)) = ‖k‖ ^ 2 := by
  have h := s83_cm_integral (d := d) (F := fun u => ⟪u, k⟫) (by fun_prop) k
  rw [← h]
  have e : ∀ u : Euc d, ⟪u + k, k⟫ = ⟪u, k⟫ + ‖k‖ ^ 2 := fun u => by
    rw [inner_add_left, real_inner_self_eq_norm_sq]
  simp only [e]
  rw [integral_add (s84_int_inner k) (integrable_const _), s84_integral_inner]
  simp

theorem s84_integrable_E_inner (k : Euc d) :
    Integrable (fun u => s83_E k u * ⟪u, k⟫) (stdGaussian (Euc d)) := by
  have hEc : Continuous (s83_E k) := by unfold s83_E; fun_prop
  refine (((s83_integrable_E_sq k).add (s84_int_inner_sq_integrable k)).const_mul (1 / 2)).mono'
    (hEc.mul (by fun_prop : Continuous fun u : Euc d => ⟪u, k⟫)).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have := s83_amgm (s83_E k u) ⟪u, k⟫
  simp only [Pi.add_apply]
  linarith [this]

/-- The exact `L²(γ)` norm of the first-order Cameron-Martin remainder. -/
theorem s84_int_R_sq (k : Euc d) :
    ∫ u, (s83_E k u - 1 - ⟪u, k⟫) ^ 2 ∂(stdGaussian (Euc d)) =
      Real.exp (‖k‖ ^ 2) - 1 - ‖k‖ ^ 2 := by
  have i1 := s83_integrable_E k
  have i2 := s83_integrable_E_sq k
  have i3 := s84_int_inner k
  have i4 := s84_int_inner_sq_integrable k
  have i5 := s84_integrable_E_inner k
  have e : ∀ u : Euc d, (s83_E k u - 1 - ⟪u, k⟫) ^ 2 =
      ((s83_E k u ^ 2 - 2 * s83_E k u) + 1) +
        ((⟪u, k⟫ ^ 2 - 2 * (s83_E k u * ⟪u, k⟫)) + 2 * ⟪u, k⟫) := fun u => by ring
  simp only [e]
  have iA1 : Integrable (fun u : Euc d => s83_E k u ^ 2 - 2 * s83_E k u) (stdGaussian (Euc d)) :=
    i2.sub (i1.const_mul 2)
  have iA : Integrable (fun u : Euc d => (s83_E k u ^ 2 - 2 * s83_E k u) + 1) (stdGaussian (Euc d)) :=
    iA1.add (integrable_const _)
  have iB1 : Integrable (fun u : Euc d => ⟪u, k⟫ ^ 2 - 2 * (s83_E k u * ⟪u, k⟫)) (stdGaussian (Euc d)) :=
    i4.sub (i5.const_mul 2)
  have iB : Integrable (fun u : Euc d => (⟪u, k⟫ ^ 2 - 2 * (s83_E k u * ⟪u, k⟫)) + 2 * ⟪u, k⟫)
      (stdGaussian (Euc d)) := iB1.add (i3.const_mul 2)
  rw [integral_add iA iB, integral_add iA1 (integrable_const _),
    integral_sub i2 (i1.const_mul 2), integral_add iB1 (i3.const_mul 2),
    integral_sub i4 (i5.const_mul 2), integral_const_mul, integral_const_mul, integral_const_mul,
    s83_integral_E_sq, s83_integral_E, s84_int_inner_sq, s84_int_E_inner, s84_integral_inner,
    integral_const]
  simp
  ring

theorem s84_int_R_sq_le (k : Euc d) (hk : ‖k‖ ≤ 1) :
    ∫ u, (s83_E k u - 1 - ⟪u, k⟫) ^ 2 ∂(stdGaussian (Euc d)) ≤ (‖k‖ ^ 2) ^ 2 := by
  rw [s84_int_R_sq]
  have hp : |‖k‖ ^ 2| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [norm_nonneg k]
  have := Real.abs_exp_sub_one_sub_id_le hp
  have h2 := (abs_le.1 this).2
  linarith

theorem s84_R_sq_integrable (k : Euc d) :
    Integrable (fun u => (s83_E k u - 1 - ⟪u, k⟫) ^ 2) (stdGaussian (Euc d)) := by
  have hEc : Continuous (s83_E k) := by unfold s83_E; fun_prop
  refine (((s83_integrable_E_sq k).add (integrable_const (1 : ℝ))).add
    (s84_int_inner_sq_integrable k)).const_mul 3 |>.mono'
    ((hEc.sub continuous_const).sub (by fun_prop : Continuous fun u : Euc d => ⟪u, k⟫) |>.pow 2).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simp only [Pi.add_apply]
  nlinarith [sq_nonneg (s83_E k u + 1), sq_nonneg (⟪u, k⟫ - 1), sq_nonneg (s83_E k u + ⟪u, k⟫)]

/-- The shifted datum `F(u) = g(c x₀ + σ u)` is square integrable with the weighted moment bound. -/
theorem s84_F_sq {g : Euc d → ℝ} (hg : Continuous g) {M C : ℝ} (hM : 0 ≤ M) (hw : Wt M C g)
    {c σ σ₀ : ℝ} (hc : |c| ≤ 1) (hσ : |σ| ≤ σ₀) (x₀ : Euc d) :
    Integrable (fun u : Euc d => g (c • x₀ + σ • u) ^ 2) (stdGaussian (Euc d)) ∧
    ∫ u, g (c • x₀ + σ • u) ^ 2 ∂(stdGaussian (Euc d)) ≤
      (C * 2 ^ M * jbracket x₀ ^ M) ^ 2 * mom d (2 * M) σ₀ := by
  have hC := hw.nonneg
  have hσ00 : 0 ≤ σ₀ := (abs_nonneg _).trans hσ
  set F : Euc d → ℝ := fun u => g (c • x₀ + σ • u) with hF
  have hFc : Continuous F := hg.comp (continuous_const.add (continuous_const_smul σ))
  set K0 : ℝ := C * 2 ^ M * jbracket x₀ ^ M with hK0
  have hK00 : 0 ≤ K0 :=
    mul_nonneg (mul_nonneg hC (by positivity)) (Real.rpow_nonneg (s83_jb_pos x₀).le _)
  have hFb : ∀ u, |F u| ≤ K0 * jbracket (σ • u) ^ M := by
    intro u
    have h1 := hw (c • x₀ + σ • u)
    have h2 := s83_jb_add_rpow hM (c • x₀) (σ • u)
    have h3 : jbracket (c • x₀) ^ M ≤ jbracket x₀ ^ M := s83_jb_smul_le_rpow hM hc x₀
    have h4 : 0 ≤ jbracket (σ • u) ^ M := Real.rpow_nonneg (s83_jb_pos _).le _
    rw [Real.norm_eq_abs] at h1
    refine h1.trans ?_
    calc C * jbracket (c • x₀ + σ • u) ^ M ≤ C * (2 ^ M * (jbracket (c • x₀) ^ M * jbracket (σ • u) ^ M)) :=
          mul_le_mul_of_nonneg_left h2 hC
      _ ≤ C * (2 ^ M * (jbracket x₀ ^ M * jbracket (σ • u) ^ M)) :=
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
  refine ⟨hF2, ?_⟩
  calc ∫ u, F u ^ 2 ∂(stdGaussian (Euc d)) ≤ ∫ u, K0 ^ 2 * jbracket (σ • u) ^ (2 * M)
        ∂(stdGaussian (Euc d)) := integral_mono hF2 (hint2.const_mul _) hFsq
    _ = K0 ^ 2 * ∫ u, jbracket (σ • u) ^ (2 * M) ∂(stdGaussian (Euc d)) := integral_const_mul _ _
    _ ≤ K0 ^ 2 * mom d (2 * M) σ₀ :=
        mul_le_mul_of_nonneg_left (s83_int_jb_smul_le hM2 hσ) (sq_nonneg _)

/-- **First-order remainder** of the Gaussian average of a continuous datum. -/
theorem s84_G_remainder {g : Euc d → ℝ} (hg : Continuous g) {M C : ℝ} (hM : 0 ≤ M) (hw : Wt M C g)
    {c σ σ₀ : ℝ} (hc : |c| ≤ 1) (hσ : |σ| ≤ σ₀) (hσ0 : σ ≠ 0) (x x₀ : Euc d)
    (hk : ‖(c / σ) • (x - x₀)‖ ≤ 1) :
    |s83_G c σ g x - s83_G c σ g x₀ -
        ∫ u, ⟪u, (c / σ) • (x - x₀)⟫ * g (c • x₀ + σ • u) ∂(stdGaussian (Euc d))| ≤
      C * 2 ^ M * jbracket x₀ ^ M * Real.sqrt (mom d (2 * M) σ₀) * ‖(c / σ) • (x - x₀)‖ ^ 2 := by
  have hC := hw.nonneg
  have hσ00 : 0 ≤ σ₀ := (abs_nonneg _).trans hσ
  set k : Euc d := (c / σ) • (x - x₀) with hkdef
  set F : Euc d → ℝ := fun u => g (c • x₀ + σ • u) with hF
  have hFc : Continuous F := hg.comp (continuous_const.add (continuous_const_smul σ))
  obtain ⟨hF2, hA⟩ := s84_F_sq hg hM hw hc hσ x₀
  have hFi : Integrable F (stdGaussian (Euc d)) := s83_int_shift hg hM hw hσ x₀
  have hshift : ∀ u : Euc d, c • x + σ • u = c • x₀ + σ • (u + k) := by
    intro u
    rw [hkdef, smul_add, smul_smul, mul_div_cancel₀ _ hσ0, smul_sub]
    abel
  have hGx : s83_G c σ g x = ∫ u, F (u + k) ∂(stdGaussian (Euc d)) := by
    unfold s83_G; simp only [hshift, hF]
  have hGx0 : s83_G c σ g x₀ = ∫ u, F u ∂(stdGaussian (Euc d)) := rfl
  have hEc : Continuous (s83_E k) := by unfold s83_E; fun_prop
  have hE1 := s83_integrable_E k
  have hE2 := s83_integrable_E_sq k
  have hl1 := s84_int_inner k
  have hl2 := s84_int_inner_sq_integrable k
  have hEF : Integrable (fun u => s83_E k u * F u) (stdGaussian (Euc d)) := by
    refine ((hF2.add hE2).const_mul (1 / 2)).mono' ((hEc.mul hFc)).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have := s83_amgm (s83_E k u) (F u)
    simp only [Pi.add_apply]
    linarith [this]
  have hlF : Integrable (fun u => ⟪u, k⟫ * F u) (stdGaussian (Euc d)) := by
    refine ((hF2.add hl2).const_mul (1 / 2)).mono'
      ((by fun_prop : Continuous fun u : Euc d => ⟪u, k⟫).mul hFc).aestronglyMeasurable
      (Eventually.of_forall fun u => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have := s83_amgm ⟪u, k⟫ (F u)
    simp only [Pi.add_apply]
    nlinarith [this]
  have hEFF : Integrable (fun u => s83_E k u * F u - F u) (stdGaussian (Euc d)) := hEF.sub hFi
  have hfh : Integrable (fun u => F u * (s83_E k u - 1 - ⟪u, k⟫)) (stdGaussian (Euc d)) := by
    have : (fun u => F u * (s83_E k u - 1 - ⟪u, k⟫)) =
        fun u => (s83_E k u * F u - F u) - ⟪u, k⟫ * F u := funext fun u => by ring
    rw [this]
    exact hEFF.sub hlF
  have hdiff : s83_G c σ g x - s83_G c σ g x₀ - ∫ u, ⟪u, k⟫ * F u ∂(stdGaussian (Euc d)) =
      ∫ u, F u * (s83_E k u - 1 - ⟪u, k⟫) ∂(stdGaussian (Euc d)) := by
    have e : (fun u => F u * (s83_E k u - 1 - ⟪u, k⟫)) =
        fun u => (s83_E k u * F u - F u) - ⟪u, k⟫ * F u := funext fun u => by ring
    rw [e, integral_sub hEFF hlF, integral_sub hEF hFi, hGx, hGx0, s83_cm_integral hFc k]
  have hh2 := s84_R_sq_integrable k
  have hCS := s83_cs hF2 hh2 hfh
  have hRle := s84_int_R_sq_le k hk
  have hA0 : 0 ≤ ∫ u, F u ^ 2 ∂(stdGaussian (Euc d)) := integral_nonneg fun u => sq_nonneg _
  have hK00 : 0 ≤ C * 2 ^ M * jbracket x₀ ^ M :=
    mul_nonneg (mul_nonneg hC (by positivity)) (Real.rpow_nonneg (s83_jb_pos x₀).le _)
  have hmom : 0 ≤ mom d (2 * M) σ₀ := s83_mom_nonneg _ _ hσ00
  have hR0 : 0 ≤ ∫ u, (s83_E k u - 1 - ⟪u, k⟫) ^ 2 ∂(stdGaussian (Euc d)) :=
    integral_nonneg fun u => sq_nonneg _
  have hsq : (∫ u, F u * (s83_E k u - 1 - ⟪u, k⟫) ∂(stdGaussian (Euc d))) ^ 2 ≤
      (C * 2 ^ M * jbracket x₀ ^ M) ^ 2 * mom d (2 * M) σ₀ * (‖k‖ ^ 2) ^ 2 :=
    hCS.trans (mul_le_mul hA hRle hR0 (mul_nonneg (sq_nonneg _) hmom))
  set L : ℝ := C * 2 ^ M * jbracket x₀ ^ M * Real.sqrt (mom d (2 * M) σ₀) * ‖k‖ ^ 2 with hL
  have hL2 : L ^ 2 = (C * 2 ^ M * jbracket x₀ ^ M) ^ 2 * mom d (2 * M) σ₀ * (‖k‖ ^ 2) ^ 2 := by
    have e1 : Real.sqrt (mom d (2 * M) σ₀) ^ 2 = mom d (2 * M) σ₀ := Real.sq_sqrt hmom
    rw [hL]
    calc (C * 2 ^ M * jbracket x₀ ^ M * Real.sqrt (mom d (2 * M) σ₀) * ‖k‖ ^ 2) ^ 2
        = (C * 2 ^ M * jbracket x₀ ^ M) ^ 2 * Real.sqrt (mom d (2 * M) σ₀) ^ 2 * (‖k‖ ^ 2) ^ 2 := by ring
      _ = _ := by rw [e1]
  have hL0 : 0 ≤ L := by
    rw [hL]; exact mul_nonneg (mul_nonneg hK00 (Real.sqrt_nonneg _)) (sq_nonneg _)
  have := abs_le_of_sq_le_sq (hL2 ▸ hsq) hL0
  rw [hdiff]
  exact this

end HRS.MS.Wad
