import HRS.MS.WadAux16

/-!
# S8.3, packet D2''' (Route A): differentiability of `G_{c,σ} g` for merely continuous `g`

`s84_S c σ g x = ∫ g(cx + σu) u dγ(u)` (the Stein vector).  For `g` continuous with `|g| ≤ C⟨·⟩^M`,
`σ ≠ 0`: `G g` is `C¹`, `D (G g)(x) = (c/σ) ⟨s84_S x, ·⟩`, `‖s84_S x‖ ≤ C 2^M mom1 ⟨x⟩^M`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

/-- The Stein vector `∫ g(c x + σ u) u dγ(u)`. -/
def s84_S (c σ : ℝ) (g : Euc d → ℝ) (x : Euc d) : Euc d :=
  ∫ u, g (c • x + σ • u) • u ∂(stdGaussian (Euc d))

/-- Pointwise bound of the shifted datum. -/
theorem s84_Fbound {g : Euc d → ℝ} {M C : ℝ} (hM : 0 ≤ M) (hw : Wt M C g) {c σ σ₀ : ℝ} (hc : |c| ≤ 1)
    (hσ : |σ| ≤ σ₀) (x u : Euc d) :
    ‖g (c • x + σ • u)‖ ≤ C * 2 ^ M * jbracket x ^ M * (1 + σ₀ * ‖u‖) ^ ⌈M⌉₊ := by
  have hC := hw.nonneg
  have h2 := hw (c • x + σ • u)
  have h3 := s83_jb_add_rpow hM (c • x) (σ • u)
  have h4 : jbracket (c • x) ^ M ≤ jbracket x ^ M := s83_jb_smul_le_rpow hM hc x
  have h5 := s83_jb_smul_poly hM hσ u
  refine h2.trans ?_
  calc C * jbracket (c • x + σ • u) ^ M
      ≤ C * (2 ^ M * (jbracket (c • x) ^ M * jbracket (σ • u) ^ M)) :=
        mul_le_mul_of_nonneg_left h3 hC
    _ ≤ C * (2 ^ M * (jbracket x ^ M * (1 + σ₀ * ‖u‖) ^ ⌈M⌉₊)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul h4 h5 (Real.rpow_nonneg (s83_jb_pos _).le _)
            (Real.rpow_nonneg (s83_jb_pos _).le _)) (by positivity)) hC
    _ = _ := by ring

theorem s84_Fu_integrable {g : Euc d → ℝ} (hg : Continuous g) {M C : ℝ} (hM : 0 ≤ M) (hw : Wt M C g)
    {c σ σ₀ : ℝ} (hc : |c| ≤ 1) (hσ : |σ| ≤ σ₀) (x : Euc d) :
    Integrable (fun u : Euc d => g (c • x + σ • u) • u) (stdGaussian (Euc d)) := by
  have hσ00 : 0 ≤ σ₀ := (abs_nonneg _).trans hσ
  refine ((s83_int_mom1 hσ00 ⌈M⌉₊).const_mul (C * 2 ^ M * jbracket x ^ M)).mono'
    ((hg.comp (continuous_const.add (continuous_const_smul σ))).smul continuous_id).aestronglyMeasurable
    (Eventually.of_forall fun u => ?_)
  rw [norm_smul]
  calc ‖g (c • x + σ • u)‖ * ‖u‖ ≤ (C * 2 ^ M * jbracket x ^ M * (1 + σ₀ * ‖u‖) ^ ⌈M⌉₊) * ‖u‖ :=
        mul_le_mul_of_nonneg_right (s84_Fbound hM hw hc hσ x u) (norm_nonneg _)
    _ = C * 2 ^ M * jbracket x ^ M * (‖u‖ * (1 + σ₀ * ‖u‖) ^ ⌈M⌉₊) := by ring

/-- Norm bound of the Stein vector. -/
theorem s84_S_norm_le {g : Euc d → ℝ} (hg : Continuous g) {M C : ℝ} (hM : 0 ≤ M) (hw : Wt M C g)
    {c σ σ₀ : ℝ} (hc : |c| ≤ 1) (hσ : |σ| ≤ σ₀) (x : Euc d) :
    ‖s84_S c σ g x‖ ≤ C * 2 ^ M * mom1 d M σ₀ * jbracket x ^ M := by
  have hσ00 : 0 ≤ σ₀ := (abs_nonneg _).trans hσ
  unfold s84_S
  refine (norm_integral_le_of_norm_le ((s83_int_mom1 hσ00 ⌈M⌉₊).const_mul
    (C * 2 ^ M * jbracket x ^ M)) (Eventually.of_forall fun u => ?_)).trans ?_
  · rw [norm_smul]
    calc ‖g (c • x + σ • u)‖ * ‖u‖ ≤ (C * 2 ^ M * jbracket x ^ M * (1 + σ₀ * ‖u‖) ^ ⌈M⌉₊) * ‖u‖ :=
          mul_le_mul_of_nonneg_right (s84_Fbound hM hw hc hσ x u) (norm_nonneg _)
      _ = C * 2 ^ M * jbracket x ^ M * (‖u‖ * (1 + σ₀ * ‖u‖) ^ ⌈M⌉₊) := by ring
  · rw [integral_const_mul]
    unfold mom1
    exact le_of_eq (by ring)

/-- Continuity of the Stein vector. -/
theorem s84_S_continuous {g : Euc d → ℝ} (hg : Continuous g) {M C : ℝ} (hM : 0 ≤ M) (hw : Wt M C g)
    {c σ σ₀ : ℝ} (hc : |c| ≤ 1) (hσ : |σ| ≤ σ₀) : Continuous (s84_S c σ g) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  have hσ00 : 0 ≤ σ₀ := (abs_nonneg _).trans hσ
  have hC := hw.nonneg
  refine continuousAt_of_dominated
    (bound := fun u : Euc d => C * 2 ^ M * (3 * jbracket x₀) ^ M * (‖u‖ * (1 + σ₀ * ‖u‖) ^ ⌈M⌉₊)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun x =>
      ((hg.comp (continuous_const.add (continuous_const_smul σ))).smul continuous_id).aestronglyMeasurable
  · have hball : Metric.ball x₀ 1 ∈ 𝓝 x₀ := Metric.ball_mem_nhds _ one_pos
    filter_upwards [hball] with x hx
    refine Eventually.of_forall fun u => ?_
    rw [mem_ball_iff_norm] at hx
    rw [norm_smul]
    have h2 : jbracket x ^ M ≤ (3 * jbracket x₀) ^ M :=
      Real.rpow_le_rpow (s83_jb_pos _).le (s83_jb_le_three hx) hM
    calc ‖g (c • x + σ • u)‖ * ‖u‖ ≤ (C * 2 ^ M * jbracket x ^ M * (1 + σ₀ * ‖u‖) ^ ⌈M⌉₊) * ‖u‖ :=
          mul_le_mul_of_nonneg_right (s84_Fbound hM hw hc hσ x u) (norm_nonneg _)
      _ ≤ (C * 2 ^ M * (3 * jbracket x₀) ^ M * (1 + σ₀ * ‖u‖) ^ ⌈M⌉₊) * ‖u‖ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h2 (by positivity)) (by positivity)) (norm_nonneg _)
      _ = _ := by ring
  · exact (s83_int_mom1 hσ00 ⌈M⌉₊).const_mul _
  · exact Eventually.of_forall fun u =>
      ((hg.comp ((continuous_const_smul c).add continuous_const)).smul continuous_const).continuousAt

/-- **Differentiability of the Gaussian average of a continuous datum** (Stein formula). -/
theorem s84_G_hasFDerivAt {g : Euc d → ℝ} (hg : Continuous g) {M C : ℝ} (hM : 0 ≤ M) (hw : Wt M C g)
    {c σ σ₀ : ℝ} (hc : |c| ≤ 1) (hσ : |σ| ≤ σ₀) (hσ0 : σ ≠ 0) (x₀ : Euc d) :
    HasFDerivAt (s83_G c σ g) ((c / σ) • innerSL ℝ (s84_S c σ g x₀)) x₀ := by
  have hσ00 : 0 ≤ σ₀ := (abs_nonneg _).trans hσ
  set A : ℝ := |c| / |σ| with hA
  have hA0 : 0 ≤ A := by positivity
  set Kc : ℝ := C * 2 ^ M * jbracket x₀ ^ M * Real.sqrt (mom d (2 * M) σ₀) with hKc
  have hKc0 : 0 ≤ Kc :=
    mul_nonneg (mul_nonneg (mul_nonneg hw.nonneg (by positivity)) (Real.rpow_nonneg (s83_jb_pos _).le _))
      (Real.sqrt_nonneg _)
  have hInt := s84_Fu_integrable hg hM hw hc hσ x₀
  -- identify the linear term
  have hlin : ∀ x : Euc d, ∫ u, ⟪u, (c / σ) • (x - x₀)⟫ * g (c • x₀ + σ • u) ∂(stdGaussian (Euc d)) =
      ((c / σ) • innerSL ℝ (s84_S c σ g x₀)) (x - x₀) := by
    intro x
    have h := integral_inner (𝕜 := ℝ) (μ := stdGaussian (Euc d)) hInt ((c / σ) • (x - x₀))
    have e : ∀ u : Euc d, ⟪(c / σ) • (x - x₀), g (c • x₀ + σ • u) • u⟫ =
        ⟪u, (c / σ) • (x - x₀)⟫ * g (c • x₀ + σ • u) := fun u => by
      rw [real_inner_smul_right, real_inner_comm]; ring
    simp only [e] at h
    rw [h]
    simp only [ContinuousLinearMap.smul_apply, innerSL_apply_apply]
    unfold s84_S
    rw [real_inner_smul_left, real_inner_comm]
    simp [real_inner_smul_left, smul_eq_mul]
  rw [hasFDerivAt_iff_isLittleO]
  refine Asymptotics.isLittleO_iff.2 fun ε hε => ?_
  set δ : ℝ := min (1 / (A + 1)) (ε / (Kc * A ^ 2 + 1)) with hδ
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  filter_upwards [Metric.ball_mem_nhds x₀ hδ0] with x hx
  rw [mem_ball_iff_norm] at hx
  have hkn : ‖(c / σ) • (x - x₀)‖ = A * ‖x - x₀‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_div]
  have hk1 : A * ‖x - x₀‖ ≤ 1 := by
    have h1 : ‖x - x₀‖ ≤ 1 / (A + 1) := hx.le.trans (min_le_left _ _)
    calc A * ‖x - x₀‖ ≤ A * (1 / (A + 1)) := mul_le_mul_of_nonneg_left h1 hA0
      _ ≤ 1 := by rw [mul_one_div, div_le_one (by positivity)]; linarith
  have hrem := s84_G_remainder hg hM hw hc hσ hσ0 x x₀ (by rw [hkn]; exact hk1)
  rw [hlin x, hkn] at hrem
  rw [Real.norm_eq_abs]
  refine hrem.trans ?_
  have h2 : ‖x - x₀‖ ≤ ε / (Kc * A ^ 2 + 1) := hx.le.trans (min_le_right _ _)
  have hn := norm_nonneg (x - x₀)
  calc Kc * (A * ‖x - x₀‖) ^ 2 = (Kc * A ^ 2 * ‖x - x₀‖) * ‖x - x₀‖ := by ring
    _ ≤ ε * ‖x - x₀‖ := by
        refine mul_le_mul_of_nonneg_right ?_ hn
        have hK2 : 0 ≤ Kc * A ^ 2 := by positivity
        calc Kc * A ^ 2 * ‖x - x₀‖ ≤ Kc * A ^ 2 * (ε / (Kc * A ^ 2 + 1)) :=
              mul_le_mul_of_nonneg_left h2 hK2
          _ ≤ ε := by
              rw [← mul_div_assoc, div_le_iff₀ (by positivity)]
              nlinarith

/-- `G_{c,σ} g` is `C¹` for continuous `g` of weighted growth, `σ ≠ 0`. -/
theorem s84_G_contDiff {g : Euc d → ℝ} (hg : Continuous g) {M C : ℝ} (hM : 0 ≤ M) (hw : Wt M C g)
    {c σ σ₀ : ℝ} (hc : |c| ≤ 1) (hσ : |σ| ≤ σ₀) (hσ0 : σ ≠ 0) :
    ContDiff ℝ 1 (s83_G c σ g) := by
  rw [contDiff_one_iff_fderiv]
  have hd : Differentiable ℝ (s83_G c σ g) := fun x => (s84_G_hasFDerivAt hg hM hw hc hσ hσ0 x).differentiableAt
  refine ⟨hd, ?_⟩
  have : fderiv ℝ (s83_G c σ g) = fun x => (c / σ) • innerSL ℝ (s84_S c σ g x) := funext fun x =>
    (s84_G_hasFDerivAt hg hM hw hc hσ hσ0 x).fderiv
  rw [this]
  exact ((innerSL ℝ (E := Euc d)).continuous.comp (s84_S_continuous hg hM hw hc hσ)).const_smul (c / σ)

/-- Operator norm of the derivative. -/
theorem s84_G_fderiv_norm {g : Euc d → ℝ} (hg : Continuous g) {M C : ℝ} (hM : 0 ≤ M) (hw : Wt M C g)
    {c σ σ₀ : ℝ} (hc : |c| ≤ 1) (hσ : |σ| ≤ σ₀) (hσ0 : σ ≠ 0) (x : Euc d) :
    ‖fderiv ℝ (s83_G c σ g) x‖ ≤ |c| / |σ| * (C * 2 ^ M * mom1 d M σ₀) * jbracket x ^ M := by
  rw [(s84_G_hasFDerivAt hg hM hw hc hσ hσ0 x).fderiv]
  refine (norm_smul _ _).trans_le ?_
  rw [innerSL_apply_norm, Real.norm_eq_abs, abs_div]
  calc |c| / |σ| * ‖s84_S c σ g x‖ ≤ |c| / |σ| * (C * 2 ^ M * mom1 d M σ₀ * jbracket x ^ M) :=
        mul_le_mul_of_nonneg_left (s84_S_norm_le hg hM hw hc hσ x) (by positivity)
    _ = _ := by ring

end HRS.MS.Wad
