import HRS.MS.WadAux84
import HRS.MS.WadAux42

/-!
# S8.3, packet S8E-4, part 1: density of `C_c^∞` in `C_M` with control of the weighted Lipschitz seminorm

`s8e_density_lip`: if `f ∈ C_M` is weighted-bounded (`Wt M Φ0 f`) and weighted-Lipschitz
(`|f(y+z) - f(y)| ≤ Λ ‖z‖ ⟨y⟩^M`, `‖z‖ < 1/4`), then for every `ε > 0` there is `φ ∈ C_c^∞` with `Wt M ε (φ - f)` and
`|φ(y+z) - φ(y)| ≤ 3^M (Λ + Φ0) ‖z‖ ⟨y⟩^M` (cutoff, then mollification by a normed bump).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal Convolution ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8e_chi_lip (R : ℝ) (x z : Euc d) :
    |max 0 (min 1 (R + 1 - ‖x + z‖)) - max 0 (min 1 (R + 1 - ‖x‖))| ≤ ‖z‖ := by
  have h1 : |min (1 : ℝ) (R + 1 - ‖x + z‖) - min (1 : ℝ) (R + 1 - ‖x‖)| ≤
      |(R + 1 - ‖x + z‖) - (R + 1 - ‖x‖)| := by
    have := abs_min_sub_min_le_max (1 : ℝ) (R + 1 - ‖x + z‖) 1 (R + 1 - ‖x‖)
    simpa using this
  have h2 : |max (0 : ℝ) (min 1 (R + 1 - ‖x + z‖)) - max 0 (min 1 (R + 1 - ‖x‖))| ≤
      |min (1 : ℝ) (R + 1 - ‖x + z‖) - min (1 : ℝ) (R + 1 - ‖x‖)| := by
    have := abs_max_sub_max_le_abs (min (1 : ℝ) (R + 1 - ‖x + z‖)) (min (1 : ℝ) (R + 1 - ‖x‖)) 0
    simpa [max_comm] using this
  have h3 : |(R + 1 - ‖x + z‖) - (R + 1 - ‖x‖)| ≤ ‖z‖ := by
    rw [show (R + 1 - ‖x + z‖) - (R + 1 - ‖x‖) = ‖x‖ - ‖x + z‖ by ring, abs_sub_comm]
    have := abs_norm_sub_norm_le (x + z) x
    simpa using this
  exact h2.trans (h1.trans h3)

theorem s8e_density_lip {M Φ0 Λ : ℝ} (hM : 0 ≤ M) {f : Euc d → ℝ} (hf : MemCM M f) (hΦ0 : Wt M Φ0 f)
    (hΛ : 0 ≤ Λ) (hLf : ∀ y z : Euc d, ‖z‖ < 1 / 4 → |f (y + z) - f y| ≤ Λ * ‖z‖ * jbracket y ^ M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : Euc d → ℝ, S85Cc φ ∧ Wt M ε (fun y => φ y - f y) ∧
      ∀ y z : Euc d, ‖z‖ < 1 / 4 → |φ (y + z) - φ y| ≤ 3 ^ M * (Λ + Φ0) * ‖z‖ * jbracket y ^ M := by
  have hΦ00 : 0 ≤ Φ0 := hΦ0.nonneg
  have hpos2 : 0 < ε / 2 := by positivity
  have h0 : Tendsto (fun x : Euc d => |f x / jbracket x ^ M|) (cocompact (Euc d)) (𝓝 0) := by
    simpa using hf.2.abs
  have hev : ∀ᶠ x in cocompact (Euc d), |f x / jbracket x ^ M| < ε / 2 :=
    h0.eventually (gt_mem_nhds hpos2)
  obtain ⟨K, hK, hKs⟩ := Filter.mem_cocompact.1 hev
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Euc d)
  have hfar : ∀ x : Euc d, R < ‖x‖ → |f x| ≤ ε / 2 * jbracket x ^ M := by
    intro x hx
    have hxK : x ∉ K := fun h => by
      have := hR h
      rw [Metric.mem_closedBall, dist_zero_right] at this
      linarith
    have := hKs hxK
    have hp : 0 < jbracket x ^ M := Real.rpow_pos_of_pos (s83_jb_pos x) _
    rw [Set.mem_setOf_eq, abs_div, abs_of_pos hp, div_lt_iff₀ hp] at this
    exact this.le
  -- cutoff
  set χ : Euc d → ℝ := fun x => max 0 (min 1 (R + 1 - ‖x‖)) with hχ
  have hχc : Continuous χ := by
    simp only [hχ]
    fun_prop
  have hχ0 : ∀ x, 0 ≤ χ x := fun x => le_max_left _ _
  have hχ1 : ∀ x, χ x ≤ 1 := fun x => max_le zero_le_one (min_le_left _ _)
  have hχin : ∀ x, ‖x‖ ≤ R → χ x = 1 := by
    intro x hx
    have : (1 : ℝ) ≤ R + 1 - ‖x‖ := by linarith
    simp only [hχ, min_eq_left this]
    exact max_eq_right zero_le_one
  have hχout : ∀ x, R + 1 ≤ ‖x‖ → χ x = 0 := by
    intro x hx
    have : R + 1 - ‖x‖ ≤ 0 := by linarith
    simp only [hχ]
    have h2 : min 1 (R + 1 - ‖x‖) ≤ 0 := (min_le_right _ _).trans this
    exact max_eq_left h2
  set f₁ : Euc d → ℝ := fun x => χ x * f x with hf₁
  have hf₁c : Continuous f₁ := hχc.mul hf.1
  have hf₁s : HasCompactSupport f₁ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) (R + 1)) fun x hx => ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
    simp only [hf₁, hχout x hx.le, zero_mul]
  have hJ : ∀ x : Euc d, 1 ≤ jbracket x ^ M := fun x => Real.one_le_rpow (s83_one_le_jb x) hM
  have hf₁f : ∀ x, |f₁ x - f x| ≤ ε / 2 * jbracket x ^ M := by
    intro x
    by_cases hx : ‖x‖ ≤ R
    · simp only [hf₁, hχin x hx, one_mul, sub_self, abs_zero]
      have := hJ x
      positivity
    · push_neg at hx
      have e : f₁ x - f x = (χ x - 1) * f x := by simp only [hf₁]; ring
      rw [e, abs_mul]
      have h1 : |χ x - 1| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [hχ0 x, hχ1 x]
      calc |χ x - 1| * |f x| ≤ 1 * |f x| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ ≤ ε / 2 * jbracket x ^ M := by rw [one_mul]; exact hfar x hx
  -- weighted Lipschitz bound of the cut-off function
  have hLf₁ : ∀ y z : Euc d, ‖z‖ < 1 / 4 → |f₁ (y + z) - f₁ y| ≤ (Λ + Φ0) * ‖z‖ * jbracket y ^ M := by
    intro y z hz
    have e : f₁ (y + z) - f₁ y = χ (y + z) * (f (y + z) - f y) + (χ (y + z) - χ y) * f y := by
      simp only [hf₁]; ring
    have hjy := Real.rpow_nonneg (s83_jb_pos y).le M
    have hc : |χ (y + z) - χ y| ≤ ‖z‖ := s8e_chi_lip R y z
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have t1 : |χ (y + z)| * |f (y + z) - f y| ≤ 1 * (Λ * ‖z‖ * jbracket y ^ M) := by
      refine mul_le_mul ?_ (hLf y z hz) (abs_nonneg _) zero_le_one
      rw [abs_of_nonneg (hχ0 _)]; exact hχ1 _
    have t2 : |χ (y + z) - χ y| * |f y| ≤ ‖z‖ * (Φ0 * jbracket y ^ M) := by
      refine mul_le_mul hc ?_ (abs_nonneg _) (norm_nonneg _)
      have := hΦ0 y
      rwa [Real.norm_eq_abs] at this
    nlinarith
  -- the mollifier
  set r : ℝ := min (1 / 4) (ε / (2 * (Λ + Φ0 + 1))) with hr
  have hr0 : 0 < r := lt_min (by norm_num) (by positivity)
  have hr4 : r ≤ 1 / 4 := min_le_left _ _
  have hrε : (Λ + Φ0) * r ≤ ε / 2 := by
    have h1 : r ≤ ε / (2 * (Λ + Φ0 + 1)) := min_le_right _ _
    have h2 : (Λ + Φ0) * r ≤ (Λ + Φ0 + 1) * r := by nlinarith
    calc (Λ + Φ0) * r ≤ (Λ + Φ0 + 1) * (ε / (2 * (Λ + Φ0 + 1))) :=
          h2.trans (mul_le_mul_of_nonneg_left h1 (by positivity))
      _ = ε / 2 := by field_simp
  set ψ : ContDiffBump (0 : Euc d) := ⟨r / 2, r, half_pos hr0, half_lt_self hr0⟩ with hψ
  have hψr : ψ.rOut = r := rfl
  set g : Euc d → ℝ := (ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f₁ : Euc d → ℝ) with hg
  have hgd : ContDiff ℝ ∞ g := ψ.hasCompactSupport_normed.contDiff_convolution_left _ ψ.contDiff_normed
    hf₁c.locallyIntegrable
  have hgs : HasCompactSupport g := ψ.hasCompactSupport_normed.convolution _ hf₁s
  refine ⟨g, ⟨hgd, hgs⟩, fun y => ?_, fun y z hz => ?_⟩
  · -- closeness
    have hj := Real.rpow_nonneg (s83_jb_pos y).le M
    have hd1 : dist (g y) (f₁ y) ≤ (Λ + Φ0) * r * jbracket y ^ M := by
      refine ψ.dist_normed_convolution_le (μ := volume) hf₁c.aestronglyMeasurable (fun x hx => ?_)
      rw [hψr, mem_ball_iff_norm] at hx
      have := hLf₁ y (x - y) (by linarith)
      rw [add_sub_cancel] at this
      rw [Real.dist_eq]
      refine this.trans ?_
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx.le (by positivity)) hj
    have h2 := hf₁f y
    have h3 : (Λ + Φ0) * r * jbracket y ^ M ≤ ε / 2 * jbracket y ^ M :=
      mul_le_mul_of_nonneg_right hrε hj
    show ‖g y - f y‖ ≤ ε * jbracket y ^ M
    rw [Real.norm_eq_abs]
    rw [Real.dist_eq] at hd1
    have e : g y - f y = (g y - f₁ y) + (f₁ y - f y) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    nlinarith
  · -- Lipschitz bound
    have hconv : ∀ y, ConvolutionExistsAt (ψ.normed volume) f₁ y (ContinuousLinearMap.lsmul ℝ ℝ) volume := fun y =>
      (ψ.hasCompactSupport_normed.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) ψ.continuous_normed
        hf₁c.locallyIntegrable) y
    set h : Euc d → ℝ := fun x => f₁ (x + z) - f₁ x with hh
    have hhc : Continuous h := (hf₁c.comp (continuous_id.add continuous_const)).sub hf₁c
    have hid : g (y + z) - g y = (ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h : Euc d → ℝ) y := by
      simp only [hg, hh, convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
      have i1 := (hconv (y + z)).integrable
      have i2 := (hconv y).integrable
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul] at i1 i2
      rw [← integral_sub i1 i2]
      congr 1
      funext t
      rw [mul_sub, show y + z - t = y - t + z by abel]
    have hnn : 0 ≤ (Λ + Φ0) * ‖z‖ * (3 ^ M * jbracket y ^ M) := by
      have := Real.rpow_nonneg (s83_jb_pos y).le M
      positivity
    have := dist_convolution_le (μ := volume) (E' := ℝ) (f := ψ.normed volume) (g := h) (x₀ := y) (R := r)
      (ε := (Λ + Φ0) * ‖z‖ * (3 ^ M * jbracket y ^ M)) (z₀ := 0) hnn
      (by rw [ψ.support_normed_eq]) (fun x => ψ.nonneg_normed x) ψ.integral_normed
      hhc.aestronglyMeasurable (fun x hx => by
        rw [Real.dist_eq, sub_zero]
        have hxy : x ∈ ball y (1 / 4) := by
          rw [mem_ball_iff_norm] at hx ⊢; linarith
        have hbd := hLf₁ x z hz
        refine hbd.trans ?_
        have hj := s84_jb_ball hM hxy
        calc (Λ + Φ0) * ‖z‖ * jbracket x ^ M ≤ (Λ + Φ0) * ‖z‖ * (3 ^ M * jbracket y ^ M) :=
              mul_le_mul_of_nonneg_left hj (by positivity)
          _ = _ := rfl)
    rw [hid]
    rw [Real.dist_eq, sub_zero] at this
    calc _ ≤ _ := this
      _ = 3 ^ M * (Λ + Φ0) * ‖z‖ * jbracket y ^ M := by ring

end HRS.MS.Wad
