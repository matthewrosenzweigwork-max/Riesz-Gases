import Mathlib

/-!
A covariance representer controlled by centered test norms has zero mass.
The constant function is approached through actual smooth compact cutoffs;
it is never asserted to be an oscillator test.  This removes an implicit
zero-mass assumption from the later physical Wick contraction.
-/
set_option autoImplicit false
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.ProClosureS111

def massCutoff (d n : ℕ) : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) :=
  ⟨(n : ℝ) + 1, (n : ℝ) + 2, by positivity, by linarith⟩

theorem massCutoff_tendsto_one (d : ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    Tendsto (fun n => massCutoff d n x) atTop (𝓝 1) := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  symm
  apply (massCutoff d n).one_of_mem_closedBall
  simp only [Metric.mem_closedBall, dist_zero_right]
  change ‖x‖ ≤ (n : ℝ) + 1
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

/-- The bound is needed only on genuine smooth compactly supported tests.
It implies zero mass for any integrable representer. -/
theorem integral_zero_of_centered_test_bound {d : ℕ}
    (mu : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure mu]
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : Integrable f mu)
    (C : ℝ)
    (hbound : ∀ b : EuclideanSpace ℝ (Fin d) → ℝ,
      ContDiff ℝ ∞ b → HasCompactSupport b →
      |∫ x, f x * b x ∂mu| ≤ C * Real.sqrt
        (∫ x, (b x - ∫ y, b y ∂mu) ^ 2 ∂mu)) :
    ∫ x, f x ∂mu = 0 := by
  let b : ℕ → EuclideanSpace ℝ (Fin d) → ℝ := fun n => massCutoff d n
  have hb0 : ∀ n x, 0 ≤ b n x := fun n x => (massCutoff d n).nonneg
  have hb1 : ∀ n x, b n x ≤ 1 := fun n x => (massCutoff d n).le_one
  have hbabs : ∀ n x, ‖b n x‖ ≤ 1 := fun n x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hb0 n x)]
    exact hb1 n x
  have hbm : ∀ n, AEStronglyMeasurable (b n) mu := fun n =>
    (show ContDiff ℝ ∞ (b n) from (massCutoff d n).contDiff).continuous.aestronglyMeasurable
  have hbi : ∀ n, Integrable (b n) mu := fun n =>
    (integrable_const (1 : ℝ)).mono' (hbm n) (ae_of_all mu (hbabs n))
  have hbconv : ∀ x, Tendsto (fun n => b n x) atTop (𝓝 1) :=
    massCutoff_tendsto_one d
  have hmean : Tendsto (fun n => ∫ x, b n x ∂mu) atTop (𝓝 1) := by
    simpa using tendsto_integral_of_dominated_convergence (μ := mu)
      (F := b) (f := fun _ => (1 : ℝ)) (fun _ => (1 : ℝ)) hbm
      (integrable_const 1) (fun n => ae_of_all mu (hbabs n))
      (ae_of_all mu hbconv)
  have hmean0 : ∀ n, 0 ≤ ∫ x, b n x ∂mu := fun n => integral_nonneg (hb0 n)
  have hmean1 : ∀ n, (∫ x, b n x ∂mu) ≤ 1 := by
    intro n
    calc
      (∫ x, b n x ∂mu) ≤ ∫ _x, (1 : ℝ) ∂mu :=
        integral_mono (hbi n) (integrable_const 1) (hb1 n)
      _ = 1 := by simp
  have hvar : Tendsto (fun n => ∫ x, (b n x - ∫ y, b n y ∂mu) ^ 2 ∂mu)
      atTop (𝓝 0) := by
    have hconv : ∀ x, Tendsto
        (fun n => (b n x - ∫ y, b n y ∂mu) ^ 2) atTop (𝓝 0) := by
      intro x
      simpa using ((hbconv x).sub hmean).pow 2
    have hdom : ∀ n x, ‖(b n x - ∫ y, b n y ∂mu) ^ 2‖ ≤ 1 := by
      intro n x
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h0 := hb0 n x
      have h1 := hb1 n x
      have hm0 := hmean0 n
      have hm1 := hmean1 n
      nlinarith [sq_nonneg (b n x + (∫ y, b n y ∂mu) - 1),
        mul_nonneg h0 (sub_nonneg.2 h1), mul_nonneg hm0 (sub_nonneg.2 hm1)]
    simpa using tendsto_integral_of_dominated_convergence (μ := mu)
      (F := fun n x => (b n x - ∫ y, b n y ∂mu) ^ 2)
      (f := fun _ => (0 : ℝ)) (fun _ => (1 : ℝ))
      (fun n => ((hbm n).sub aestronglyMeasurable_const).pow 2)
      (integrable_const 1) (fun n => ae_of_all mu (hdom n))
      (ae_of_all mu hconv)
  have hfconv : Tendsto (fun n => ∫ x, f x * b n x ∂mu) atTop
      (𝓝 (∫ x, f x ∂mu)) := by
    apply tendsto_integral_of_dominated_convergence (μ := mu) (fun x => ‖f x‖)
    · intro n
      exact hf.aestronglyMeasurable.mul (hbm n)
    · exact hf.norm
    · intro n
      exact ae_of_all mu fun x => by
        rw [norm_mul]
        exact mul_le_of_le_one_right (norm_nonneg _) (hbabs n x)
    · exact ae_of_all mu fun x => by simpa using tendsto_const_nhds.mul (hbconv x)
  have hzero : Tendsto (fun n => |∫ x, f x * b n x ∂mu|) atTop (𝓝 0) := by
    have hup : Tendsto
        (fun n => C * Real.sqrt (∫ x, (b n x - ∫ y, b n y ∂mu) ^ 2 ∂mu))
        atTop (𝓝 0) := by
      simpa using ((Real.continuous_sqrt.tendsto 0).comp hvar).const_mul C
    exact squeeze_zero (fun _ => abs_nonneg _)
      (fun n => hbound (b n) (massCutoff d n).contDiff (massCutoff d n).hasCompactSupport)
      hup
  exact abs_eq_zero.1 (tendsto_nhds_unique hfconv.abs hzero)

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.integral_zero_of_centered_test_bound
