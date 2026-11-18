import HRS.MS.Fp81S21GaussianFeatureBound3

/-! Canonical chart sections converge in the thermal L² space. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- Thermal convergence with the compact approximants fixed to the canonical
chart sections, so the same sequence can be used for literal feature convergence. -/
theorem fp81s21_chartSection_thermal_convergence
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (f : Euc p.d → ℝ)
    (hfW : IsR2WeightedTest (2 * p.d + 8) ((p.d : ℝ) + 2) f) :
    let μ := HRS.Whole.withDensityReal R.ρβ
    let ψ : ℕ → compactSmoothSubmodule p.d := chartSection E (E.encode f)
    ∃ hf : MemLp f 2 μ, ∃ hψ : ∀ n, MemLp (ψ n : Euc p.d → ℝ) 2 μ,
      Tendsto (fun n => (hψ n).toLp (ψ n : Euc p.d → ℝ))
        atTop (𝓝 (hf.toLp f)) := by
  let μ := HRS.Whole.withDensityReal R.ρβ
  letI : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  have hr : (2 : ℝ) + (p.d : ℝ) / 2 < ((2 * p.d + 8 : ℕ) : ℝ) := by
    have hd : (0 : ℝ) ≤ p.d := Nat.cast_nonneg _
    push_cast
    linarith
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) p.d]
  obtain ⟨B, _, hOp⟩ := physical_weighted_L2_operators p.hd p.s p.a p.β
    ((p.d : ℝ) + 2) (2 * p.d + 8) p.hs0 p.hs p.ha p.hβ hr hP R.ρβ R.thermal
  let ψ : ℕ → compactSmoothSubmodule p.d := chartSection E (E.encode f)
  have hψW : ∀ n, IsR2WeightedTest (2 * p.d + 8) ((p.d : ℝ) + 2)
      (ψ n : Euc p.d → ℝ) := fun n =>
    weightedTestSubmodule_iff.1 (weighted_test_of_compact_smooth hP (ψ n).property)
  let hψ : ∀ n, MemLp (ψ n : Euc p.d → ℝ) 2 μ :=
    fun n => (hOp (ψ n) (hψW n)).1
  let hf : MemLp f 2 μ := (hOp f hfW).1
  refine ⟨hf, hψ, ?_⟩
  let fn : ℕ → Lp ℝ 2 μ := fun n => (hψ n).toLp (ψ n : Euc p.d → ℝ)
  let fL : Lp ℝ 2 μ := hf.toLp f
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hb : ∀ n, ‖fn n - fL‖ ^ 2 ≤ B *
      (weightedSobolevE (2 * p.d + 8) ((p.d : ℝ) + 2)
        ((ψ n : Euc p.d → ℝ) - f)).toReal ^ 2 := by
    intro n
    have heq : ‖fn n - fL‖ ^ 2 = ∫ x : Euc p.d,
        ((ψ n : Euc p.d → ℝ) x - f x) ^ 2 ∂μ := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (fn n) fL, (hψ n).coeFn_toLp,
        hf.coeFn_toLp] with x h1 h2 h3
      change (fn n - fL) x * (fn n - fL) x = _
      rw [h1]
      simp only [Pi.sub_apply]
      change fn n x = _ at h2
      change fL x = _ at h3
      rw [h2, h3]
      ring
    rw [heq]
    simpa only [Pi.sub_apply] using
      (hOp _ (chartSection_error_weighted E hP f hfW n)).2.1
  have he := chartSection_error_tendsto E hP f hfW
  have hlim : Tendsto (fun n : ℕ => B *
      (weightedSobolevE (2 * p.d + 8) ((p.d : ℝ) + 2)
        ((ψ n : Euc p.d → ℝ) - f)).toReal ^ 2) atTop (𝓝 0) := by
    simpa [ψ] using (he.pow 2).const_mul B
  have hsq : Tendsto (fun n => ‖fn n - fL‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun _ => sq_nonneg _) hb hlim
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] using hsqrt

#print axioms fp81s21_chartSection_thermal_convergence
end HRS.Fp81.S21
end
