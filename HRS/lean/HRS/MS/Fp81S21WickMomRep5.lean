import HRS.MS.Fp81S21WickMomRep4
import HRS.MS.ProClosureS111ChartWickAllTests

/-! Product L² convergence of the commutator kernels of chart sections. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology
open scoped ENNReal

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- The actual commutator kernels of the chart sections converge in product
L² to the kernel of any compact smooth test. -/
theorem fp81s21_wick_chartSection_kernel_tendsto
    {d r : ℕ} {Pw : ℝ} (hd : 2 ≤ d)
    (s a beta : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta)
    (hr : (2 : ℝ) + (d : ℝ) / 2 < r) (hP : (d : ℝ) < 2 * Pw)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d s a beta rho)
    (E : r26t6_WeightedChart d r Pw) (f : Euc d → ℝ) (hf : IsR2Test f) :
    let μ : Measure (Euc d) := HRS.Whole.withDensityReal rho
    ∃ hk : ∀ g : Euc d → ℝ, IsR2WeightedTest r Pw g →
      MemLp (fun xy : Euc d × Euc d =>
        commutatorKernel d s (gradient g) xy.1 xy.2) 2
        (μ.prod μ),
    Tendsto (fun n : ℕ => ((hk (chartSection E (E.encode f) n)
      (weightedTestSubmodule_iff.1 (weighted_test_of_compact_smooth hP
        (chartSection E (E.encode f) n).property))).toLp
          (fun xy : Euc d × Euc d => commutatorKernel d s
            (gradient (chartSection E (E.encode f) n : Euc d → ℝ)) xy.1 xy.2) : Lp ℝ 2 (μ.prod μ)))
      atTop (𝓝 (((hk f (weightedTestSubmodule_iff.1
        (weighted_test_of_compact_smooth hP hf))).toLp
          (fun xy : Euc d × Euc d => commutatorKernel d s (gradient f) xy.1 xy.2) : Lp ℝ 2 (μ.prod μ)))) := by
  obtain ⟨B, hB, hOp⟩ := physical_weighted_L2_operators hd s a beta Pw r
    hs0 hs ha hbeta hr hP rho hrho
  let μ := HRS.Whole.withDensityReal rho
  let hw : ∀ g : Euc d → ℝ, IsR2WeightedTest r Pw g →
      MemLp (fun xy : Euc d × Euc d => commutatorKernel d s (gradient g) xy.1 xy.2)
        2 (μ.prod μ) := fun g hg => (hOp g hg).2.2.1
  refine ⟨hw, ?_⟩
  let fn : ℕ → compactSmoothSubmodule d := chartSection E (E.encode f)
  let hfW : IsR2WeightedTest r Pw f :=
    weightedTestSubmodule_iff.1 (weighted_test_of_compact_smooth hP hf)
  let hnW : ∀ n, IsR2WeightedTest r Pw (fn n) := fun n =>
    weightedTestSubmodule_iff.1 (weighted_test_of_compact_smooth hP
      (show IsR2Test (fn n : Euc d → ℝ) from (fn n).property))
  let k : Lp ℝ 2 (μ.prod μ) := (hw f hfW).toLp
    (fun xy => commutatorKernel d s (gradient f) xy.1 xy.2)
  let kn : ℕ → Lp ℝ 2 (μ.prod μ) := fun n => (hw (fn n) (hnW n)).toLp
    (fun xy => commutatorKernel d s (gradient (fn n : Euc d → ℝ)) xy.1 xy.2)
  change Tendsto kn atTop (𝓝 k)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hr0 : 0 < r := by
    have hd0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    have hr' : (0 : ℝ) < r := by linarith
    exact_mod_cast hr'
  have hb : ∀ n, ‖kn n - k‖ ^ 2 ≤ B *
      (weightedSobolevE r Pw ((fn n : Euc d → ℝ) - f)).toReal ^ 2 := by
    intro n
    have hsub := commutator_gradient_sub s (fn n) f
      ((fn n).property.1.differentiable (by norm_num))
      (hf.1.differentiable (by norm_num))
    have heq : ‖kn n - k‖ ^ 2 = ∫ xy : Euc d × Euc d,
        (commutatorKernel d s (gradient (fn n : Euc d → ℝ)) xy.1 xy.2 -
         commutatorKernel d s (gradient f) xy.1 xy.2) ^ 2 ∂(μ.prod μ) := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (kn n) k, (hw (fn n) (hnW n)).coeFn_toLp,
        (hw f hfW).coeFn_toLp] with xy h1 h2 h3
      change (kn n - k) xy * (kn n - k) xy = _
      rw [h1]
      simp only [Pi.sub_apply]
      change (kn n) xy = _ at h2
      change k xy = _ at h3
      rw [h2, h3]
      ring
    rw [heq]
    have he := (hOp _ (chartSection_error_weighted E hP f hfW n)).2.2.2
    change (∫ xy : Euc d × Euc d, commutatorKernel d s
      (gradient ((fn n : Euc d → ℝ) - f)) xy.1 xy.2 ^ 2 ∂(μ.prod μ)) ≤
        B * (weightedSobolevE r Pw ((fn n : Euc d → ℝ) - f)).toReal ^ 2 at he
    simpa only [hsub] using he
  have he := chartSection_error_tendsto E hP f hfW
  have hlim : Tendsto (fun n : ℕ => B *
      (weightedSobolevE r Pw ((fn n : Euc d → ℝ) - f)).toReal ^ 2) atTop (𝓝 0) := by
    simpa [fn] using (he.pow 2).const_mul B
  have hsq : Tendsto (fun n => ‖kn n - k‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun _ => sq_nonneg _) hb hlim
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] using hsqrt

#print axioms fp81s21_wick_chartSection_kernel_tendsto
end HRS.Fp81.S21
end
