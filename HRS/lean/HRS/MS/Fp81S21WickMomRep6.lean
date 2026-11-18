import HRS.MS.Fp81S21WickMomRep5

/-! Fixed compact-test identification with the supplied kernel operator. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- For a compact test, the coherent chart action is a version of the
positive half-Wick operator applied to the test's commutator kernel. -/
theorem fp81s21_wick_compact_test_agreement
    {d r : ℕ} {Pw : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    (hd : 2 ≤ d) (s a beta : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta)
    (hr : (2 : ℝ) + (d : ℝ) / 2 < r) (hP : (d : ℝ) < 2 * Pw)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d s a beta rho)
    (E : r26t6_WeightedChart d r Pw) (P : Measure Ω) [IsProbabilityMeasure P]
    (W : Lp ℝ 2 ((HRS.Whole.withDensityReal rho).prod
      (HRS.Whole.withDensityReal rho)) →L[ℝ] Lp ℝ 2 P)
    (hk : ∀ j, MemLp (fun xy : Euc d × Euc d =>
      commutatorKernel d s (gradient (E.test j)) xy.1 xy.2) 2
      ((HRS.Whole.withDensityReal rho).prod (HRS.Whole.withDensityReal rho)))
    (q : Ω → r26t6_Coeff) (hq : MemLp q 2 P)
    (hcoord : ∀ j, (fun ω => q ω j) =ᵐ[P]
      (W ((hk j).toLp (fun xy : Euc d × Euc d =>
        commutatorKernel d s (gradient (E.test j)) xy.1 xy.2)) : Ω → ℝ))
    (f : Euc d → ℝ) (hf : IsR2Test f)
    (hker : MemLp (fun xy : Euc d × Euc d =>
      commutatorKernel d s (gradient f) xy.1 xy.2) 2
      ((HRS.Whole.withDensityReal rho).prod (HRS.Whole.withDensityReal rho))) :
    (fun ω => fp81s21_chartAction E (q ω) f) =ᵐ[P]
      (W (hker.toLp (fun xy : Euc d × Euc d =>
        commutatorKernel d s (gradient f) xy.1 xy.2)) : Ω → ℝ) := by
  let μ := HRS.Whole.withDensityReal rho
  letI : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu hrho.1.1
  obtain ⟨hw, hlim⟩ := fp81s21_wick_chartSection_kernel_tendsto hd s a beta
    hs0 hs ha hbeta hr hP rho hrho E f hf
  let c := E.encode f
  let fn : ℕ → compactSmoothSubmodule d := chartSection E c
  let hnW : ∀ n, IsR2WeightedTest r Pw (fn n) := fun n =>
    weightedTestSubmodule_iff.1 (weighted_test_of_compact_smooth hP
      (show IsR2Test (fn n : Euc d → ℝ) from (fn n).property))
  let hfW : IsR2WeightedTest r Pw f :=
    weightedTestSubmodule_iff.1 (weighted_test_of_compact_smooth hP hf)
  let kn : ℕ → Lp ℝ 2 (μ.prod μ) := fun n => (hw (fn n) (hnW n)).toLp
    (fun xy => commutatorKernel d s (gradient (fn n : Euc d → ℝ)) xy.1 xy.2)
  let k : Lp ℝ 2 (μ.prod μ) := hker.toLp
    (fun xy => commutatorKernel d s (gradient f) xy.1 xy.2)
  have hkconv : Tendsto kn atTop (𝓝 k) := by
    simpa only [kn, k, fn, c, hnW, hfW] using hlim
  let Y : Ω → ℝ := fun ω => inner ℝ (q ω) c
  let Yn : ℕ → Ω → ℝ := fun n ω => inner ℝ (q ω) (coeffSection c n)
  have hY : MemLp Y 2 P := hq.inner_const c
  have hYn : ∀ n, MemLp (Yn n) 2 P := fun n => hq.inner_const (coeffSection c n)
  let Yp : Lp ℝ 2 P := hY.toLp Y
  let Ynp : ℕ → Lp ℝ 2 P := fun n => (hYn n).toLp (Yn n)
  have hfinite : ∀ n, Ynp n = W (kn n) := by
    intro n
    apply Lp.ext
    filter_upwards [(hYn n).coeFn_toLp,
      fp81s21_wick_chartSection_agreement E s μ P W hk q hcoord c n (hw (fn n) (hnW n))] with ω h1 h2
    change Ynp n ω = _ at h1
    exact h1.trans h2
  have hYconv : Tendsto Ynp atTop (𝓝 Yp) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hsquare := inner_pairing_square_tendsto P q hq c (coeffSection c) (coeffSection_tendsto c)
    have heq : ∀ n, ‖Ynp n - Yp‖ ^ 2 = ∫ ω, (Yn n ω - Y ω) ^ 2 ∂P := by
      intro n
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (Ynp n) Yp,
        (hYn n).coeFn_toLp, hY.coeFn_toLp] with ω h1 h2 h3
      change (Ynp n - Yp) ω * (Ynp n - Yp) ω = _
      rw [h1]
      simp only [Pi.sub_apply]
      change Ynp n ω = _ at h2
      change Yp ω = _ at h3
      rw [h2, h3]
      ring
    have hsq : Tendsto (fun n => ‖Ynp n - Yp‖ ^ 2) atTop (𝓝 0) := by
      simpa only [heq, Yn, Y] using hsquare
    have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
    simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] using hsqrt
  have hYeq : Yp = W k := by
    apply tendsto_nhds_unique hYconv
    have hWconv := W.continuous.tendsto k |>.comp hkconv
    simpa only [Function.comp_def, ← hfinite] using hWconv
  have hae : Y =ᵐ[P] (W k : Ω → ℝ) := by
    filter_upwards [hY.coeFn_toLp] with ω hω
    change Yp ω = Y ω at hω
    rw [hYeq] at hω
    exact hω.symm
  simpa only [Y, c, fp81s21_chartAction] using hae

#print axioms fp81s21_wick_compact_test_agreement
end HRS.Fp81.S21
end
