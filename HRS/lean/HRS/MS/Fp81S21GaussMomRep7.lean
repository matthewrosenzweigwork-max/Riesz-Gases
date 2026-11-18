import HRS.MS.Fp81S21GaussMomRep6
import HRS.MS.ProClosureS111PairingLimits

/-! Mean-square identification of oscillator observations and chart action. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology Set
open scoped ENNReal RealInnerProductSpace BigOperators

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.ProClosureS111 HRS.MS.S111X1

theorem fp81s21_oscillator_testwise_of_secondMoment_bound
    {d r : ℕ} {Pw m : ℝ}
    {Ω : Type*} [MeasurableSpace Ω]
    (hP : (d : ℝ) < 2 * Pw)
    (E : r26t6_WeightedChart d r Pw)
    (P : Measure Ω) (Z : Ω → OscDual d m)
    (q : Ω → r26t6_Coeff)
    (hq : MemLp q 2 P)
    (C : ℝ) (hC : 0 ≤ C)
    (hsecond : ∀ f : Euc d → ℝ, IsR2Test f →
      MemLp (fun ω => OscDual.eval (Z ω) f) 2 P ∧
      (∫ ω, OscDual.eval (Z ω) f ^ 2 ∂P) ≤
        C * (weightedSobolevE r Pw f).toReal ^ 2)
    (hcoord : ∀ j, ∀ᵐ ω ∂P,
      q ω j = OscDual.eval (Z ω) (E.test j)) :
    ∀ f : Euc d → ℝ, IsR2Test f →
      (fun ω => fp81s21_chartAction E (q ω) f) =ᵐ[P]
        (fun ω => OscDual.eval (Z ω) f) := by
  intro f hf
  let c := E.encode f
  let fn : ℕ → compactSmoothSubmodule d := chartSection E c
  let X : Ω → ℝ := fun ω => OscDual.eval (Z ω) f
  let Xn : ℕ → Ω → ℝ := fun n ω => OscDual.eval (Z ω) (fn n)
  let Y : Ω → ℝ := fun ω => inner ℝ (q ω) c
  let Yn : ℕ → Ω → ℝ := fun n ω => inner ℝ (q ω) (coeffSection c n)
  have hX : MemLp X 2 P := (hsecond f hf).1
  have hXn : ∀ n, MemLp (Xn n) 2 P := fun n => (hsecond (fn n) (fn n).property).1
  have hY : MemLp Y 2 P := hq.inner_const c
  have hYn : ∀ n, MemLp (Yn n) 2 P := fun n => hq.inner_const _
  have hfinite : ∀ n, Yn n =ᵐ[P] Xn n := by
    intro n
    filter_upwards [ae_all_iff.mpr hcoord] with ω hω
    dsimp [Yn, Xn, fn]
    rw [inner_coeffSection, chartSection_eval]
    exact Finset.sum_congr rfl fun j _ => by rw [hω j]
  have hsub : ∀ n ω, OscDual.eval (Z ω) ((fn n : Euc d → ℝ) - f) = Xn n ω - X ω := by
    intro n ω
    let a : oscSub d m := ⟨fn n, r2Test_isOscTest m (fn n).property⟩
    let b : oscSub d m := ⟨f, r2Test_isOscTest m hf⟩
    simpa only [gaussianTestEvaluation_apply, Submodule.coe_sub, a, b, Xn, X] using
      (map_sub (gaussianTestEvaluation (Z ω)) a b)
  have hfw : IsR2WeightedTest r Pw f :=
    weightedTestSubmodule_iff.1 (weighted_test_of_compact_smooth hP hf)
  have hlimX : Tendsto (fun n => ∫ ω, (Xn n ω - X ω) ^ 2 ∂P) atTop (𝓝 0) := by
    have he := chartSection_error_tendsto E hP f hfw
    have hu : Tendsto (fun n => C * (weightedSobolevE r Pw
        ((fn n : Euc d → ℝ) - f)).toReal ^ 2) atTop (𝓝 0) := by
      simpa using (he.pow 2).const_mul C
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hu
      (fun n => integral_nonneg fun _ => sq_nonneg _) ?_
    intro n
    have ht : IsR2Test ((fn n : Euc d → ℝ) - f) :=
      (compactSmoothSubmodule d).sub_mem (fn n).property hf
    simpa only [hsub n] using (hsecond _ ht).2
  have hlimY : Tendsto (fun n => ∫ ω, (Yn n ω - Y ω) ^ 2 ∂P) atTop (𝓝 0) :=
    inner_pairing_square_tendsto P q hq c (coeffSection c) (coeffSection_tendsto c)
  let g : Ω → ℝ := fun ω => Y ω - X ω
  have hg : MemLp g 2 P := hY.sub hX
  have hyl := integral_mul_tendsto_of_square_error P Yn Y g hYn hY hg hlimY
  have hxl := integral_mul_tendsto_of_square_error P Xn X g hXn hX hg hlimX
  have heq : (∫ ω, Y ω * g ω ∂P) = ∫ ω, X ω * g ω ∂P := by
    apply tendsto_nhds_unique hyl
    apply hxl.congr'
    filter_upwards [] with n
    apply integral_congr_ae
    filter_upwards [hfinite n] with ω hω
    rw [hω]
  have hzero : (∫ ω, g ω ^ 2 ∂P) = 0 := by
    have hi := integral_sub (hY.integrable_mul hg) (hX.integrable_mul hg)
    change (∫ ω, Y ω * g ω - X ω * g ω ∂P) =
      (∫ ω, Y ω * g ω ∂P) - (∫ ω, X ω * g ω ∂P) at hi
    have hid : (fun ω => Y ω * g ω - X ω * g ω) = fun ω => g ω ^ 2 := by
      funext ω
      dsimp [g]
      ring
    rw [hid, heq, sub_self] at hi
    exact hi
  have hae := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (g ω)) hg.integrable_sq).1 hzero
  filter_upwards [hae] with ω hω
  have hz : g ω = 0 := (sq_eq_zero_iff).1 hω
  change Y ω = X ω
  dsimp [g] at hz
  linarith

#print axioms fp81s21_oscillator_testwise_of_secondMoment_bound
end HRS.Fp81.S21
end
