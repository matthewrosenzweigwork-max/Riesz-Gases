import HRS.MS.PROS15ETiltL4
import HRS.MS.PROS15dTiltBound
import HRS.MC.E213U13j

/-!
# Second Gaussian chaos: quantitative L2 continuity under exponential tilting

This supplies the analytic passage from reference-L2 convergence of genuinely
second-chaos random variables to L2 convergence under the same fixed normalized
exponential tilt. The constant is explicit and requires only the second
exponential moment. No finite-rank or smoothness restriction is imposed on
the second-chaos variables.
-/

set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS.MC.E213U13

theorem s15e_second_chaos_tilted_second_bound
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} {hξ : IsStdGaussianSeq P ξ}
    {V F : Ω → ℝ}
    (hV : AEMeasurable V P)
    (hExp2 : Integrable (fun ω => Real.exp (-(2 * V ω))) P)
    (hF : InQ2 hξ F) :
    ∫ ω, F ω ^ 2 ∂(r26t3_tilt P V) ≤
      (∫ ω, Real.exp (-V ω) ∂P)⁻¹ *
        ((Real.sqrt 15 * (∫ ω, F ω ^ 2 ∂P)) *
          Real.sqrt (∫ ω, Real.exp (-(2 * V ω)) ∂P)) := by
  have hExp2' : Integrable (fun ω => Real.exp (-2 * V ω)) P := by
    convert hExp2 using 1
    funext ω
    congr 1
    ring
  have hExp1 : Integrable (fun ω => Real.exp (-V ω)) P :=
    s21g2_s15a_int1 (P := P) hV (r := (2 : ℝ)) (by norm_num) hExp2'
  have hFour := s21l_inQ2_four hF
  have hNonneg : 0 ≤ ∫ ω, F ω ^ 2 ∂P :=
    integral_nonneg (fun ω => sq_nonneg _)
  have hSqrt : Real.sqrt (∫ ω, F ω ^ 4 ∂P) ≤
      Real.sqrt 15 * (∫ ω, F ω ^ 2 ∂P) := by
    calc
      Real.sqrt (∫ ω, F ω ^ 4 ∂P) ≤
          Real.sqrt (15 * (∫ ω, F ω ^ 2 ∂P) ^ 2) :=
            Real.sqrt_le_sqrt hFour.2
      _ = Real.sqrt 15 * (∫ ω, F ω ^ 2 ∂P) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 15),
          Real.sqrt_sq_eq_abs, abs_of_nonneg hNonneg]
  have hBase := s15d_tilted_second_moment_bound
    (P := P) (V := V) (F := F) hV hExp1 hExp2
    (s15e_inQ2_memLp_four hF)
  have hZ : 0 < ∫ ω, Real.exp (-V ω) ∂P :=
    s21g2_s15a_Z_pos P hV hExp1
  exact hBase.trans
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right hSqrt (Real.sqrt_nonneg _))
      (inv_nonneg.2 hZ.le))

/-- On a fixed probability space, Gaussian second-chaos L2 convergence
persists under a fixed normalized exponential tilt whose squared density
has a finite reference expectation. -/
theorem s15e_second_chaos_tilted_second_convergence
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ξ : ℕ → Ω → ℝ} {hξ : IsStdGaussianSeq P ξ}
    {V : Ω → ℝ}
    (hV : AEMeasurable V P)
    (hExp2 : Integrable (fun ω => Real.exp (-(2 * V ω))) P)
    (Y : ℕ → Ω → ℝ) (Z : Ω → ℝ)
    (hY : ∀ n, InQ2 hξ (Y n)) (hZ : InQ2 hξ Z)
    (hL2 : Tendsto
      (fun n => ∫ ω, (Y n ω - Z ω) ^ 2 ∂P) atTop (𝓝 0)) :
    Tendsto
      (fun n => ∫ ω, (Y n ω - Z ω) ^ 2 ∂(r26t3_tilt P V))
      atTop (𝓝 0) := by
  have hDiff : ∀ n, InQ2 hξ (fun ω => Y n ω - Z ω) := by
    intro n
    have hMinus := InQ2.const_mul (-1 : ℝ) hZ
    have hSum := InQ2.add (hY n) hMinus
    convert hSum using 1
    funext ω
    ring
  have hBound : ∀ n,
      (∫ ω, (Y n ω - Z ω) ^ 2 ∂(r26t3_tilt P V)) ≤
        (∫ ω, Real.exp (-V ω) ∂P)⁻¹ *
          ((Real.sqrt 15 * (∫ ω, (Y n ω - Z ω) ^ 2 ∂P)) *
            Real.sqrt (∫ ω, Real.exp (-(2 * V ω)) ∂P)) := by
    intro n
    exact s15e_second_chaos_tilted_second_bound
      P hV hExp2 (hDiff n)
  have htend : Tendsto (fun n =>
        (∫ ω, Real.exp (-V ω) ∂P)⁻¹ *
          ((Real.sqrt 15 * (∫ ω, (Y n ω - Z ω) ^ 2 ∂P)) *
            Real.sqrt (∫ ω, Real.exp (-(2 * V ω)) ∂P))) atTop (𝓝 0) := by
    convert (((hL2.const_mul (Real.sqrt 15)).mul_const
      (Real.sqrt (∫ ω, Real.exp (-(2 * V ω)) ∂P))).const_mul
      ((∫ ω, Real.exp (-V ω) ∂P)⁻¹)) using 1 <;> ring
  exact squeeze_zero
    (fun n => integral_nonneg (fun ω => sq_nonneg _)) hBound htend

#print axioms s15e_second_chaos_tilted_second_bound
#print axioms s15e_second_chaos_tilted_second_convergence
end HRS.MS.R26T3
