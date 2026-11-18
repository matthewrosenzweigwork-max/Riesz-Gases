import HRS.MS.SA16V2Jets

/-!
# S.A.16 (SA16Y9) Dj1: the derivative of `∫‖f‖^p` in a direction (stability, P1, part 1)

`sa16y9_uLp_norm`: `‖g(f)‖_{L^{p'}} = ‖f‖_{L^p}^{p-1}`; `sa16y9_D_le`: `D(f) h ≤ p ‖f‖^{p-1} ‖h‖`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.Whole.AppendixA.Phase2SA16S
open HRS.Whole.AppendixA.Phase2SA16V HRS.Whole.AppendixA.Phase2SA16V2

section Dj1
variable {α : Type*} {m : MeasurableSpace α} {μ : Measure α} {V : Type*} [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] (p : ℝ) [Fact (2 ≤ p)]

lemma sa16y9_uLp_norm (f : Lp V (ENNReal.ofReal p) μ) : ‖sa16v_uLp p f‖ = ‖f‖ ^ (p - 1) := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  have hp1 : 1 < p := by linarith
  have hq0 : 0 < Real.conjExponent p := (Real.HolderConjugate.conjExponent hp1).symm.pos
  have hP0 : ENNReal.ofReal (Real.conjExponent p) ≠ 0 := by simpa using hq0
  set u := sa16v_uLp p f with hu
  have h := (Lp.memLp u).eLpNorm_eq_integral_rpow_norm hP0 ENNReal.ofReal_ne_top
  rw [ENNReal.toReal_ofReal hq0.le] at h
  have hqe : Real.conjExponent p = p / (p - 1) := rfl
  have hp1' : p - 1 ≠ 0 := by linarith
  have hint : ∫ x, ‖u x‖ ^ Real.conjExponent p ∂μ = ‖f‖ ^ p := by
    rw [sa16v2_norm_pow_eq p f]
    refine integral_congr_ae ?_
    filter_upwards [sa16v_uLp_coe p f] with x hx
    rw [hx, sa16v_norm_g _ (by linarith)]
    have e : p - 2 + 1 = p - 1 := by ring
    rw [e, ← Real.rpow_mul (norm_nonneg _), hqe]
    congr 1
    field_simp
  have hnn : 0 ≤ ∫ x, ‖u x‖ ^ Real.conjExponent p ∂μ :=
    integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  rw [Lp.norm_def, h, ENNReal.toReal_ofReal (Real.rpow_nonneg hnn _), hint,
    ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  rw [hqe]
  field_simp

lemma sa16y9_D_le (f h : Lp V (ENNReal.ofReal p) μ) : sa16v_D p f h ≤ p * (‖f‖ ^ (p - 1) * ‖h‖) := by
  have hp0 : 0 ≤ p := by have : (2 : ℝ) ≤ p := Fact.out; linarith
  rw [sa16v_D_apply]
  refine mul_le_mul_of_nonneg_left ?_ hp0
  have := sa16v_pair_le p h (sa16v_uLp p f)
  rw [sa16y9_uLp_norm] at this
  calc ∫ x, ⟪h x, sa16v_g (p - 2) (f x)⟫ ∂μ = ∫ x, ⟪h x, (sa16v_uLp p f) x⟫ ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [sa16v_uLp_coe p f] with x hx
        rw [hx]
    _ ≤ |∫ x, ⟪h x, (sa16v_uLp p f) x⟫ ∂μ| := le_abs_self _
    _ ≤ ‖h‖ * ‖f‖ ^ (p - 1) := this
    _ = ‖f‖ ^ (p - 1) * ‖h‖ := mul_comm _ _

end Dj1

end HRS.Whole.AppendixA.Phase2SA16S
