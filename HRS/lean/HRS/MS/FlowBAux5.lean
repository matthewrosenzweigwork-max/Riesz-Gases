import HRS.MS.FlowBAux2
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# MS-FLOW-B, invertibility of `1 + V` for a Volterra-type operator

`V : X →L X` with `‖V γ t‖ ≤ ∫_0^{clampT T t} Λ ‖γ s‖ ds`.  Then `‖V^n‖ ≤ (ΛT)^n / n!`, so `‖V^N‖ < 1`
for large `N`, and `1 + V` is a unit (`1 - (-V)^N` is a unit and commutes with the geometric factor).
-/

open MeasureTheory Filter Topology Set Metric
open scoped BoundedContinuousFunction Nat

namespace HRS.MS.FlowB

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem volterra_pow_bound {T Λ : ℝ} (hT : 0 ≤ T) (hΛ : 0 ≤ Λ) (L : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E))
    (hL : ∀ γ t, ‖L γ t‖ ≤ ∫ s in (0 : ℝ)..clampT T t, Λ * ‖γ s‖) :
    ∀ n : ℕ, ∀ γ : ℝ →ᵇ E, ∀ t, ‖(L ^ n) γ t‖ ≤ (Λ * clampT T t) ^ n / n ! * ‖γ‖ := by
  intro n
  induction n with
  | zero =>
    intro γ t
    simpa using γ.norm_coe_le_norm t
  | succ n ih =>
    intro γ t
    have hct := clampT_nonneg T t
    have hctT : clampT T t ≤ T := (clampT_mem hT t).2
    rw [pow_succ', ContinuousLinearMap.mul_apply]
    set η := (L ^ n) γ with hη
    refine (hL η t).trans ?_
    have hmono : ∫ s in (0 : ℝ)..clampT T t, Λ * ‖η s‖ ≤
        ∫ s in (0 : ℝ)..clampT T t, (Λ ^ (n + 1) * ‖γ‖ / n !) * s ^ n := by
      refine intervalIntegral.integral_mono_on hct ?_ ?_ fun s hs => ?_
      · exact ((η.continuous.norm.const_mul Λ)).intervalIntegrable _ _
      · exact (by fun_prop : Continuous fun s : ℝ => (Λ ^ (n + 1) * ‖γ‖ / n !) * s ^ n).intervalIntegrable _ _
      · have hs' : clampT T s = s := clampT_of_mem ⟨hs.1, hs.2.trans hctT⟩
        have := ih γ s
        rw [hs'] at this
        calc Λ * ‖η s‖ ≤ Λ * ((Λ * s) ^ n / n ! * ‖γ‖) := mul_le_mul_of_nonneg_left this hΛ
          _ = (Λ ^ (n + 1) * ‖γ‖ / n !) * s ^ n := by ring
    refine hmono.trans_eq ?_
    rw [intervalIntegral.integral_const_mul, integral_pow]
    rw [Nat.factorial_succ]
    push_cast
    field_simp
    ring

theorem opNorm_pow_le {T Λ : ℝ} (hT : 0 ≤ T) (hΛ : 0 ≤ Λ) (L : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E))
    (hL : ∀ γ t, ‖L γ t‖ ≤ ∫ s in (0 : ℝ)..clampT T t, Λ * ‖γ s‖) (n : ℕ) :
    ‖L ^ n‖ ≤ (Λ * T) ^ n / n ! := by
  have h0 : 0 ≤ (Λ * T) ^ n / n ! := by positivity
  refine ContinuousLinearMap.opNorm_le_bound _ h0 fun γ => ?_
  refine (BoundedContinuousFunction.norm_le (mul_nonneg h0 (norm_nonneg _))).2 fun t => ?_
  refine (volterra_pow_bound hT hΛ L hL n γ t).trans ?_
  have hct := clampT_nonneg T t
  have hctT : clampT T t ≤ T := (clampT_mem hT t).2
  gcongr

variable [CompleteSpace E]

theorem isUnit_one_add_volterra {T Λ : ℝ} (hT : 0 ≤ T) (hΛ : 0 ≤ Λ)
    (V : (ℝ →ᵇ E) →L[ℝ] (ℝ →ᵇ E))
    (hV : ∀ γ t, ‖V γ t‖ ≤ ∫ s in (0 : ℝ)..clampT T t, Λ * ‖γ s‖) :
    IsUnit (1 + V) := by
  have hV' : ∀ γ t, ‖(-V) γ t‖ ≤ ∫ s in (0 : ℝ)..clampT T t, Λ * ‖γ s‖ := fun γ t => by
    simpa using hV γ t
  obtain ⟨N, hN⟩ := ((FloorSemiring.tendsto_pow_div_factorial_atTop (Λ * T)).eventually
    (gt_mem_nhds (zero_lt_one' ℝ))).exists
  have hW : ‖(-V) ^ N‖ < 1 := (opNorm_pow_le hT hΛ (-V) hV' N).trans_lt hN
  have hu : IsUnit (1 - (-V) ^ N) := by
    have := (Units.oneSub ((-V) ^ N) hW).isUnit
    rwa [Units.val_oneSub] at this
  have hgeom : (1 + V) * ∑ i ∈ Finset.range N, (-V) ^ i = 1 - (-V) ^ N := by
    have := mul_neg_geom_sum (-V) N
    simpa using this
  have hcomm : Commute (1 + V) (∑ i ∈ Finset.range N, (-V) ^ i) := by
    refine Commute.sum_right _ _ _ fun i _ => ?_
    exact (Commute.one_left _).add_left
      ((Commute.neg_right (Commute.refl V)).pow_right i)
  rw [← hgeom] at hu
  exact ((Commute.isUnit_mul_iff hcomm).1 hu).1

end HRS.MS.FlowB
