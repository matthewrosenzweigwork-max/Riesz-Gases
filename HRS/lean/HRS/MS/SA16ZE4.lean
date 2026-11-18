import HRS.MS.SA16ZE3

/-!
# S.A.16 (SA16Z) E4: `L^p` norms versus integrals of `|D^kφ|^p`
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section E4
variable {d : ℕ}

lemma sa16z_lintegral_rpow_eq {f : Euc d → ℝ} (hf : AEStronglyMeasurable f volume) {p : ℝ} (hp : 0 < p) :
    ∫⁻ x, ENNReal.ofReal (|f x| ^ p) = (eLpNorm f (ENNReal.ofReal p) volume) ^ p := by
  have hne0 : ENNReal.ofReal p ≠ 0 := by simpa using hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hne0 ENNReal.ofReal_ne_top hf, ENNReal.toReal_ofReal hp.le]
  rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one]
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp.le]

lemma sa16z_vn_memLp {φ : Euc d → ℝ} (hφ : IsCcInfty φ) (k : ℕ) {p : ℝ} :
    MemLp (sa16sz_vn φ k) (ENNReal.ofReal p) volume :=
  (sa16sz_vn_cont φ hφ.1 k).memLp_of_hasCompactSupport (sa16sz_vn_cs hφ k)

lemma sa16z_JJ_lt_top {φ : Euc d → ℝ} (hφ : IsCcInfty φ) (k : ℕ) {p : ℝ} :
    sa16z_JJ p φ k < ⊤ := (sa16z_vn_memLp hφ k).eLpNorm_lt_top

lemma sa16z_JJ_rpow {φ : Euc d → ℝ} (hφ : IsCcInfty φ) (k : ℕ) {p : ℝ} (hp : 1 ≤ p) :
    (sa16z_JJ p φ k).toReal ^ p = ∫ x, sa16sz_vn φ k x ^ p := by
  have hp0 : 0 < p := by linarith
  have hint : Integrable (fun x => sa16sz_vn φ k x ^ p) :=
    ((sa16sz_vn_pow_cont φ hφ.1 k hp0.le).integrable_of_hasCompactSupport (sa16sz_vn_pow_cs hφ k hp0))
  have h1 := sa16z_lintegral_rpow_eq (sa16sz_vn_cont φ hφ.1 k).aestronglyMeasurable hp0
  have h2 : ∫⁻ x, ENNReal.ofReal (|sa16sz_vn φ k x| ^ p) = ENNReal.ofReal (∫ x, sa16sz_vn φ k x ^ p) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x =>
      Real.rpow_nonneg (sa16sz_vn_nonneg φ k x) _)]
    refine lintegral_congr fun x => ?_
    rw [abs_of_nonneg (sa16sz_vn_nonneg φ k x)]
  rw [h2] at h1
  have := congrArg ENNReal.toReal h1
  rw [ENNReal.toReal_ofReal (integral_nonneg fun x => Real.rpow_nonneg (sa16sz_vn_nonneg φ k x) _),
    ← ENNReal.toReal_rpow] at this
  exact this.symm

/-- `S_N^p ≤ (N+1)^{p-1} ∑_k ∫ |D^kφ|^p` -/
lemma sa16z_S_rpow_le {φ : Euc d → ℝ} (hφ : IsCcInfty φ) (N : ℕ) {p : ℝ} (hp : 1 ≤ p) :
    (sa16z_S p φ N).toReal ^ p ≤ ((N : ℝ) + 1) ^ (p - 1) * ∑ k ∈ Finset.range (N + 1), ∫ x, sa16sz_vn φ k x ^ p := by
  have hp0 : 0 < p := by linarith
  have hfin : ∀ k ∈ Finset.range (N + 1), sa16z_JJ p φ k ≠ ⊤ := fun k _ => (sa16z_JJ_lt_top hφ k).ne
  have hS : (sa16z_S p φ N).toReal = ∑ k ∈ Finset.range (N + 1), (sa16z_JJ p φ k).toReal := by
    unfold sa16z_S; rw [ENNReal.toReal_sum hfin]
  rw [hS]
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hjen := Real.rpow_arith_mean_le_arith_mean_rpow (Finset.range (N + 1))
    (fun _ => 1 / ((N : ℝ) + 1)) (fun k => (sa16z_JJ p φ k).toReal) (fun _ _ => by positivity)
    (by simp; field_simp) (fun k _ => ENNReal.toReal_nonneg) hp
  simp only [← Finset.mul_sum] at hjen
  have e : ∑ k ∈ Finset.range (N + 1), (sa16z_JJ p φ k).toReal =
      ((N : ℝ) + 1) * (1 / ((N : ℝ) + 1) * ∑ k ∈ Finset.range (N + 1), (sa16z_JJ p φ k).toReal) := by
    field_simp
  rw [e, Real.mul_rpow hN.le (by positivity)]
  have h2 : ((N : ℝ) + 1) ^ p = ((N : ℝ) + 1) ^ (p - 1) * ((N : ℝ) + 1) := by
    rw [← Real.rpow_add_one hN.ne']; congr 1; ring
  rw [h2, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  calc ((N : ℝ) + 1) * (1 / ((N : ℝ) + 1) * ∑ k ∈ Finset.range (N + 1), (sa16z_JJ p φ k).toReal) ^ p
      ≤ ((N : ℝ) + 1) * (1 / ((N : ℝ) + 1) * ∑ k ∈ Finset.range (N + 1), (sa16z_JJ p φ k).toReal ^ p) :=
        mul_le_mul_of_nonneg_left hjen hN.le
    _ = ∑ k ∈ Finset.range (N + 1), (sa16z_JJ p φ k).toReal ^ p := by field_simp
    _ = _ := Finset.sum_congr rfl fun k _ => sa16z_JJ_rpow hφ k hp

end E4

end HRS.Whole.AppendixA.Phase2SA16R
