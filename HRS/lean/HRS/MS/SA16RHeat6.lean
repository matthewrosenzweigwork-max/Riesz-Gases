import HRS.MS.SA16RHeat5

/-!
# S.A.16 (SA16R) Heat6: jet bounds and the gain operator

`sa16r_heat_mem`: `g_a ⋆ φ ∈ sa16r_S d (k+1) p` with `L^p` derivatives; `sa16r_heat_norm`: its `(k+1)`-jet has `L^p` norm
at most `‖K_a‖₁` times the `k`-jet norm of `φ`; `sa16r_Gam`: the extended operator.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution

section Heat6
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16r_cc_memLp {u : Euc d → ℝ} (hu : IsCcInfty u) : MemLp u (ENNReal.ofReal p) volume :=
  hu.1.continuous.memLp_of_hasCompactSupport hu.2

/-- every derivative of order `≤ k+1` of `g_a ⋆ φ` is in `L^p` -/
lemma sa16r_pd_heat_memLp {a : ℝ} (ha : 0 < a) {φ : Euc d → ℝ} (hφ : IsCcInfty φ) {k j : ℕ}
    (hj : j ≤ k + 1) (r : Fin j → Fin d) :
    MemLp (partialDeriv r (sa16r_cv (sa16r_g d a) φ)) (ENNReal.ofReal p) volume := by
  have hp : (1 : ℝ) ≤ p := by have := (Fact.out : 2 ≤ p); linarith
  rcases sa16r_pd_heat_eq ha hφ hj r with ⟨u, hu, -, h⟩ | ⟨i, u, hu, -, h⟩
  · rw [h]
    exact sa16r_cv_memLp sa16r_g_meas (sa16r_g_int ha) hu.1.continuous hp (sa16r_cc_memLp hu)
  · rw [h]
    exact sa16r_cv_memLp (sa16r_dg_cont a i).measurable (sa16r_dg_int ha i) hu.1.continuous hp
      (sa16r_cc_memLp hu)

lemma sa16r_heat_S_memLp {a : ℝ} (ha : 0 < a) {φ : Euc d → ℝ} (hφ : IsCcInfty φ) (k : ℕ) :
    MemLp (sa16j_S d (k + 1) (sa16r_cv (sa16r_g d a) φ)) (ENNReal.ofReal p) volume := by
  set f := sa16r_cv (sa16r_g d a) φ with hf
  have hg : MemLp (fun x => ∑ j ∈ Finset.range (k + 1 + 1), ∑ r : Fin j → Fin d, |partialDeriv r f x|)
      (ENNReal.ofReal p) volume := by
    refine memLp_finsetSum _ fun j hj => memLp_finsetSum _ fun r _ => ?_
    exact (sa16r_pd_heat_memLp (p := p) (k := k) ha hφ (by have := Finset.mem_range.1 hj; omega) r).norm
  refine hg.mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact (sa16j_S_cont (sa16r_cv_contDiff ha hφ) (k + 1)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (sa16j_S_nonneg d (k + 1) f x)]
    exact sa16j_S_le (k + 1) f x

lemma sa16r_heat_mem {a : ℝ} (ha : 0 < a) {φ : Euc d → ℝ} (hφ : IsCcInfty φ) (k : ℕ) :
    sa16r_cv (sa16r_g d a) φ ∈ sa16r_S d (k + 1) p :=
  sa16r_mem_S (k + 1) (sa16r_cv_contDiff ha hφ) (sa16r_heat_S_memLp ha hφ k)

/-- pointwise jet bound -/
lemma sa16r_jet_heat_pointwise {a : ℝ} (ha : 0 < a) {φ : Euc d → ℝ} (hφ : IsCcInfty φ) (k : ℕ)
    (x : Euc d) :
    ‖wJet (k + 1) (sa16r_cv (sa16r_g d a) φ) x‖ ≤
      sa16r_cv (sa16r_K d a) (fun y => ‖wJet k φ y‖) x := by
  have hm0 : ∀ y, 0 ≤ ‖wJet k φ y‖ := fun y => norm_nonneg _
  have hmc : Continuous (fun y => ‖wJet k φ y‖) := (sa16j_jet_cont hφ.1 k).norm
  have hmb : ∃ B, ∀ y, ‖wJet k φ y‖ ≤ B := by
    obtain ⟨B, hB⟩ := (sa16j_jet_cont hφ.1 k).norm.bounded_above_of_compact_support
      (sa16j_jet_support hφ.2 k).norm
    exact ⟨B, fun y => by simpa using hB y⟩
  have hnn : 0 ≤ sa16r_cv (sa16r_K d a) (fun y => ‖wJet k φ y‖) x := by
    unfold sa16r_cv
    exact integral_nonneg fun z => mul_nonneg (sa16r_K_nonneg ha z) (hm0 _)
  refine (pi_norm_le_iff_of_nonneg hnn).2 fun τ => ?_
  rw [Real.norm_eq_abs]
  have hτ : (τ.1 : ℕ) ≤ k + 1 := by have := τ.1.2; omega
  show |partialDeriv τ.2 (sa16r_cv (sa16r_g d a) φ) x| ≤ _
  rcases sa16r_pd_heat_eq ha hφ hτ τ.2 with ⟨u, hu, ⟨j', hj', r', rfl⟩, h⟩ | ⟨i, u, hu, ⟨r', rfl⟩, h⟩
  · rw [h]
    exact sa16r_cv_abs_le (sa16r_K_int ha) (sa16s_cc_partialDeriv hφ r') hm0 hmb hmc
      (fun z => sa16r_g_le_K ha z) (fun y => sa16j_pd_le_jet k φ y hj' r') x
  · rw [h]
    exact sa16r_cv_abs_le (sa16r_K_int ha) (sa16s_cc_partialDeriv hφ r') hm0 hmb hmc
      (fun z => sa16r_dg_le_K ha i z) (fun y => sa16j_pd_le_jet k φ y le_rfl r') x

end Heat6

end HRS.Whole.AppendixA.Phase2SA16R
