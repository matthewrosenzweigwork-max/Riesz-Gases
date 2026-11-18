import HRS.MS.SA16RHeat15

/-!
# S.A.16 (SA16R) Heat16: strong continuity of the heat operator at `0+`

`sa16r_H_tendsto`: for every `G ∈ WmpSpace d (k+1) p`, `H_a G → G` as `a → 0+`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Heat16
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16r_H_tendsto_cc (k : ℕ) (φ : ccSub d) :
    Tendsto (fun a : ℝ => sa16r_H d k p a (sa16r_Jcc d (k + 1) p φ)) (𝓝[>] 0)
      (𝓝 (sa16r_Jcc d (k + 1) p φ)) := by
  have hp : (1 : ℝ) ≤ p := by have := (Fact.out : 2 ≤ p); linarith
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set fφ : sa16r_S d (k + 1) p := ⟨φ.1, ccSub_le_S d (k + 1) p φ.2⟩ with hfφ
  have hJφ : sa16r_Jcc d (k + 1) p φ = sa16r_J d (k + 1) p fφ := rfl
  have hSφ : MemLp (sa16j_S d (k + 1) fφ.1) (ENNReal.ofReal p) volume := sa16r_cc_S_memLp φ.2 (k + 1)
  have hsum : Tendsto (fun a : ℝ => ∑ τ : WIndex d (k + 1), eLpNorm (fun x =>
      sa16r_cv (sa16r_g d a) (partialDeriv τ.2 φ.1) x - partialDeriv τ.2 φ.1 x)
      (ENNReal.ofReal p) volume) (𝓝[>] 0) (𝓝 0) := by
    have := tendsto_finsetSum (Finset.univ : Finset (WIndex d (k + 1))) (fun τ _ =>
      sa16r_approx_id_eLp (sa16s_cc_partialDeriv φ.2 τ.2) hp)
    simpa using this
  have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsum
  simp only [ENNReal.toReal_zero] at hreal
  refine squeeze_zero' (Eventually.of_forall fun a => norm_nonneg _) ?_ hreal
  filter_upwards [self_mem_nhdsWithin] with a ha
  have ha' : 0 < a := ha
  simp only [Function.comp]
  rw [sa16r_H_Jcc ha' k φ, hJφ]
  have hS1 : MemLp (sa16j_S d (k + 1) (sa16r_heatL d p ha' k φ).1) (ENNReal.ofReal p) volume :=
    sa16r_heat_S_memLp ha' φ.2 (k + 0)
  rw [sa16r_J_sub_norm (k + 1) hS1 hSφ]
  have hle := sa16r_jet_le_sum (sa16r_cv_contDiff ha' φ.2) φ.2.1 (k + 1) hp (p := p)
  have hfin : (∑ τ : WIndex d (k + 1), eLpNorm (fun x =>
      sa16r_cv (sa16r_g d a) (partialDeriv τ.2 φ.1) x - partialDeriv τ.2 φ.1 x)
      (ENNReal.ofReal p) volume) ≠ ⊤ := by
    refine ne_of_lt (ENNReal.sum_lt_top.2 fun τ _ => ?_)
    have hu := sa16s_cc_partialDeriv φ.2 (j := τ.1) τ.2
    exact (MemLp.sub (sa16r_cv_memLp sa16r_g_meas (sa16r_g_int ha') hu.1.continuous hp
      (sa16r_cc_memLp hu)) (sa16r_cc_memLp hu)).eLpNorm_lt_top
  have hEq : (∑ τ : WIndex d (k + 1), eLpNorm (fun x => partialDeriv τ.2 (sa16r_cv (sa16r_g d a) φ.1) x -
      partialDeriv τ.2 φ.1 x) (ENNReal.ofReal p) volume) =
      ∑ τ : WIndex d (k + 1), eLpNorm (fun x =>
        sa16r_cv (sa16r_g d a) (partialDeriv τ.2 φ.1) x - partialDeriv τ.2 φ.1 x) (ENNReal.ofReal p) volume := by
    refine Finset.sum_congr rfl fun τ _ => ?_
    congr 1
    funext x
    rw [sa16r_cv_pd ha' φ.2 τ.1 τ.2]
  exact ENNReal.toReal_mono hfin (hle.trans (le_of_eq hEq))

theorem sa16r_H_tendsto (k : ℕ) (G : WmpSpace d (k + 1) p) :
    Tendsto (fun a : ℝ => sa16r_H d k p a G) (𝓝[>] 0) (𝓝 G) := by
  have h := sa16r_tendsto_of_dense (l := 𝓝[>] (0 : ℝ)) (fun a => sa16r_H d k p a)
    (ContinuousLinearMap.id ℝ (WmpSpace d (k + 1) p)) (B := 1)
    (by filter_upwards [self_mem_nhdsWithin] with a ha using sa16r_H_opNorm (p := p) ha k)
    ContinuousLinearMap.norm_id_le (D := Set.range (sa16r_Jcc d (k + 1) p))
    (sa16r_Jcc_dense d (k + 1) p)
    (by
      rintro z ⟨φ, rfl⟩
      simpa using sa16r_H_tendsto_cc (p := p) k φ) G
  simpa using h

end Heat16

end HRS.Whole.AppendixA.Phase2SA16R
