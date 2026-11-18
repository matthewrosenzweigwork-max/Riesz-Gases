import HRS.MS.SA16SHw5
import HRS.MS.SA16StrongLeib

/-!
# S.A.16 (SA16S) Op1: operators on `WmpSpace` from linear maps on `C_c^∞` with a pointwise jet bound

`sa16so_extend`: if `L : C_c^∞ → C^∞` is linear and `‖jet_k (L φ) (x)‖ ≤ C ‖jet_l φ (x)‖` pointwise, then
`L` extends to a continuous linear map `T : WmpSpace d l p → WmpSpace d k p` of norm `≤ C` whose zeroth component
on the jet of `φ ∈ C_c^∞` is `L φ`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Op1
variable {d : ℕ}

lemma sa16so_S_le_jet (k : ℕ) (g : Euc d → ℝ) (x : Euc d) :
    sa16j_S d k g x ≤ (∑ j ∈ Finset.range (k + 1), (d : ℝ) ^ j) * ‖wJet k g x‖ := by
  unfold sa16j_S
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun j hj =>
    sa16y_iter_le_jet g x (by have := Finset.mem_range.1 hj; omega)

theorem sa16so_extend (d k l : ℕ) (p : ℝ) [Fact (2 ≤ p)] (L : ccSub d →ₗ[ℝ] (Euc d → ℝ))
    (hL : ∀ φ, ContDiff ℝ ∞ (L φ)) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ (φ : ccSub d) x, ‖wJet k (L φ) x‖ ≤ C * ‖wJet l φ.1 x‖) :
    ∃ T : WmpSpace d l p →L[ℝ] WmpSpace d k p, ‖T‖ ≤ C ∧
      ∀ φ : ccSub d, wrep d k p (T (sa16r_Jcc d l p φ)) =ᵐ[volume] L φ := by
  have hjl : ∀ φ : ccSub d, MemLp (fun x => ‖wJet l φ.1 x‖) (ENNReal.ofReal p) volume :=
    fun φ => (sa16r_jet_memLp_cc (p := p) φ.2 l).norm
  have hS : ∀ φ : ccSub d, MemLp (sa16j_S d k (L φ)) (ENNReal.ofReal p) volume := by
    intro φ
    refine ((hjl φ).const_mul ((∑ j ∈ Finset.range (k + 1), (d : ℝ) ^ j) * C)).mono'
      (sa16j_S_cont (hL φ) k).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sa16j_S_nonneg d k _ x)]
    refine (sa16so_S_le_jet k _ x).trans ?_
    have h0 : 0 ≤ ∑ j ∈ Finset.range (k + 1), (d : ℝ) ^ j := Finset.sum_nonneg fun _ _ => by positivity
    calc (∑ j ∈ Finset.range (k + 1), (d : ℝ) ^ j) * ‖wJet k (L φ) x‖
        ≤ (∑ j ∈ Finset.range (k + 1), (d : ℝ) ^ j) * (C * ‖wJet l φ.1 x‖) :=
          mul_le_mul_of_nonneg_left (hb φ x) h0
      _ = _ := by ring
  have hmem : ∀ φ : ccSub d, L φ ∈ sa16r_S d k p := fun φ => sa16r_mem_S k (hL φ) (hS φ)
  let 𝓛 : ccSub d →ₗ[ℝ] sa16r_S d k p :=
    { toFun := fun φ => ⟨L φ, hmem φ⟩
      map_add' := fun a b => Subtype.ext (L.map_add a b)
      map_smul' := fun c a => Subtype.ext (L.map_smul c a) }
  have hb' : ∀ φ, ‖sa16r_J d k p (𝓛 φ)‖ ≤ C * ‖sa16r_Jcc d l p φ‖ := by
    intro φ
    have h0 : ‖sa16r_J d k p (⟨L φ, hmem φ⟩ : sa16r_S d k p)‖ =
        (eLpNorm (wJet k (L φ)) (ENNReal.ofReal p) volume).toReal :=
      sa16r_J_norm k (f := ⟨L φ, hmem φ⟩) (hS φ)
    show ‖sa16r_J d k p (⟨L φ, hmem φ⟩ : sa16r_S d k p)‖ ≤ _
    rw [h0, sa16r_Jcc_norm]
    have hfin : eLpNorm (wJet l φ.1) (ENNReal.ofReal p) volume ≠ ⊤ :=
      (sa16r_jet_memLp_cc (p := p) φ.2 l).eLpNorm_lt_top.ne
    have h1 : eLpNorm (wJet k (L φ)) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C * eLpNorm (wJet l φ.1) (ENNReal.ofReal p) volume := by
      have : eLpNorm (wJet k (L φ)) (ENNReal.ofReal p) volume ≤
          eLpNorm (fun x => C • wJet l φ.1 x) (ENNReal.ofReal p) volume := by
        refine eLpNorm_mono (sa16j_jet_cont (hL φ) k).aestronglyMeasurable fun x => ?_
        simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hC]
        exact hb φ x
      refine this.trans (le_of_eq ?_)
      rw [show (fun x => C • wJet l φ.1 x) = C • wJet l φ.1 from rfl, eLpNorm_const_smul,
        Real.enorm_eq_ofReal hC]
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) h1
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] at h2
  obtain ⟨T, hT1, hT2, -⟩ := sa16r_extend_cc d l k p 𝓛 hC hb'
  refine ⟨T, hT1, fun φ => ?_⟩
  rw [hT2 φ]
  exact sa16r_J_spec d k p (𝓛 φ)

end Op1

end HRS.Whole.AppendixA.Phase2SA16R
