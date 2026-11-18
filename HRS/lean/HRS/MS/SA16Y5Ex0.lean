import HRS.MS.SA16Y5Lb6
import HRS.MS.SA16RHeat14

/-!
# S.A.16 (SA16Y5) Ex0: closed-jet extension of a linear family of smooth functions (K3, generic tool)

`sa16y5_ext_of_fun`: let `F : C_c^∞ → (ℝ^d → ℝ)` be linear, smooth-valued, with
`‖∂^idx F φ‖_p ≤ c0 ‖wJet k φ‖_p` for every `idx` of length `j ≤ l`.  Then there is a bounded linear
`T : W^{k,p} → W^{l,p}` with `‖T‖ ≤ card(WIndex d l) c0` and `wrep (T (Jcc φ)) = F φ` a.e.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Ex0

lemma sa16y5_Sjet_memLp {d l : ℕ} {p : ℝ} [Fact (2 ≤ p)] {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f)
    (h : ∀ {j : ℕ}, j ≤ l → ∀ idx : Fin j → Fin d, MemLp (partialDeriv idx f) (ENNReal.ofReal p) volume) :
    MemLp (sa16j_S d l f) (ENNReal.ofReal p) volume := by
  have hg : MemLp (fun x => ∑ j ∈ Finset.range (l + 1), ∑ r : Fin j → Fin d, |partialDeriv r f x|)
      (ENNReal.ofReal p) volume := by
    refine memLp_finsetSum _ fun j hj => memLp_finsetSum _ fun r _ => ?_
    exact (h (by have := Finset.mem_range.1 hj; omega) r).norm
  refine hg.mono' ?_ (Eventually.of_forall fun x => ?_)
  · exact (sa16j_S_cont hf l).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (sa16j_S_nonneg d l f x)]
    exact sa16j_S_le l f x

theorem sa16y5_ext_of_fun (d k l : ℕ) (p : ℝ) [Fact (2 ≤ p)] (F : ccSub d → Euc d → ℝ)
    (hadd : ∀ φ ψ, F (φ + ψ) = F φ + F ψ) (hsmul : ∀ (c : ℝ) φ, F (c • φ) = c • F φ)
    (hsm : ∀ φ, ContDiff ℝ ∞ (F φ)) {c0 : ℝ} (hc0 : 0 ≤ c0)
    (hpd : ∀ φ : ccSub d, ∀ {j : ℕ}, j ≤ l → ∀ idx : Fin j → Fin d,
      eLpNorm (partialDeriv idx (F φ)) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal c0 * eLpNorm (wJet k φ.1) (ENNReal.ofReal p) volume) :
    ∃ T : WmpSpace d k p →L[ℝ] WmpSpace d l p, ‖T‖ ≤ (Fintype.card (WIndex d l) : ℝ) * c0 ∧
      ∀ φ : ccSub d, wrep d l p (T (sa16r_Jcc d k p φ)) =ᵐ[volume] F φ := by
  have hEfin : ∀ φ : ccSub d, eLpNorm (wJet k φ.1) (ENNReal.ofReal p) volume ≠ ⊤ := fun φ =>
    (sa16r_jet_memLp_cc φ.2 k).eLpNorm_lt_top.ne
  have hS : ∀ φ : ccSub d, MemLp (sa16j_S d l (F φ)) (ENNReal.ofReal p) volume := by
    intro φ
    refine sa16y5_Sjet_memLp (hsm φ) (fun {j} hj idx => ?_)
    have hlt : eLpNorm (partialDeriv idx (F φ)) (ENNReal.ofReal p) volume < ⊤ :=
      lt_of_le_of_lt (hpd φ hj idx) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hEfin φ).lt_top)
    exact hlt
  let L : ccSub d →ₗ[ℝ] sa16r_S d l p :=
    { toFun := fun φ => ⟨F φ, sa16r_mem_S l (hsm φ) (hS φ)⟩
      map_add' := fun φ ψ => Subtype.ext (hadd φ ψ)
      map_smul' := fun c φ => Subtype.ext (hsmul c φ) }
  have hcc : 0 ≤ (Fintype.card (WIndex d l) : ℝ) * c0 := by positivity
  have hb : ∀ φ, ‖sa16r_J d l p (L φ)‖ ≤ ((Fintype.card (WIndex d l) : ℝ) * c0) * ‖sa16r_Jcc d k p φ‖ := by
    intro φ
    rw [sa16r_J_norm (f := L φ) l (hS φ), sa16r_Jcc_norm]
    have h1 : eLpNorm (wJet l (F φ)) (ENNReal.ofReal p) volume ≤
        (Fintype.card (WIndex d l) : ℝ≥0∞) * (ENNReal.ofReal c0 * eLpNorm (wJet k φ.1) (ENNReal.ofReal p) volume) := by
      rw [← sa16j_wNormE_eq d l p (hsm φ) (hS φ)]
      exact sa16y_wnorm_of_pd d l p (hsm φ) (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hEfin φ).lt_top)
        (fun {j} hj idx => hpd φ hj idx)
    have h2 := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (hEfin φ))) h1
    have e : ((Fintype.card (WIndex d l) : ℝ≥0∞) * (ENNReal.ofReal c0 * eLpNorm (wJet k φ.1) (ENNReal.ofReal p) volume)).toReal =
        ((Fintype.card (WIndex d l) : ℝ) * c0) * (eLpNorm (wJet k φ.1) (ENNReal.ofReal p) volume).toReal := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hc0, ENNReal.toReal_natCast]
      ring
    rw [e] at h2
    exact h2
  obtain ⟨T, hT, hTJ, -⟩ := sa16r_extend_cc d k l p L hcc hb
  refine ⟨T, hT, fun φ => ?_⟩
  rw [hTJ φ]
  exact sa16r_J_spec d l p (L φ)

end Ex0

end HRS.Whole.AppendixA.Phase2SA16R
