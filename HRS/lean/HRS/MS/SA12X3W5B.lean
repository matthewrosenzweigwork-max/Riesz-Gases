import HRS.MS.SA12X3W5A

/-!
# S.A.12 C5-T06 (SA12X3), part B: joint continuity of jets under dilation; the lifted density family
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ComplexConjugate ContDiff

namespace HRS.PDE.SA12W2

variable {d : ℕ}

open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Construction

theorem sa12x3w_jc_scale {t c : ℝ} (hc : c ≠ 0) {f : ℝ → Euc d → ℝ}
    (hsm : ∀ τ ∈ Icc (0 : ℝ) t, ContDiff ℝ ∞ (f τ))
    (hjets : ∀ j : ℕ, ContinuousOn (fun q : ℝ × Euc d => iteratedFDeriv ℝ j (f q.1) q.2) (Icc (0 : ℝ) t ×ˢ univ))
    (a : ℝ) (j : ℕ) :
    ContinuousOn (fun q : ℝ × Euc d => iteratedFDeriv ℝ j (fun y => a * f q.1 (c • y)) q.2)
      (Icc (0 : ℝ) t ×ˢ univ) := by
  have hcomp : ContinuousOn (fun q : ℝ × Euc d => iteratedFDeriv ℝ j (f q.1) (c • q.2))
      (Icc (0 : ℝ) t ×ˢ univ) := by
    have hmap : ContinuousOn (fun q : ℝ × Euc d => (q.1, c • q.2)) (Icc (0 : ℝ) t ×ˢ univ) :=
      (by fun_prop : Continuous fun q : ℝ × Euc d => (q.1, c • q.2)).continuousOn
    exact (hjets j).comp hmap (fun q hq => ⟨hq.1, mem_univ _⟩)
  have hfun : ∀ q ∈ Icc (0 : ℝ) t ×ˢ (univ : Set (Euc d)),
      a • (c ^ j • iteratedFDeriv ℝ j (f q.1) (c • q.2)) = iteratedFDeriv ℝ j (fun y => a * f q.1 (c • y)) q.2 := by
    intro q hq
    have hs := hsm q.1 hq.1
    have hsc : ContDiff ℝ ∞ (fun y => f q.1 (c • y)) := hs.comp (contDiff_const_smul c)
    have := iteratedFDeriv_const_smul_apply' (a := a) (i := j) (f := fun y => f q.1 (c • y)) (x := q.2)
      (hsc.of_le (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).contDiffAt
    simp only [smul_eq_mul] at this
    rw [this, HRS.MS.Ker1.ker1_iteratedFDeriv_comp_smul (f q.1) hc j q.2]
  exact ((hcomp.const_smul (c ^ j)).const_smul a).congr (fun q hq => (hfun q hq).symm)

theorem sa12x3w_dens_JC {L T t : ℝ} (hL : 0 < L) (ht : t ≤ T) {μ : ℝ → Euc d → ℝ}
    (hTime : HRS.MH.AdjointRd.Phase2SA12Construction.PeriodicTimeSmooth T μ) (hsm : ∀ τ ∈ Icc (0 : ℝ) T, ContDiff ℝ ∞ (μ τ))
    (hper : ∀ τ ∈ Icc (0 : ℝ) T, ∀ (x : Euc d) (z : Fin d → ℤ), μ τ (x + L • latticePt z) = μ τ x) :
    sa12w2_JC t (fun τ => sa12w2_dens L (μ τ)) := by
  have hlift : ∀ τ ∈ Icc (0 : ℝ) t, Torus.lift (sa12w2_dens L (μ τ)) = fun y => L ^ d * μ τ (L • y) :=
    fun τ hτ => funext fun y => sa12w2_dens_lift (hper τ ⟨hτ.1, hτ.2.trans ht⟩) y
  have hsub : Icc (0 : ℝ) t ×ˢ (univ : Set (Euc d)) ⊆ Icc (0 : ℝ) T ×ˢ univ :=
    prod_mono (Icc_subset_Icc_right ht) subset_rfl
  refine ⟨fun τ hτ => ?_, fun j => ?_⟩
  · rw [hlift τ hτ]
    exact contDiff_const.mul ((hsm τ ⟨hτ.1, hτ.2.trans ht⟩).comp (contDiff_const_smul L))
  · have := sa12x3w_jc_scale (t := t) (c := L) hL.ne' (f := μ) (fun τ hτ => hsm τ ⟨hτ.1, hτ.2.trans ht⟩)
      (fun j => (hTime j).mono hsub) (L ^ d) j
    refine this.congr fun q hq => ?_
    rw [hlift q.1 hq.1]

end HRS.PDE.SA12W2
