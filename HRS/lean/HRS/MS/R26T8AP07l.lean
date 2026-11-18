import HRS.MS.R26T8AP07k

/-!
# S8.2 local Newton layer, packet T8A.P07 (part l): joint smoothness of an annular Newton piece
`r26t8a_p07_T_contDiff`: `(Y, w) |-> annularNewton nu chi R F Y w` is `C^n` jointly (convolution with a locally integrable kernel of a `C^n`,
compactly supported in the relative variable, parametrised source).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Metric Convolution
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_p07_T_contDiff (hd : 2 ≤ d) (nu : ℝ) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {R : ℝ} (hR : 0 < R)
    {F : Euc d → Euc d → ℝ} {n : ℕ} (hF : ContDiffOn ℝ n (Function.uncurry F) {p | p.1 ≠ p.2}) :
    ContDiff ℝ (n : WithTop ℕ∞) (fun Yw : Euc d × Euc d => r26t8a_annularNewton nu chi R F Yw.1 Yw.2) := by
  have hKloc : LocallyIntegrable (newtonKernel d nu) (volume : Measure (Euc d)) := by
    rw [locallyIntegrable_iff]
    intro K hK
    obtain ⟨r, hr⟩ := hK.isBounded.subset_ball (0 : Euc d)
    exact (r26t8a_K_integrableOn hd nu r).mono_set hr
  have hS : ContDiff ℝ (n : WithTop ℕ∞) (fun Yw : Euc d × Euc d => r26t8a_annulus chi R Yw.2 * midPair F Yw.1 Yw.2) :=
    r26t8a_S_contDiff hchi hR hF
  have hvan : ∀ (Y : Euc d), ∀ x : Euc d, Y ∈ (Set.univ : Set (Euc d)) → x ∉ closedBall (0 : Euc d) (2 * R) →
      (fun Y x => r26t8a_annulus chi R x * midPair F Y x) Y x = 0 := by
    intro Y x _ hx
    rw [mem_closedBall, dist_zero_right, not_le] at hx
    simp [r26t8a_annulus_zero_large hchi hR hx.le]
  have hconv := contDiffOn_convolution_right_with_param (𝕜 := ℝ) (μ := (volume : Measure (Euc d)))
    (n := (n : ℕ∞)) (ContinuousLinearMap.mul ℝ ℝ) (f := newtonKernel d nu)
    (g := fun Y x : Euc d => r26t8a_annulus chi R x * midPair F Y x) (s := Set.univ)
    (k := closedBall (0 : Euc d) (2 * R)) isOpen_univ (isCompact_closedBall _ _) hvan hKloc
    (by
      have : ContDiff ℝ (n : ℕ∞) (Function.uncurry fun Y x : Euc d => r26t8a_annulus chi R x * midPair F Y x) :=
        by exact_mod_cast hS
      exact this.contDiffOn)
  have hcd : ContDiff ℝ (n : ℕ∞)
      (fun q : Euc d × Euc d => ((newtonKernel d nu) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
        (fun x : Euc d => r26t8a_annulus chi R x * midPair F q.1 x)) q.2) := by
    rw [← contDiffOn_univ]
    simpa using hconv
  have heq : (fun Yw : Euc d × Euc d => r26t8a_annularNewton nu chi R F Yw.1 Yw.2) =
      fun q : Euc d × Euc d => ((newtonKernel d nu) ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
        (fun x : Euc d => r26t8a_annulus chi R x * midPair F q.1 x)) q.2 := by
    funext q
    rw [convolution_def]
    unfold r26t8a_annularNewton
    rw [← integral_sub_left_eq_self (fun w : Euc d => newtonKernel d nu (q.2 - w) *
      r26t8a_annulus chi R w * midPair F q.1 w) volume q.2]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    simp only [sub_sub_cancel, ContinuousLinearMap.mul_apply']
    ring
  rw [heq]
  exact_mod_cast hcd

end HRS.MS.R26T8A
