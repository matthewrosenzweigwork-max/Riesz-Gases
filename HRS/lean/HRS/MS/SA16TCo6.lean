import HRS.MS.SA16TCo4

/-!
# S.A.16 (SA16T) Co6: strong continuity of the smoothed coefficients in the time parameter

`sa16t_bcv_cont`: if `(σ, y) ↦ b σ y` is continuous on `S × ℝ^d` (`S` compact), then for every `n, k` and `ε > 0` there is
`δ > 0` with `‖D^j (f_{n,σ,i} - f_{n,σ',i})‖ ≤ ε` for all `j ≤ k`, `|σ - σ'| < δ`; i.e. the difference of the coefficient
families is an `SA16BddCoef k ε`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16

section Co6
variable {d : ℕ}

lemma sa16t_bc_smooth {g : Euc d → ℝ} (hg : Continuous g) (n : ℕ) : ContDiff ℝ ∞ (sa16t_bc d n g) :=
  (sa16j_chi_contDiff d (sa16t_R n)).mul (sa16y_mollify_smooth n hg)

lemma sa16t_slice_cont {S : Set ℝ} {b : ℝ → Euc d → Euc d}
    (hb : ContinuousOn (fun q : ℝ × Euc d => b q.1 q.2) (S ×ˢ univ)) {σ : ℝ} (hσ : σ ∈ S) :
    Continuous (b σ) := by
  have hc : Continuous (fun y : Euc d => (σ, y)) := continuous_const.prodMk continuous_id
  have := hb.comp (f := fun y : Euc d => (σ, y)) (s := univ) hc.continuousOn (fun y _ => ⟨hσ, trivial⟩)
  exact continuousOn_univ.1 this

theorem sa16t_bcv_cont (k n : ℕ) {S : Set ℝ} (hS : IsCompact S) {b : ℝ → Euc d → Euc d}
    (hb : ContinuousOn (fun q : ℝ × Euc d => b q.1 q.2) (S ×ˢ univ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ σ ∈ S, ∀ σ' ∈ S, |σ - σ'| < δ →
      SA16BddCoef k ε (fun i x => sa16t_bcv d n (b σ) i x - sa16t_bcv d n (b σ') i x) := by
  obtain ⟨Cn, hCn0, hCn⟩ := sa16t_bc_small d k n
  set A : ℝ := ε / (Cn + 1) with hA
  have hA0 : 0 < A := by rw [hA]; positivity
  set Rr : ℝ := 2 * sa16t_R n + 1 with hRr
  have hK : IsCompact (S ×ˢ closedBall (0 : Euc d) Rr) := hS.prod (isCompact_closedBall _ _)
  have hKsub : S ×ˢ closedBall (0 : Euc d) Rr ⊆ S ×ˢ univ := prod_mono le_rfl (subset_univ _)
  have hcomp : ∀ i : Fin d, ContinuousOn (fun q : ℝ × Euc d => b q.1 q.2 i) (S ×ˢ closedBall (0 : Euc d) Rr) :=
    fun i => ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp_continuousOn (hb.mono hKsub))
  have hunif := fun i => hK.uniformContinuousOn_of_continuous (hcomp i)
  have hδ : ∀ i : Fin d, ∃ δ : ℝ, 0 < δ ∧ ∀ q ∈ S ×ˢ closedBall (0 : Euc d) Rr, ∀ q' ∈ S ×ˢ closedBall (0 : Euc d) Rr,
      dist q q' < δ → dist (b q.1 q.2 i) (b q'.1 q'.2 i) < A := fun i =>
    Metric.uniformContinuousOn_iff.1 (hunif i) A hA0
  choose δi hδi0 hδi using hδ
  have hslice : ∀ σ ∈ S, ∀ i : Fin d, Continuous (fun y => b σ y i) := fun σ hσ i =>
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp (sa16t_slice_cont hb hσ)
  have hbcsub : ∀ σ ∈ S, ∀ σ' ∈ S, ∀ i : Fin d,
      (fun x => sa16t_bcv d n (b σ) i x - sa16t_bcv d n (b σ') i x) =
        sa16t_bc d n (fun y => b σ y i - b σ' y i) := fun σ hσ σ' hσ' i =>
    (sa16t_bc_sub (hslice σ hσ i) (hslice σ' hσ' i) n).symm
  by_cases hd : d = 0
  · subst hd
    refine ⟨1, one_pos, fun σ hσ σ' hσ' _ => ⟨hε.le, fun i => i.elim0, fun i => i.elim0⟩⟩
  have hdpos : 0 < d := Nat.pos_of_ne_zero hd
  have : Nonempty (Fin d) := ⟨⟨0, hdpos⟩⟩
  refine ⟨Finset.univ.inf' Finset.univ_nonempty δi, (Finset.lt_inf'_iff _).2 fun i _ => hδi0 i,
    fun σ hσ σ' hσ' hlt => ⟨hε.le, fun i => ?_, fun i j hj x => ?_⟩⟩
  · rw [hbcsub σ hσ σ' hσ' i]
    exact sa16t_bc_smooth ((hslice σ hσ i).sub (hslice σ' hσ' i)) n
  · rw [hbcsub σ hσ σ' hσ' i]
    have hlt' : |σ - σ'| < δi i := lt_of_lt_of_le hlt (Finset.inf'_le _ (Finset.mem_univ i))
    have hG : ∀ y : Euc d, ‖y‖ ≤ Rr → |b σ y i - b σ' y i| ≤ A := by
      intro y hy
      have hq : (σ, y) ∈ S ×ˢ closedBall (0 : Euc d) Rr := ⟨hσ, by simpa using hy⟩
      have hq' : (σ', y) ∈ S ×ˢ closedBall (0 : Euc d) Rr := ⟨hσ', by simpa using hy⟩
      have hd' : dist (σ, y) (σ', y) < δi i := by
        rw [Prod.dist_eq, dist_self, Real.dist_eq]
        simpa using hlt'
      have := hδi i _ hq _ hq' hd'
      rw [Real.dist_eq] at this
      exact this.le
    have := hCn (fun y => b σ y i - b σ' y i) ((hslice σ hσ i).sub (hslice σ' hσ' i)) A hG j hj x
    refine this.trans ?_
    rw [hA, mul_div_assoc']
    rw [div_le_iff₀ (by positivity)]
    nlinarith

end Co6

end HRS.Whole.AppendixA.Phase2SA16R
