import HRS.MS.SA16SSt1

/-!
# S.A.16 (SA16S) En1: commuting derivatives (packet P7, step 2)

`sa16sy_pd_comm`: `∂^idx (∂_i f) = ∂_i (∂^idx f)` for smooth `f`; `sa16sy_pd_lap`: `∂^idx (Δ f) = Δ (∂^idx f)`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section En1
variable {d : ℕ}

/-- symmetry of second derivatives of a smooth function -/
lemma sa16sy_symm {g : Euc d → ℝ} (hg : ContDiff ℝ ∞ g) (v w x : Euc d) :
    fderiv ℝ (fun y => fderiv ℝ g y v) x w = fderiv ℝ (fun y => fderiv ℝ g y w) x v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ g) x :=
    ((hg.fderiv_right (m := 1) (by simp)).differentiable (by simp)) x
  have hsym : IsSymmSndFDerivAt ℝ g x :=
    (hg.contDiffAt (n := ∞)).isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  rw [fderiv_clm_apply hd (differentiableAt_const v), fderiv_clm_apply hd (differentiableAt_const w)]
  simp
  exact hsym.eq w v

lemma sa16sy_pd_comm {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (i : Fin d) :
    ∀ {j : ℕ} (idx : Fin j → Fin d),
      partialDeriv idx (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) =
        fun x => fderiv ℝ (partialDeriv idx f) x (EuclideanSpace.single i 1) := by
  intro j
  induction j with
  | zero =>
    intro idx
    funext x
    rw [sa16j_pd_zero]
    have : partialDeriv idx f = f := funext fun y => sa16j_pd_zero idx f y
    rw [this]
  | succ j ih =>
    intro idx
    obtain ⟨i', idx', rfl⟩ : ∃ (i' : Fin d) (idx' : Fin j → Fin d), idx = Fin.cons i' idx' :=
      ⟨idx 0, Fin.tail idx, (Fin.cons_self_tail idx).symm⟩
    funext x
    have hdi : ContDiff ℝ ∞ (fun y => fderiv ℝ f y (EuclideanSpace.single i 1)) := sa16so_dir_smooth hf _
    rw [sa16s_pd_cons hdi i' idx' x, ih idx']
    have hfun : partialDeriv (Fin.cons i' idx' : Fin (j + 1) → Fin d) f =
        fun y => fderiv ℝ (partialDeriv idx' f) y (EuclideanSpace.single i' 1) :=
      funext fun y => sa16s_pd_cons hf i' idx' y
    rw [hfun]
    exact sa16sy_symm (sa16j_pd_smooth hf idx') _ _ x

lemma sa16sy_pd_sum {ι : Type*} (s : Finset ι) {g : ι → Euc d → ℝ} (hg : ∀ i ∈ s, ContDiff ℝ ∞ (g i)) {j : ℕ}
    (idx : Fin j → Fin d) (x : Euc d) :
    partialDeriv idx (fun y => ∑ i ∈ s, g i y) x = ∑ i ∈ s, partialDeriv idx (g i) x := by
  unfold partialDeriv
  rw [iteratedFDeriv_fun_sum_apply (fun i hi => (hg i hi).contDiffAt.of_le (by exact_mod_cast le_top))]
  simp

lemma sa16sy_pd_lap {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ) {j : ℕ} (idx : Fin j → Fin d) (x : Euc d) :
    partialDeriv idx (sa16r_lap φ) x = sa16r_lap (partialDeriv idx φ) x := by
  have hdi : ∀ i : Fin d, ContDiff ℝ ∞ (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) :=
    fun i => sa16so_dir_smooth hφ _
  have hfun : sa16r_lap φ = fun y => ∑ i : Fin d, fderiv ℝ (fun y => fderiv ℝ φ y
      (EuclideanSpace.single i 1)) y (EuclideanSpace.single i 1) := rfl
  rw [hfun, sa16sy_pd_sum Finset.univ (fun i _ => sa16so_dir_smooth (hdi i) _)]
  unfold sa16r_lap
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sa16sy_pd_comm (hdi i) i idx, sa16sy_pd_comm hφ i idx]

end En1

end HRS.Whole.AppendixA.Phase2SA16R
