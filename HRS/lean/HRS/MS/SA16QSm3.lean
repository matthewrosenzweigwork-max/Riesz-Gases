import HRS.MS.SA16QSm2

/-!
# S.A.16 (SA16Q), E6 part 9: coordinate derivatives of `eucNonlocal` for smooth bounded coefficients

`sa16q_pd_F`: for `a ∈ SB`, `u ∈ 𝓢`, the coordinate derivative `∂^idx` of `eucNonlocal s M a u` is the same
expression with `P = a u`, `Q_j = (∂_j a) u` replaced by `∂^idx P`, `∂^idx Q_j` (Schwartz).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16

section PdLin
variable {d : ℕ}

lemma sa16q_pd_sum {ι : Type*} (u : Finset ι) (f : ι → Euc d → ℝ) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    {l : ℕ} (idx : Fin l → Fin d) (x : Euc d) :
    partialDeriv idx (fun y => ∑ i ∈ u, f i y) x = ∑ i ∈ u, partialDeriv idx (f i) x := by
  unfold partialDeriv
  rw [iteratedFDeriv_fun_sum_apply (fun i _ => ((hf i).of_le (by exact_mod_cast le_top)).contDiffAt)]
  simp [ContinuousMultilinearMap.sum_apply]

lemma sa16q_pd_smul {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (c : ℝ) {l : ℕ} (idx : Fin l → Fin d)
    (x : Euc d) : partialDeriv idx (fun y => c * f y) x = c * partialDeriv idx f x := by
  have : (fun y => c * f y) = c • f := by funext y; simp
  rw [this]
  exact sa16s_partialDeriv_smul hf c idx x

lemma sa16q_pd_sub {f g : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {l : ℕ}
    (idx : Fin l → Fin d) (x : Euc d) :
    partialDeriv idx (fun y => f y - g y) x = partialDeriv idx f x - partialDeriv idx g x := by
  unfold partialDeriv
  have hf' : ContDiffAt ℝ l f x := (hf.of_le (by exact_mod_cast le_top)).contDiffAt
  have hg' : ContDiffAt ℝ l g x := (hg.of_le (by exact_mod_cast le_top)).contDiffAt
  have := iteratedFDeriv_sub_apply hf' hg'
  show (iteratedFDeriv ℝ l (f - g) x) _ = _
  rw [this]
  rfl

lemma sa16q_pd_dsum (c : Fin d → Fin d → ℝ) (A B : Fin d → Fin d → Euc d → ℝ)
    (hA : ∀ i j, ContDiff ℝ ∞ (A i j)) (hB : ∀ i j, ContDiff ℝ ∞ (B i j)) {l : ℕ} (idx : Fin l → Fin d)
    (x : Euc d) :
    partialDeriv idx (fun y => ∑ i, ∑ j, c i j * (A i j y - B i j y)) x =
      ∑ i, ∑ j, c i j * (partialDeriv idx (A i j) x - partialDeriv idx (B i j) x) := by
  have h1 : ∀ i j, ContDiff ℝ ∞ (fun y => A i j y - B i j y) := fun i j => (hA i j).sub (hB i j)
  have h2 : ∀ i j, ContDiff ℝ ∞ (fun y => c i j * (A i j y - B i j y)) :=
    fun i j => contDiff_const.mul (h1 i j)
  have h3 : ∀ i, ContDiff ℝ ∞ (fun y => ∑ j, c i j * (A i j y - B i j y)) :=
    fun i => ContDiff.sum fun j _ => h2 i j
  rw [sa16q_pd_sum Finset.univ (fun i y => ∑ j, c i j * (A i j y - B i j y)) h3 idx x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sa16q_pd_sum Finset.univ (fun j y => c i j * (A i j y - B i j y)) (h2 i) idx x]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sa16q_pd_smul (h1 i j) (c i j) idx x, sa16q_pd_sub (hA i j) (hB i j) idx x]

open LineDeriv in
/-- the Schwartz function `∂^idx u` -/
def sa16q_pdS {l : ℕ} (idx : Fin l → Fin d) (u : 𝓢(Euc d, ℝ)) : 𝓢(Euc d, ℝ) :=
  ∂^{fun k => (EuclideanSpace.single (idx k) (1 : ℝ) : Euc d)} u

lemma sa16q_pdS_apply {l : ℕ} (idx : Fin l → Fin d) (u : 𝓢(Euc d, ℝ)) (x : Euc d) :
    sa16q_pdS idx u x = partialDeriv idx (⇑u) x := by
  unfold sa16q_pdS
  rw [sa16j_pd_schwartz u idx]

lemma sa16q_pdS_fun {l : ℕ} (idx : Fin l → Fin d) (u : 𝓢(Euc d, ℝ)) :
    ⇑(sa16q_pdS idx u) = partialDeriv idx (⇑u) := funext (sa16q_pdS_apply idx u)

end PdLin

section PdF
variable {d : ℕ} (hd : 2 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs2 : s ≤ (d : ℝ) - 2)
include hd hs hs2

theorem sa16q_pd_F_gen (M : Matrix (Fin d) (Fin d) ℝ) (P : 𝓢(Euc d, ℝ)) (Q : Fin d → 𝓢(Euc d, ℝ))
    {l : ℕ} (idx : Fin l → Fin d) (x : Euc d) :
    partialDeriv idx (fun y => ∑ i : Fin d, ∑ j : Fin d, M j i *
      (fderiv ℝ (fun z => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) P) z
          (EuclideanSpace.single j (1 : ℝ))) y (EuclideanSpace.single i (1 : ℝ)) -
        fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) (Q j)) y (EuclideanSpace.single i (1 : ℝ)))) x =
      ∑ i : Fin d, ∑ j : Fin d, M j i *
        (fderiv ℝ (fun y => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) (sa16q_pdS idx P)) y
            (EuclideanSpace.single j (1 : ℝ))) x (EuclideanSpace.single i (1 : ℝ)) -
          fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) (sa16q_pdS idx (Q j))) x
            (EuclideanSpace.single i (1 : ℝ))) := by
  have hGs : ∀ ψ : 𝓢(Euc d, ℝ), ContDiff ℝ ∞ (HRS.Whole.convFun (rieszKernel d s) ψ) :=
    fun ψ => sa16q_conv_contDiff_top hd hs hs2 ψ
  have hVs : ∀ (ψ : 𝓢(Euc d, ℝ)) (j : Fin d), ContDiff ℝ ∞
      (fun z => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) ψ) z (EuclideanSpace.single j (1 : ℝ))) :=
    fun ψ j => ((hGs ψ).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hAs : ∀ (ψ : 𝓢(Euc d, ℝ)) (i j : Fin d), ContDiff ℝ ∞
      (fun y => fderiv ℝ (fun z => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) ψ) z
        (EuclideanSpace.single j (1 : ℝ))) y (EuclideanSpace.single i (1 : ℝ))) := fun ψ i j =>
    (((hVs ψ j).fderiv_right (m := ∞) (by simp))).clm_apply contDiff_const
  have hBs : ∀ (ψ : 𝓢(Euc d, ℝ)) (i : Fin d), ContDiff ℝ ∞
      (fun y => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) ψ) y (EuclideanSpace.single i (1 : ℝ))) :=
    fun ψ i => ((hGs ψ).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  rw [sa16q_pd_dsum (fun i j => M j i)
    (fun i j y => fderiv ℝ (fun z => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) P) z
        (EuclideanSpace.single j (1 : ℝ))) y (EuclideanSpace.single i (1 : ℝ)))
    (fun i j y => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) (Q j)) y
        (EuclideanSpace.single i (1 : ℝ)))
    (fun i j => hAs P i j) (fun i j => hBs (Q j) i) idx x]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have hA : partialDeriv idx (fun y => fderiv ℝ (fun z => fderiv ℝ
        (HRS.Whole.convFun (rieszKernel d s) P) z (EuclideanSpace.single j (1 : ℝ))) y
        (EuclideanSpace.single i (1 : ℝ))) x =
      fderiv ℝ (fun y => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) (sa16q_pdS idx P)) y
        (EuclideanSpace.single j (1 : ℝ))) x (EuclideanSpace.single i (1 : ℝ)) := by
    rw [sa16q_pd_comm (hVs P j) i l idx x]
    have e1 : partialDeriv idx (fun z => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) P) z
        (EuclideanSpace.single j (1 : ℝ))) =
        fun y => fderiv ℝ (partialDeriv idx (HRS.Whole.convFun (rieszKernel d s) P)) y
          (EuclideanSpace.single j (1 : ℝ)) :=
      funext fun y => sa16q_pd_comm (hGs P) j l idx y
    rw [e1, sa16q_conv_pd hd hs hs2 l idx P, ← sa16q_pdS_fun]
  have hB : partialDeriv idx (fun y => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) (Q j)) y
        (EuclideanSpace.single i (1 : ℝ))) x =
      fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) (sa16q_pdS idx (Q j))) x
        (EuclideanSpace.single i (1 : ℝ)) := by
    rw [sa16q_pd_comm (hGs (Q j)) i l idx x, sa16q_conv_pd hd hs hs2 l idx (Q j), ← sa16q_pdS_fun]
  rw [hA, hB]

theorem sa16q_pd_F (M : Matrix (Fin d) (Fin d) ℝ) {a : Euc d → ℝ} (ha : sa16q_SB a)
    (u : 𝓢(Euc d, ℝ)) {l : ℕ} (idx : Fin l → Fin d) (x : Euc d) :
    partialDeriv idx (HRS.MH.AdjointRd.eucNonlocal s M a ⇑u) x =
      ∑ i : Fin d, ∑ j : Fin d, M j i *
        (fderiv ℝ (fun y => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s)
            (sa16q_pdS idx (sa16q_mulS ha u))) y (EuclideanSpace.single j (1 : ℝ))) x
            (EuclideanSpace.single i (1 : ℝ)) -
          fderiv ℝ (HRS.Whole.convFun (rieszKernel d s)
            (sa16q_pdS idx (sa16q_mulS (sa16q_SB_pd ha (EuclideanSpace.single j (1 : ℝ))) u))) x
            (EuclideanSpace.single i (1 : ℝ))) := by
  have hfun : HRS.MH.AdjointRd.eucNonlocal s M a ⇑u = fun y => ∑ i : Fin d, ∑ j : Fin d, M j i *
      (fderiv ℝ (fun z => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) (sa16q_mulS ha u)) z
          (EuclideanSpace.single j (1 : ℝ))) y (EuclideanSpace.single i (1 : ℝ)) -
        fderiv ℝ (HRS.Whole.convFun (rieszKernel d s)
          (sa16q_mulS (sa16q_SB_pd ha (EuclideanSpace.single j (1 : ℝ))) u)) y
          (EuclideanSpace.single i (1 : ℝ))) :=
    funext fun y => sa16q_F_decomp hd hs hs2 M ha u y
  rw [hfun]
  exact sa16q_pd_F_gen hd hs hs2 M (sa16q_mulS ha u)
    (fun j => sa16q_mulS (sa16q_SB_pd ha (EuclideanSpace.single j (1 : ℝ))) u) idx x

end PdF

end HRS.Whole.AppendixA.Phase2SA16Q
