import HRS.MS.SA16Y4Io3

/-!
# S.A.16 (SA16Y4) Io4: derivatives of `eucNonlocal` in the order-1 range

`sa16y4io_pd_F`: for `a ∈ SB`, `u ∈ 𝓢`, `0 ≤ s < d-1`:
`∂^idx (eucNonlocal s M a u) = ∑_{ij} M_{ji} ∂_i (g * ∂^idx (a ∂_j u))` (derivatives stay on `a ∂_j u`, no second derivative of `u`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16

section Io4
variable {d : ℕ} (hd : 1 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < (d : ℝ) - 1)
include hd hs hs1

theorem sa16y4io_conv_pd (j : ℕ) (idx : Fin j → Fin d) (ψ : 𝓢(Euc d, ℝ)) :
    partialDeriv idx (HRS.Whole.convFun (rieszKernel d s) ψ) =
      HRS.Whole.convFun (rieszKernel d s) (partialDeriv idx ⇑ψ) := by
  rw [sa16q_conv_eq d s ψ, sa16q_conv_eq d s (partialDeriv idx ⇑ψ)]
  exact sa16q_gen_pd (sa16q_g_meas d s) (sa16y4io_g_WI hd hs hs1) j idx ψ

theorem sa16y4io_pd_F (M : Matrix (Fin d) (Fin d) ℝ) {a : Euc d → ℝ} (ha : sa16q_SB a)
    (u : 𝓢(Euc d, ℝ)) {l : ℕ} (idx : Fin l → Fin d) (x : Euc d) :
    partialDeriv idx (HRS.MH.AdjointRd.eucNonlocal s M a ⇑u) x =
      ∑ i : Fin d, ∑ j : Fin d, M j i *
        fderiv ℝ (HRS.Whole.convFun (rieszKernel d s)
          (sa16q_pdS idx (sa16q_mulS ha (sa16q_dS (EuclideanSpace.single j (1 : ℝ)) u)))) x
          (EuclideanSpace.single i (1 : ℝ)) := by
  set Ψ : Fin d → 𝓢(Euc d, ℝ) := fun j => sa16q_mulS ha (sa16q_dS (EuclideanSpace.single j (1 : ℝ)) u) with hΨ
  have hGs : ∀ ψ : 𝓢(Euc d, ℝ), ContDiff ℝ ∞ (HRS.Whole.convFun (rieszKernel d s) ψ) :=
    fun ψ => sa16y4io_conv_contDiff_top hd hs hs1 ψ
  have hBs : ∀ (ψ : 𝓢(Euc d, ℝ)) (i : Fin d), ContDiff ℝ ∞
      (fun y => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) ψ) y (EuclideanSpace.single i (1 : ℝ))) :=
    fun ψ i => ((hGs ψ).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hfun : HRS.MH.AdjointRd.eucNonlocal s M a ⇑u = fun y => ∑ i : Fin d, ∑ j : Fin d, M j i *
      fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) (Ψ j)) y (EuclideanSpace.single i (1 : ℝ)) := by
    have e : ∀ j : Fin d, (fun x' => ∫ y, rieszKernel d s (x' - y) *
        (a y * fderiv ℝ ⇑u y (EuclideanSpace.single j (1 : ℝ)))) =
        HRS.Whole.convFun (rieszKernel d s) (Ψ j) := by
      intro j
      funext x'
      simp only [HRS.Whole.convFun, hΨ, sa16q_mulS_apply, sa16q_dS_apply]
    funext y
    unfold HRS.MH.AdjointRd.eucNonlocal
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [e j]
  have h2 : ∀ i j, ContDiff ℝ ∞ (fun y => M j i * fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) (Ψ j)) y
      (EuclideanSpace.single i (1 : ℝ))) := fun i j => contDiff_const.mul (hBs (Ψ j) i)
  have h3 : ∀ i, ContDiff ℝ ∞ (fun y => ∑ j, M j i * fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) (Ψ j)) y
      (EuclideanSpace.single i (1 : ℝ))) := fun i => ContDiff.sum fun j _ => h2 i j
  rw [hfun, sa16q_pd_sum Finset.univ (fun i y => ∑ j, M j i * fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) (Ψ j)) y
      (EuclideanSpace.single i (1 : ℝ))) h3 idx x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [sa16q_pd_sum Finset.univ (fun j y => M j i * fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) (Ψ j)) y
      (EuclideanSpace.single i (1 : ℝ))) (h2 i) idx x]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sa16q_pd_smul (hBs (Ψ j) i) (M j i) idx x]
  congr 1
  rw [sa16q_pd_comm (hGs (Ψ j)) i l idx x, sa16y4io_conv_pd hd hs hs1 l idx (Ψ j), ← sa16q_pdS_fun]
end Io4

end HRS.Whole.AppendixA.Phase2SA16Q
