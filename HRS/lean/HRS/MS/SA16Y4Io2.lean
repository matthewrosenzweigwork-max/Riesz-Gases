import HRS.MS.SA16Y4Io1

/-!
# S.A.16 (SA16Y4) Io2: pointwise formula for `eucNonlocal` in the order-1 range

For `a ∈ C¹_b`, `1 ≤ d`, `0 ≤ s < d - 1`, `u ∈ 𝓢`:
`eucNonlocal s M a u x = ∑_{ij} M_{ji} ∫ K1_i(y) a(x-y) ∂_j u(x-y) dy` (`K1_i = ∂_i g`, locally integrable since `s+1 < d`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16

section Io2
variable {d : ℕ}

theorem sa16y4io_F_pointwise (hd : 1 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < (d : ℝ) - 1)
    (M : Matrix (Fin d) (Fin d) ℝ) {a : Euc d → ℝ} (ha1 : ContDiff ℝ 1 a)
    {B0 B1 : ℝ} (hB0 : ∀ x, |a x| ≤ B0) (hB1 : ∀ x, ‖fderiv ℝ a x‖ ≤ B1) (u : 𝓢(Euc d, ℝ)) (x : Euc d) :
    HRS.MH.AdjointRd.eucNonlocal s M a ⇑u x = ∑ i : Fin d, ∑ j : Fin d, M j i *
      ∫ y, sa16q_K1E s 0 i y * (a (x - y) * fderiv ℝ u (x - y) (EuclideanSpace.single j (1 : ℝ))) := by
  unfold HRS.MH.AdjointRd.eucNonlocal
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  obtain ⟨C, hC, hdiff, hcont, hD, hD'⟩ :=
    sa16q_prod_hyp ha1 hB0 hB1 (sa16q_dS (EuclideanSpace.single j (1 : ℝ)) u)
  have hfun : (fun x' => ∫ y, rieszKernel d s (x' - y) *
        (a y * fderiv ℝ ⇑u y (EuclideanSpace.single j (1 : ℝ)))) =
      fun x' => ∫ y, rieszKernel d s y * (fun y => a y * (sa16q_dS (EuclideanSpace.single j (1 : ℝ)) u) y)
        (x' - y) := by
    funext x'
    have := HRS.S16Cze.s16cze_conv_swap (rieszKernel d s)
      (fun y => a y * fderiv ℝ ⇑u y (EuclideanSpace.single j (1 : ℝ))) x'
    simp only [HRS.Whole.convFun] at this
    rw [this]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [sa16q_dS_apply]
  rw [hfun, sa16q_fderiv_conv_apply (sa16q_g_meas d s) (sa16y4io_g_WI hd hs hs1) hC hdiff hcont hD hD' x
    (EuclideanSpace.single i (1 : ℝ))]
  refine (sa16y4io_ibp_g hd hs hs1 i x hC hdiff hcont hD hD').trans ?_
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [sa16q_dS_apply]
end Io2

end HRS.Whole.AppendixA.Phase2SA16Q
