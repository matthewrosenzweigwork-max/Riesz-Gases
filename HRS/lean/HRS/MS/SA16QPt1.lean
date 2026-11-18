import HRS.MS.SA16QSm5

/-!
# S.A.16 (SA16Q), E6 part 12: the pointwise formula for `eucNonlocal` with a `C¹_b` coefficient

For `a` of class `C¹` with `a` and `∇a` bounded, `d ≥ 2`, `0 ≤ s ≤ d-2`, `u ∈ 𝓢`:

`eucNonlocal s M a u x = ∑_{ij} M_{ji} ∫ K1_i(y) a(x-y) ∂_j u(x-y) dy`,  `K1_i = ∂_i g`.

This is the form used for the pointwise convergence of the mollified operators.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16

section Pt
variable {d : ℕ}

/-- a `C¹_b` function times a Schwartz function satisfies the hypotheses of the integration by parts -/
lemma sa16q_prod_hyp {a : Euc d → ℝ} (ha1 : ContDiff ℝ 1 a) {B0 B1 : ℝ} (hB0 : ∀ x, |a x| ≤ B0)
    (hB1 : ∀ x, ‖fderiv ℝ a x‖ ≤ B1) (h : 𝓢(Euc d, ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ Differentiable ℝ (fun y => a y * h y) ∧
      Continuous (fderiv ℝ (fun y => a y * h y)) ∧ sa16q_Dec C (fun y => a y * h y) ∧
      sa16q_Dec C (fderiv ℝ (fun y => a y * h y)) := by
  obtain ⟨C1, hC1, hd1, hc1, hD1, hD1'⟩ := sa16q_schwartz_hyp h
  have hB00 : 0 ≤ B0 := (abs_nonneg _).trans (hB0 0)
  have hB10 : 0 ≤ B1 := (norm_nonneg _).trans (hB1 0)
  have had : Differentiable ℝ a := ha1.differentiable (by simp)
  have hfd : ∀ y, fderiv ℝ (fun y => a y * h y) y = a y • fderiv ℝ h y + h y • fderiv ℝ a y := by
    intro y
    exact ((had y).hasFDerivAt.mul (h.differentiableAt.hasFDerivAt)).fderiv
  refine ⟨B0 * C1 + B1 * C1 + B0 * C1, by positivity, fun y => (had y).mul h.differentiableAt, ?_, ?_, ?_⟩
  · have : fderiv ℝ (fun y => a y * h y) = fun y => a y • fderiv ℝ h y + h y • fderiv ℝ a y :=
      funext hfd
    rw [this]
    have hca : Continuous (fderiv ℝ a) := ha1.continuous_fderiv (by simp)
    exact (ha1.continuous.smul hc1).add (h.continuous.smul hca)
  · intro z
    show ‖a z * h z‖ ≤ _
    rw [norm_mul]
    have h1 := hD1 z
    have hw : 0 ≤ (1 + ‖z‖) ^ (-((d + 2 : ℕ) : ℝ)) := Real.rpow_nonneg (by positivity) _
    have h3 : ‖a z‖ ≤ B0 := by simpa [Real.norm_eq_abs] using hB0 z
    calc ‖a z‖ * ‖h z‖ ≤ B0 * (C1 * (1 + ‖z‖) ^ (-((d + 2 : ℕ) : ℝ))) :=
          mul_le_mul h3 h1 (norm_nonneg _) hB00
      _ ≤ (B0 * C1 + B1 * C1 + B0 * C1) * (1 + ‖z‖) ^ (-((d + 2 : ℕ) : ℝ)) := by
          nlinarith [mul_nonneg hB00 (mul_nonneg hC1 hw), mul_nonneg hB10 (mul_nonneg hC1 hw)]
  · intro z
    rw [hfd z]
    refine (norm_add_le _ _).trans ?_
    rw [norm_smul, norm_smul]
    have h1 := hD1 z
    have h2 := hD1' z
    have hw : 0 ≤ (1 + ‖z‖) ^ (-((d + 2 : ℕ) : ℝ)) := Real.rpow_nonneg (by positivity) _
    have h3 : ‖a z‖ ≤ B0 := by simpa [Real.norm_eq_abs] using hB0 z
    calc ‖a z‖ * ‖fderiv ℝ h z‖ + ‖h z‖ * ‖fderiv ℝ a z‖
        ≤ B0 * (C1 * (1 + ‖z‖) ^ (-((d + 2 : ℕ) : ℝ))) +
            (C1 * (1 + ‖z‖) ^ (-((d + 2 : ℕ) : ℝ))) * B1 :=
          add_le_add (mul_le_mul h3 h2 (norm_nonneg _) hB00)
            (mul_le_mul h1 (hB1 z) (norm_nonneg _) (mul_nonneg hC1 hw))
      _ ≤ _ := by
          nlinarith [mul_nonneg hB00 (mul_nonneg hC1 hw), mul_nonneg hB10 (mul_nonneg hC1 hw)]

variable (hd : 2 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs2 : s ≤ (d : ℝ) - 2)
include hd hs hs2

theorem sa16q_F_pointwise (M : Matrix (Fin d) (Fin d) ℝ) {a : Euc d → ℝ} (ha1 : ContDiff ℝ 1 a)
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
  rw [hfun, sa16q_fderiv_conv_apply (sa16q_g_meas d s) (sa16q_g_WI hd hs hs2) hC hdiff hcont hD hD' x
    (EuclideanSpace.single i (1 : ℝ))]
  refine (sa16q_ibp_g hd hs hs2 i x hC hdiff hcont hD hD').trans ?_
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only [sa16q_dS_apply]

end Pt

end HRS.Whole.AppendixA.Phase2SA16Q
