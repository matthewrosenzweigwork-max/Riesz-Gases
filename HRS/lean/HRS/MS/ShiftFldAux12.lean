import HRS.MS.ShiftFldAux11

/-!
# S79P: the second integration by parts: `∑_i ∫ ∂_i u ρ (∂_i g*ψ) = ∫ (g*ψ) ρ 𝒜u`
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S79G

open HRS.Whole HRS.MS.S21 HRS.MH.DualityRd HRS.MS.UniqT3 HRS.MS.UniqNDefs HRS.Whole.AppendixALemmas
open HRS (Euc)

variable {d : ℕ}

theorem s79g_D1D1_eq {u : Euc d → ℝ} (hu : ContDiff ℝ 2 u) (i j : Fin d) (y : Euc d) :
    D1 j (D1 i u) y = fderiv ℝ (fderiv ℝ u) y (EuclideanSpace.single j (1 : ℝ))
      (EuclideanSpace.single i (1 : ℝ)) := by
  have hc : DifferentiableAt ℝ (fderiv ℝ u) y :=
    ((hu.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero) y
  show fderiv ℝ (fun z => fderiv ℝ u z (EuclideanSpace.single i (1 : ℝ))) y _ = _
  rw [fderiv_clm_apply hc (differentiableAt_const _)]
  simp

theorem s79g_D1D1_bound {u : Euc d → ℝ} (hu : HRS.MemCb 2 u) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i j y, |D1 j (D1 i u) y| ≤ B := by
  obtain ⟨B, hB0, hB⟩ := HRS.MH.DualityRd.db1_iteratedFDeriv_bdd hu (j := 2) (by norm_num)
  refine ⟨B, hB0, fun i j y => ?_⟩
  rw [s79g_D1D1_eq hu.1 i j y, ← Real.norm_eq_abs]
  have h1 : ‖fderiv ℝ (fderiv ℝ u) y (EuclideanSpace.single j (1 : ℝ))
      (EuclideanSpace.single i (1 : ℝ))‖ ≤ ‖fderiv ℝ (fderiv ℝ u) y‖ := by
    refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    calc ‖fderiv ℝ (fderiv ℝ u) y (EuclideanSpace.single j (1 : ℝ))‖ *
          ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖
        ≤ (‖fderiv ℝ (fderiv ℝ u) y‖ * ‖(EuclideanSpace.single j (1 : ℝ) : Euc d)‖) * 1 := by
          gcongr
          · exact ContinuousLinearMap.le_opNorm _ _
          · simp
      _ ≤ ‖fderiv ℝ (fderiv ℝ u) y‖ := by simp
  refine h1.trans ?_
  have h2 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := u) (x := y) (n := 1)
  have h3 := norm_iteratedFDeriv_one (𝕜 := ℝ) (x := y) (fderiv ℝ u)
  rw [← h3, h2]
  exact hB y

theorem s79g_lap_sum {u : Euc d → ℝ} (hu : ContDiff ℝ 2 u) (x : Euc d) :
    Laplacian.laplacian u x = ∑ i : Fin d, D1 i (D1 i u) x :=
  HRS.MD.DOMProof.domp_lap_eq_sum_ddk hu.contDiffAt

theorem s79g_div_rho (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) (hρ : IsThermalEquilibrium d s a β (thermalDensity d s a β))
    {u : Euc d → ℝ} (hu : ContDiff ℝ 2 u) (y : Euc d) :
    ∑ i : Fin d, fderiv ℝ (fun z => thermalDensity d s a β z * D1 i u z) y
        (EuclideanSpace.single i (1 : ℝ)) =
      -(thermalDensity d s a β y * Aop d s a β (thermalDensity d s a β) u y) := by
  obtain ⟨C, c, BU, hT⟩ := S45.s45_thermal_data hd hs0 hsd ha hβ
  have hρd : Differentiable ℝ (thermalDensity d s a β) := hT.smooth.differentiable (by simp)
  have hD1d : ∀ i, Differentiable ℝ (D1 i u) := fun i =>
    (D1_contDiff hu i).differentiable one_ne_zero
  have hterm : ∀ i : Fin d, fderiv ℝ (fun z => thermalDensity d s a β z * D1 i u z) y
      (EuclideanSpace.single i (1 : ℝ)) =
      (β * thermalDensity d s a β y * (bdr d s a β (thermalDensity d s a β) y) i) * D1 i u y +
        thermalDensity d s a β y * D1 i (D1 i u) y := by
    intro i
    have hh : HasFDerivAt (fun z => thermalDensity d s a β z * D1 i u z)
        (thermalDensity d s a β y • fderiv ℝ (D1 i u) y + D1 i u y • fderiv ℝ (thermalDensity d s a β) y) y :=
      (hρd y).hasFDerivAt.mul (hD1d i y).hasFDerivAt
    rw [hh.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have h1 : fderiv ℝ (thermalDensity d s a β) y (EuclideanSpace.single i (1 : ℝ)) =
        (β * thermalDensity d s a β y) * (bdr d s a β (thermalDensity d s a β) y) i := by
      have := s79g_grad_rho hd hs0 hsd ha hβ hρ y
      have h2 := HRS.MD.DOMProof.domp_gradient_apply (thermalDensity d s a β) y i
      rw [this] at h2
      simpa [HRS.MD.DOMProof.dk] using h2.symm
    rw [h1]
    show _ = _ + _ * fderiv ℝ (D1 i u) y (EuclideanSpace.single i (1 : ℝ))
    ring
  simp only [hterm, Finset.sum_add_distrib]
  unfold Aop
  rw [s79g_lap_sum hu]
  have hin : inner ℝ (bdr d s a β (thermalDensity d s a β) y) (gradient u y) =
      ∑ i : Fin d, (bdr d s a β (thermalDensity d s a β) y) i * D1 i u y := by
    simp only [PiLp.inner_apply, HRS.MD.DOMProof.domp_gradient_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [HRS.MD.DOMProof.dk, D1, mul_comm]
  rw [hin]
  have e1 : ∑ i : Fin d, (β * thermalDensity d s a β y * (bdr d s a β (thermalDensity d s a β) y) i) *
      D1 i u y = thermalDensity d s a β y * (β * ∑ i : Fin d,
        (bdr d s a β (thermalDensity d s a β) y) i * D1 i u y) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have e2 : ∑ i : Fin d, thermalDensity d s a β y * D1 i (D1 i u) y =
      thermalDensity d s a β y * ∑ i : Fin d, D1 i (D1 i u) y := (Finset.mul_sum _ _ _).symm
  rw [e1, e2]
  ring

end HRS.MS.S79G
