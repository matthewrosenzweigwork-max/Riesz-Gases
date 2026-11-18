import HRS.MS.UniqN1bA

/-!
# N1b of `UniqPlan.md`, part (b): polarization and the global Hessian bound

`D_j D_i ψ = ¼ (D²_{e_i+e_j} ψ - D²_{e_i-e_j} ψ)` (symmetry of the second derivative), so
`∂_j(g * ∂_iψ) = g * D_j D_i ψ` is a combination of two `g * D_q² ψ`; `n1b_hess_global` is the global
`L²` bound at `s = d - 2`, `n1b_hess_local` the local form of `n1a_hess_local` (with `C₀ = 0`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff ComplexConjugate

namespace HRS.MS.UniqN1b

open HRS HRS.Whole HRS.Whole.AppendixALemmas HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux
  HRS.MS.UniqT3 HRS.MS.UniqN3a

variable {d : ℕ}

theorem n1b_qq_bil {v : Euc d → ℝ} (hv : ContDiff ℝ 2 v) (a b y : Euc d) :
    fderiv ℝ (fun z => fderiv ℝ v z b) y a = fderiv ℝ (fderiv ℝ v) y a b := by
  have hd : DifferentiableAt ℝ (fderiv ℝ v) y :=
    ((hv.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)) y
  rw [fderiv_clm_apply hd (differentiableAt_const _)]
  simp

theorem n1b_polar {v : Euc d → ℝ} (hv : ContDiff ℝ 2 v) (i j : Fin d) (y : Euc d) :
    D1 j (D1 i v) y = (1 / 4 : ℝ) * (qq (EuclideanSpace.single i 1 + EuclideanSpace.single j 1) v y -
      qq (EuclideanSpace.single i 1 - EuclideanSpace.single j 1) v y) := by
  have hsym : IsSymmSndFDerivAt ℝ v y :=
    (hv.contDiffAt).isSymmSndFDerivAt (by simp [minSmoothness_of_isRCLikeNormedField])
  have e1 : D1 j (D1 i v) y = fderiv ℝ (fderiv ℝ v) y (EuclideanSpace.single j 1)
      (EuclideanSpace.single i 1) := n1b_qq_bil hv _ _ y
  have e2 : ∀ q : Euc d, qq q v y = fderiv ℝ (fderiv ℝ v) y q q := fun q => n1b_qq_bil hv q q y
  rw [e1, e2, e2]
  have := hsym (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  simp only [map_add, map_sub, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply]
  rw [this]
  ring

theorem n1b_D1_kcd (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) (i j : Fin d) :
    D1 j (kernelConvDeriv d s i ψ) = HRS.Whole.convFun (rieszKernel d s) (D1 j (D1 i ψ)) := by
  have hl := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  have hK : kernelConvDeriv d s i ψ = HRS.Whole.convFun (rieszKernel d s) (D1 i ψ) := rfl
  funext y
  rw [hK, convFun_D1 hl (D1_contDiff hψ i) (D1_supp hψc i) j y]

theorem n1b_convFun_integrable {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {F : Euc d → ℝ}
    (hF : Continuous F) (hFc : HasCompactSupport F) (x : Euc d) :
    Integrable (fun y => rieszKernel d s (x - y) * F y) volume := by
  have hl := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  have := (hFc.convolutionExists_left (ContinuousLinearMap.mul ℝ ℝ) hF hl x).integrable
  refine this.congr (Eventually.of_forall fun y => ?_)
  simp only [ContinuousLinearMap.mul_apply']; ring

theorem n1b_qq_eLp (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s = (d : ℝ) - 2) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (q : Euc d) (v : Euc d → ℝ), ContDiff ℝ 2 v → HasCompactSupport v →
      MemLp (HRS.Whole.convFun (rieszKernel d s) (qq q v)) 2 volume ∧
      eLpNorm (HRS.Whole.convFun (rieszKernel d s) (qq q v)) 2 volume ≤
        ENNReal.ofReal (K * ‖q‖ ^ 2) * eLpNorm v 2 volume := by
  obtain ⟨K, hK0, hK⟩ := n1b_qq_L2 hd hs0 hsd
  refine ⟨K, hK0, fun q v hv hvc => ?_⟩
  obtain ⟨hmem, hint⟩ := hK q v hv hvc
  refine ⟨hmem, ?_⟩
  have hvm : MemLp v 2 volume := hv.continuous.memLp_of_hasCompactSupport hvc
  rw [n1b_eLpNorm_eq hmem, n1b_eLpNorm_eq hvm, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc Real.sqrt (∫ x, (HRS.Whole.convFun (rieszKernel d s) (qq q v) x) ^ 2)
      ≤ Real.sqrt ((K * ‖q‖ ^ 2) ^ 2 * ∫ x, v x ^ 2) := Real.sqrt_le_sqrt hint
    _ = K * ‖q‖ ^ 2 * Real.sqrt (∫ x, v x ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]

theorem n1b_norm_single_add_sub (i j : Fin d) :
    ‖(EuclideanSpace.single i 1 + EuclideanSpace.single j 1 : Euc d)‖ ≤ 2 ∧
      ‖(EuclideanSpace.single i 1 - EuclideanSpace.single j 1 : Euc d)‖ ≤ 2 := by
  have h1 : ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ = 1 := by simp
  have h2 : ‖(EuclideanSpace.single j (1 : ℝ) : Euc d)‖ = 1 := by simp
  exact ⟨(norm_add_le _ _).trans (by rw [h1, h2]; norm_num),
    (norm_sub_le _ _).trans (by rw [h1, h2]; norm_num)⟩

/-- **Global Hessian bound at the endpoint `s = d - 2`.** -/
theorem n1b_hess_global (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s = (d : ℝ) - 2) :
    ∃ C : ℝ, ∀ (i j : Fin d) (ψ : Euc d → ℝ), ContDiff ℝ 2 ψ → HasCompactSupport ψ →
      MemLp (D1 j (kernelConvDeriv d s i ψ)) 2 volume ∧
      eLpNorm (D1 j (kernelConvDeriv d s i ψ)) 2 volume ≤ ENNReal.ofReal C * eLpNorm ψ 2 volume := by
  obtain ⟨K, hK0, hK⟩ := n1b_qq_eLp hd hs0 hsd
  have hsd' : s < d := by rw [hsd]; linarith
  refine ⟨2 * K, fun i j ψ hψ hψc => ?_⟩
  set qp : Euc d := EuclideanSpace.single i 1 + EuclideanSpace.single j 1 with hqp
  set qm : Euc d := EuclideanSpace.single i 1 - EuclideanSpace.single j 1 with hqm
  obtain ⟨hmp, hnp⟩ := hK qp ψ hψ hψc
  obtain ⟨hmm, hnm⟩ := hK qm ψ hψ hψc
  set a := HRS.Whole.convFun (rieszKernel d s) (qq qp ψ) with ha
  set b := HRS.Whole.convFun (rieszKernel d s) (qq qm ψ) with hb
  have hfun : D1 j (kernelConvDeriv d s i ψ) = (1 / 4 : ℝ) • (a - b) := by
    rw [n1b_D1_kcd hd hs0 hsd' hψ hψc i j]
    funext x
    have hip := n1b_convFun_integrable hs0 hsd' (qq_contDiff hψ (q := qp))
      (qq_hasCompactSupport hψc) x
    have him := n1b_convFun_integrable hs0 hsd' (qq_contDiff hψ (q := qm))
      (qq_hasCompactSupport hψc) x
    simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, ha, hb, HRS.Whole.convFun]
    rw [← integral_sub hip him, ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only [n1b_polar hψ i j y]
    ring
  have hsm : MemLp (a - b) 2 volume := hmp.sub hmm
  rw [hfun]
  refine ⟨hsm.const_smul _, ?_⟩
  obtain ⟨hpn, hmn⟩ := n1b_norm_single_add_sub (d := d) i j
  have hp4 : ‖qp‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg qp]
  have hm4 : ‖qm‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg qm]
  have hcp : ENNReal.ofReal (K * ‖qp‖ ^ 2) ≤ ENNReal.ofReal (4 * K) :=
    ENNReal.ofReal_le_ofReal (by nlinarith)
  have hcm : ENNReal.ofReal (K * ‖qm‖ ^ 2) ≤ ENNReal.ofReal (4 * K) :=
    ENNReal.ofReal_le_ofReal (by nlinarith)
  calc eLpNorm ((1 / 4 : ℝ) • (a - b)) 2 volume
      = ‖(1 / 4 : ℝ)‖ₑ * eLpNorm (a - b) 2 volume := eLpNorm_const_smul _ _ _ _
    _ ≤ ‖(1 / 4 : ℝ)‖ₑ * (eLpNorm a 2 volume + eLpNorm b 2 volume) :=
        mul_le_mul_right (eLpNorm_sub_le (by norm_num)) _
    _ ≤ ‖(1 / 4 : ℝ)‖ₑ * (ENNReal.ofReal (4 * K) * eLpNorm ψ 2 volume +
          ENNReal.ofReal (4 * K) * eLpNorm ψ 2 volume) := by
        gcongr
        · exact hnp.trans (mul_le_mul_left hcp _)
        · exact hnm.trans (mul_le_mul_left hcm _)
    _ = ENNReal.ofReal (2 * K) * eLpNorm ψ 2 volume := by
        have e1 : ‖(1 / 4 : ℝ)‖ₑ = ENNReal.ofReal (1 / 4) := by
          rw [← ofReal_norm, Real.norm_eq_abs, abs_of_pos (by norm_num)]
        have e2 : ENNReal.ofReal (1 / 4) * (ENNReal.ofReal (4 * K) + ENNReal.ofReal (4 * K)) =
            ENNReal.ofReal (2 * K) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_mul (by norm_num)]
          congr 1; ring
        rw [e1, ← add_mul, ← mul_assoc, e2]

/-- **N1b.** The local Hessian bound at the endpoint `s = d - 2` (statement of `n1a_hess_local`,
with `C₀ = 0`). -/
theorem n1b_hess_local (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s = (d : ℝ) - 2) :
    ∃ C₀ C : ℝ, ∀ (i j : Fin d) (ρ : ℝ), 1 ≤ ρ → ∀ (c : Euc d) (ψ : Euc d → ℝ),
      ContDiff ℝ 2 ψ → HasCompactSupport ψ → Function.support ψ ⊆ closedBall c ρ →
      ∀ (c' : Euc d) (r' : ℝ), r' ≤ ρ →
        eLpNorm ((closedBall c' r').indicator (fun y => D1 j (kernelConvDeriv d s i ψ) y)) 2 volume ≤
          ENNReal.ofReal (C * ρ ^ C₀) * eLpNorm ψ 2 volume := by
  obtain ⟨C, hC⟩ := n1b_hess_global hd hs0 hsd
  refine ⟨0, C, fun i j ρ hρ c ψ hψ hψc _ c' r' _ => ?_⟩
  rw [Real.rpow_zero, mul_one]
  exact (eLpNorm_indicator_le _ measurableSet_closedBall).trans (hC i j ψ hψ hψc).2

end HRS.MS.UniqN1b
