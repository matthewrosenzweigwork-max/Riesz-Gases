import HRS.MS.UniqE4b

/-!
# E4 of `UniqPlan.md`, part 3: the kernel `H = g * ∂_iψ'` and the exact commutator identity

* `e4_kcd_moll`     : `g * ∂_i(η_ε * ψ') = η_ε * (g * ∂_iψ')`  (Fubini, `K_cv`).
* `e4_kcd_contDiff`, `e4_kcd_bdd'`, `e4_D1_kcd` : `C¹`, boundedness and derivative of `H`.
* `e4_identity`     : for the weak gradient `v` of `u`, `ρ'` decaying `C¹`, `ψ' ∈ C²_c`, `φ = η_ε * ψ'`:
  `∫ u ∂_j(ρ' H_φ) - ∫ (η_ε * u) ∂_j(ρ' H') = - ∫ [η_ε, ρ'] v_j · H'`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.UniqE4

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqM1 HRS.MS.UniqM2
  HRS.MS.UniqM3 HRS.MS.UniqT3 HRS.MS.UniqC3 HRS.MS.UniqE3 HRS.MS.UniqN0

variable {d : ℕ}

theorem e4_cv_comm (f h : Euc d → ℝ) (y : Euc d) :
    HRS.MS.UniqT3.cv f h y = HRS.MS.UniqT3.cv h f y := by
  unfold HRS.MS.UniqT3.cv
  rw [← integral_sub_left_eq_self (fun x => f x * h (y - x)) volume y]
  congr 1; funext x
  simp only [sub_sub_cancel]; ring

theorem e4_moll_cv3 (ε : ℝ) (f : Euc d → ℝ) (y : Euc d) :
    moll d ε f y = HRS.MS.UniqT3.cv f (eta d ε) y := by
  unfold moll HRS.MS.UniqT3.cv
  congr 1; funext x; ring

theorem e4_kcd_moll {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ε : ℝ} (hε : 0 < ε) (i : Fin d)
    {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) :
    kernelConvDeriv d s i (moll d ε ψ) = moll d ε (kernelConvDeriv d s i ψ) := by
  funext y
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by norm_num)
  have hD : D1 i (moll d ε ψ) = moll d ε (D1 i ψ) := e3_D1_moll hε hψ1 hψc i
  have hbc : Continuous (D1 i ψ) := e3_continuous_D1 hψ1 i
  have hbcs : HasCompactSupport (D1 i ψ) := D1_supp hψc i
  have hηc : Continuous (eta d ε) := eta_contDiff.continuous
  have hηcs : HasCompactSupport (eta d ε) := eta_hasCompactSupport hε
  calc kernelConvDeriv d s i (moll d ε ψ) y
      = HRS.Whole.convFun (rieszKernel d s) (D1 i (moll d ε ψ)) y := by
        rw [n0_kcd_eq]
    _ = HRS.Whole.convFun (rieszKernel d s) (HRS.MS.UniqT3.cv (eta d ε) (D1 i ψ)) y := by
        rw [hD]
        congr 1; funext x
        rw [e4_moll_cv3]
        exact e4_cv_comm _ _ x
    _ = HRS.MS.UniqT3.cv (eta d ε) (HRS.Whole.convFun (rieszKernel d s) (D1 i ψ)) y :=
        K_cv hs0 hsd hηc hηcs hbc hbcs y
    _ = HRS.MS.UniqT3.cv (HRS.Whole.convFun (rieszKernel d s) (D1 i ψ)) (eta d ε) y :=
        e4_cv_comm _ _ y
    _ = moll d ε (kernelConvDeriv d s i ψ) y := by
        rw [e4_moll_cv3, n0_kcd_eq]

theorem e4_kcd_contDiff {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i : Fin d) {F : Euc d → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) : ContDiff ℝ 1 (kernelConvDeriv d s i F) := by
  have hl := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  have hconv : kernelConvDeriv d s i F = convolution (D1 i F) (rieszKernel d s)
      (ContinuousLinearMap.mul ℝ ℝ) volume := by
    funext y
    rw [n0_kcd_eq]
    simp only [HRS.Whole.convFun, convolution_def, ContinuousLinearMap.mul_apply']
    congr 1; funext t; ring
  rw [hconv]
  exact (D1_supp hFc i).contDiff_convolution_left (n := 1) (ContinuousLinearMap.mul ℝ ℝ)
    (D1_contDiff hF i) hl

theorem e4_D1_kcd {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i j : Fin d) {F : Euc d → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (y : Euc d) :
    D1 j (kernelConvDeriv d s i F) y = kernelConvDeriv d s j (D1 i F) y := by
  have hl := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  rw [n0_kcd_eq, n0_kcd_eq]
  exact convFun_D1 hl (D1_contDiff hF i) (D1_supp hFc i) j y

theorem e4_kcd_bdd {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (i : Fin d) {F : Euc d → ℝ}
    (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) :
    ∃ M : ℝ, ∀ y, |kernelConvDeriv d s i F y| ≤ M := by
  obtain ⟨R0, hR0⟩ := hFc.isCompact.isBounded.subset_closedBall (0 : Euc d)
  set R : ℝ := max R0 1 with hR
  have hR1 : 1 ≤ R := le_max_right _ _
  have hsupp : Function.support F ⊆ closedBall 0 R := fun x hx =>
    closedBall_subset_closedBall (le_max_left _ _) (hR0 (subset_tsupport F hx))
  have hcont : Continuous (kernelConvDeriv d s i F) := by
    rw [n0_kcd_eq]
    exact K_cont hs0 hsd (e3_continuous_D1 hF i) (D1_supp hFc i)
  obtain ⟨M1, hM1⟩ := (isCompact_closedBall (0 : Euc d) (2 * R)).exists_bound_of_continuousOn
    hcont.continuousOn
  set P : ℝ := ∫ x, |F x| with hP
  refine ⟨max M1 ((max 1 s * 2 ^ (s + 1)) * P), fun y => ?_⟩
  by_cases hy : ‖y‖ ≤ 2 * R
  · have := hM1 y (by simpa using hy)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  · have hy' : 2 * R ≤ ‖y - 0‖ := by rw [sub_zero]; exact (not_le.1 hy).le
    refine (n0_far_bound hs0 i hF hFc hR1 hsupp hy').trans ?_
    refine le_trans ?_ (le_max_right _ _)
    have hyc : 1 ≤ ‖y - 0‖ := by linarith
    have : ‖y - 0‖ ^ (-s - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hyc (by linarith)
    have hP0 : 0 ≤ P := integral_nonneg fun x => abs_nonneg _
    have hK : 0 ≤ max 1 s * 2 ^ (s + 1) := by positivity
    calc (max 1 s * 2 ^ (s + 1)) * P * ‖y - 0‖ ^ (-s - 1) ≤ (max 1 s * 2 ^ (s + 1)) * P * 1 := by
          gcongr
      _ = _ := mul_one _

end HRS.MS.UniqE4
