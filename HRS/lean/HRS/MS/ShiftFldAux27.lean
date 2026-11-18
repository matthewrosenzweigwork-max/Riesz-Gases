import HRS.MS.ShiftFldAux26

/-!
# S79P: the covariance `K(τ, τ+δ)` does not depend on `τ` (Hermite test functions)
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.S79G

open HRS.Whole HRS.MS.UniqT3 HRS.MS.S21 HRS.MH.DualityRd
open HRS (Euc)

variable {d : ℕ}

/-- The covariance of the stationary Gaussian field of `IsStationaryGaussianField` between times `τ, τ'`. -/
def Kcov (d : ℕ) (s a β : ℝ) (τ τ' : ℝ) (φ ψ : Euc d → ℝ) : ℝ :=
  HRS.Whole.susceptibilityCov (rieszKernel d s) (thermalMeasure d s a β) β
      (propagatorW (Cst d s a β) 0 τ φ) (propagatorW (Cst d s a β) 0 τ' ψ) +
    noiseCovW (Cst d s a β) β⁻¹ τ τ' φ ψ

theorem s79g_gam_eq (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) {f g : Euc d → ℝ} (hf : HRS.MemCb 2 f) (hg : HRS.MemCb 2 g) :
    ∫ x, inner ℝ (gradient f x) (gradient g x) * thermalDensity d s a β x = Gam d s a β f g := by
  obtain ⟨C, c, BU, hT⟩ := S45.s45_thermal_data hd hs0 hsd ha hβ
  obtain ⟨f0, f1, f2, hf0, hf1, hf2, hbf0, hbf1, hbf2⟩ := s79g_memcb_bounds hf
  obtain ⟨g0, g1, g2, hg0, hg1, hg2, hbg0, hbg1, hbg2⟩ := s79g_memcb_bounds hg
  unfold Gam
  have hint : ∀ i : Fin d, Integrable (fun x => thermalDensity d s a β x * (D1 i f x * D1 i g x)) := by
    intro i
    refine Integrable.mono' ((HRS.MH.CoercLower.isProbDensity_integrable hT.prob).mul_const (f1 * g1))
      (hT.smooth.continuous.mul (((D1_contDiff hf.1 i).continuous.mul (D1_contDiff hg.1 i).continuous))).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hT.prob.nonneg x), abs_mul]
    calc thermalDensity d s a β x * (|D1 i f x| * |D1 i g x|) ≤ thermalDensity d s a β x * (f1 * g1) :=
          mul_le_mul_of_nonneg_left (mul_le_mul (hbf1 i x) (hbg1 i x) (abs_nonneg _) hf1) (hT.prob.nonneg x)
      _ = _ := by ring
  rw [← integral_finsetSum _ (fun i _ => hint i)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [PiLp.inner_apply, HRS.MD.DOMProof.domp_gradient_apply]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [HRS.MD.DOMProof.dk, D1, mul_comm, mul_left_comm]

theorem s79g_Kstat (hd : 2 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) (hρ : IsThermalEquilibrium d s a β (thermalDensity d s a β)) (m : ℝ)
    (α α' : MultiIndex d) {τ0 δ : ℝ} (hτ0 : 0 ≤ τ0) (hδ : 0 ≤ δ) :
    Kcov d s a β τ0 (τ0 + δ) (oscTestFun m α) (oscTestFun m α') =
      Kcov d s a β 0 δ (oscTestFun m α) (oscTestFun m α') := by
  set φ := oscTestFun m α with hφ
  set ψ := oscTestFun m α' with hψ
  have hτ1 : 0 ≤ τ0 + δ := add_nonneg hτ0 hδ
  obtain ⟨u, hu, hpu⟩ := s79g_classical hd hs.le hsd ha hβ m α hτ0
  obtain ⟨v, hv, hpv⟩ := s79g_classical hd hs.le hsd ha hβ m α' hτ1
  have gu := goodPath_of_classical hu
  have gv := (goodPath_of_classical hv).mono (show τ0 ≤ τ0 + δ by linarith)
  have hFTC := s79g_FTC hd hs hsd ha hβ hρ hτ0 gu gv
  -- the noise term
  have hnoise : noiseCovW (Cst d s a β) β⁻¹ τ0 (τ0 + δ) φ ψ =
      2 * β⁻¹ * ∫ r in (0 : ℝ)..τ0, Gam d s a β (u r) (v r) := by
    unfold noiseCovW
    rw [min_eq_left (by linarith), integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le hτ0]
    congr 1
    refine intervalIntegral.integral_congr fun r hr => ?_
    rw [Set.uIcc_of_le hτ0] at hr
    have hr' : r ∈ Icc (0 : ℝ) τ0 := hr
    rw [hpu r hr', hpv r ⟨hr.1, hr.2.trans (by linarith)⟩]
    exact s79g_gam_eq hd hs.le hsd ha hβ (gu.memCb r hr') (gv.memCb r hr')
  have h0u : propagatorW (Cst d s a β) 0 τ0 φ = u 0 := hpu 0 ⟨le_rfl, hτ0⟩
  have h0v : propagatorW (Cst d s a β) 0 (τ0 + δ) ψ = v 0 := hpv 0 ⟨le_rfl, hτ1⟩
  have hvτ : v τ0 = propagatorW (Cst d s a β) 0 δ ψ := by
    rw [← hpv τ0 ⟨hτ0, by linarith⟩, s79g_translate hd hs.le hsd ha hβ m α' hτ1 hτ0 (by linarith) le_rfl]
    congr 1
    ring
  have huτ : u τ0 = φ := hu.terminal
  -- time zero
  obtain ⟨u0, hu0, hpu0⟩ := s79g_classical hd hs.le hsd ha hβ m α (le_refl (0 : ℝ))
  have hprop00 : propagatorW (Cst d s a β) 0 0 φ = φ := by
    rw [hpu0 0 ⟨le_rfl, le_rfl⟩]; exact hu0.terminal
  have hnoise0 : noiseCovW (Cst d s a β) β⁻¹ 0 δ φ ψ = 0 := by
    unfold noiseCovW
    rw [min_eq_left hδ, Set.Icc_self]
    simp
  unfold Kcov
  rw [hnoise, h0u, h0v, hprop00, hnoise0, ← hvτ, ← huτ]
  linarith

end HRS.MS.S79G
