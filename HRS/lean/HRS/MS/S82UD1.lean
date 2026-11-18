import HRS.MS.S82UC3

/-!
# S8.2 A01 (S82U): thermal facts, `s82t_J1` as the abstract `J ψ`, Q-specific Jmean and grouped form
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82U
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82P2 HRS.MS.S82T HRS.MH.PairingRd

/-- Thermal bundle for the quadratic critical model. -/
lemma u_thermal {d : ℕ} (hd : 2 ≤ d) {a beta : ℝ} (ha : 0 < a) (hbeta : 0 < beta) :
    ∃ Λ Gc c K : ℝ, UForce d (HRS.Whole.thermalDensity d (criticalS d) a beta) Λ ∧
      HRS.Whole.HasR2GaussianUpper Gc c (HRS.Whole.thermalDensity d (criticalS d) a beta) ∧
      0 < Gc ∧ 0 < c ∧ 0 ≤ K ∧ Measurable (forceMean (HRS.Whole.thermalDensity d (criticalS d) a beta)) ∧
      ∀ x, ‖forceMean (HRS.Whole.thermalDensity d (criticalS d) a beta) x‖ ≤ K := by
  have hs0 : 0 ≤ criticalS d := by unfold criticalS; positivity
  have hsd : criticalS d < d := by
    unfold criticalS
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  obtain ⟨Cth, cth, BU, hT⟩ := S45.s45_thermal_data hd hs0 hsd ha hbeta
  set rho := HRS.Whole.thermalDensity d (criticalS d) a beta with hrho
  have hdiff : Differentiable ℝ rho := hT.smooth.differentiable (by simp)
  have hlip : ∀ x z : Euc d, ‖z‖ ≤ 1 / 4 → |rho (x - z) - rho x| ≤ Cth * ‖z‖ ^ (1 : ℝ) := by
    intro x z _
    have h1 := Convex.norm_image_sub_le_of_norm_fderiv_le (f := rho) (s := Set.univ) (C := Cth)
      (fun y _ => hdiff y) (fun y _ => by
        refine (hT.h1 y).trans ?_
        have : Real.exp (-cth * ‖y‖ ^ 2) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖y‖, hT.hc])
        nlinarith [hT.C0]) convex_univ (Set.mem_univ x) (Set.mem_univ (x - z))
    rw [Real.rpow_one, Real.norm_eq_abs] at *
    have e : ‖x - z - x‖ = ‖z‖ := by rw [sub_sub_cancel_left, norm_neg]
    rw [e] at h1
    exact h1
  obtain ⟨K, hK0, hKm, hK⟩ := s82t_forceMean_bdd hd ha hbeta
  refine ⟨Cth, Cth + 1, cth, K, ⟨hT.prob, hT.C0, hlip⟩, ⟨hT.hc, fun x => ?_⟩, by linarith [hT.C0],
    hT.hc, hK0, hKm, hK⟩
  have h1 := (le_abs_self _).trans (hT.h0 x)
  have h2 : 0 ≤ Real.exp (-cth * ‖x‖ ^ 2) := (Real.exp_pos _).le
  nlinarith

lemma u_matVec_neg_one {d : ℕ} (v : Euc d) :
    Torus.matVec ((-1 : Matrix (Fin d) (Fin d) ℝ).transpose) v = -v := by
  unfold Torus.matVec
  rw [Matrix.transpose_neg, Matrix.transpose_one, map_neg]
  simp

lemma u_conv_neg {d : ℕ} (G : Euc d → Euc d) (h : Euc d → ℝ) (x : Euc d) :
    convGradConvW G (fun w => -(h w)) x = -convGradConvW G h x := by
  unfold convGradConvW
  rw [← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  split_ifs
  · rw [← neg_smul]; congr 1; ring
  · rw [neg_smul]

/-- `s82t_J1` for the critical coefficients is the abstract `J ψ`. -/
lemma u_J1_eq {d : ℕ} (a beta : ℝ) (rho : Euc d → ℝ) (gt : Euc d → Euc d → Euc d) (x y : Euc d) :
    s82t_J1 (critCoeff d a beta rho) gt x y =
      ∑ j : Fin d, (convGradConvW (rieszKernelGrad d (criticalS d))
        (fun w => rho w * gt w y j) x) j := by
  unfold s82t_J1
  have hM : (critCoeff d a beta rho).M = -1 := rfl
  have hρ : (critCoeff d a beta rho).ρ 0 = rho := rfl
  have hs : (critCoeff d a beta rho).s = criticalS d := rfl
  simp only [hM, hρ, hs, u_matVec_neg_one, PiLp.neg_apply, mul_neg]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [u_conv_neg (rieszKernelGrad d (criticalS d)) (fun w => rho w * gt w y j) x]
  simp

end HRS.MS.S82U
