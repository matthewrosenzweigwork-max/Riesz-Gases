import HRS.MS.S82P2Mom
import HRS.MS.QsfCorr2
import HRS.MH.PairingRdP5

/-!
# S8.2 (S82T): the mean force `forceMean rho` is measurable and bounded (thermal density)
`forceMean rho = convGradConvW (rieszKernelGrad d s) rho` is the cancellation convolution; for the
thermal density (Lipschitz, integrable) it is bounded by `PairingRdP.integrable_conv_rd` and measurable
by `StronglyMeasurable.integral_prod_right'`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82T
open HRS HRS.Whole HRS.MS.Phase2S82

lemma s82t_forceMean_measurable {d : ℕ} {rho : Euc d → ℝ} (hρ : Measurable rho) :
    Measurable (forceMean rho) := by
  unfold forceMean convGradConvW
  have hG := HRS.Whole.movtr_rieszKernelGrad_measurable (d := d) (criticalS d)
  have hsub : Measurable (fun p : Euc d × Euc d => p.1 - p.2) := measurable_fst.sub measurable_snd
  have hF : Measurable (fun p : Euc d × Euc d =>
      if ‖p.1 - p.2‖ ≤ 1 / 4 then
        (rho p.2 - rho p.1) • rieszKernelGrad d (criticalS d) (p.1 - p.2)
      else rho p.2 • rieszKernelGrad d (criticalS d) (p.1 - p.2)) := by
    refine Measurable.ite (measurableSet_le (measurable_norm.comp hsub) measurable_const) ?_ ?_
    · exact ((hρ.comp measurable_snd).sub (hρ.comp measurable_fst)).smul (hG.comp hsub)
    · exact (hρ.comp measurable_snd).smul (hG.comp hsub)
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable

/-- The thermal mean force is measurable and bounded (constant depending only on `d, a, beta`). -/
theorem s82t_forceMean_bdd {d : ℕ} (hd : 2 ≤ d) {a beta : ℝ} (ha : 0 < a) (hbeta : 0 < beta) :
    ∃ K : ℝ, 0 ≤ K ∧ Measurable (forceMean (HRS.Whole.thermalDensity d (criticalS d) a beta)) ∧
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
  have hρm : Measurable rho := hT.prob.measurable
  have hint : Integrable rho := integrable_of_integral_eq_one hT.prob.integral_one
  obtain ⟨-, K, hK⟩ := HRS.MH.PairingRdP.integrable_conv_rd (d := d) (by omega) hs0 hsd hρm hint hT.C0
    (β := 1) (by have : (2 : ℝ) ≤ d := by exact_mod_cast hd
                 unfold criticalS at *; linarith) hlip
  refine ⟨max K 0, le_max_right _ _, s82t_forceMean_measurable hρm, fun x => ?_⟩
  exact (hK x).trans (le_max_left _ _)

end HRS.MS.S82T
