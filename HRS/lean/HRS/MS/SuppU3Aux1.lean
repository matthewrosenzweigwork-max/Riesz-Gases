import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# U3, part 1: derivatives of a mollification

For `ρ ∈ C_c^∞(ℝ^d)` and `G ∈ C^n`, `D^n(ρ ⋆ G) = ρ ⋆ D^n G` (`u3_conv_iter` for compactly supported `G`,
`u3_conv_iter_local` for `ρ` supported in the unit ball and arbitrary `G`).
-/

noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff Convolution

namespace HRS.MS.SuppU3

variable {d : ℕ}

theorem u3_precompR_lsmul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (a : ℝ)
    (T : EuclideanSpace ℝ (Fin d) →L[ℝ] F) :
    ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F).precompR (EuclideanSpace ℝ (Fin d))) a T = a • T := by
  ext v; simp

theorem u3_conv_iter (ρ : EuclideanSpace ℝ (Fin d) → ℝ) (hρ : Continuous ρ)
    (n : ℕ) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (G : EuclideanSpace ℝ (Fin d) → F) (hG : ContDiff ℝ n G) (hGc : HasCompactSupport G)
    (x : EuclideanSpace ℝ (Fin d)) :
    iteratedFDeriv ℝ n (fun y => ∫ t, ρ t • G (y - t)) x = ∫ t, ρ t • iteratedFDeriv ℝ n G (x - t) := by
  induction n generalizing F with
  | zero =>
    have hint : ∀ y, Integrable (fun t => ρ t • G (y - t)) := by
      intro y
      have := hGc.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F)
        (hρ.locallyIntegrable (μ := volume)) hG.continuous y
      exact this
    rw [iteratedFDeriv_zero_eq_comp]
    simp only [Function.comp_apply]
    have key := LinearIsometry.integral_comp_comm
      (continuousMultilinearCurryFin0 ℝ (EuclideanSpace ℝ (Fin d)) F).symm.toLinearIsometry
      (fun t => ρ t • G (x - t)) (μ := volume)
    simp only [LinearIsometryEquiv.coe_toLinearIsometry] at key
    rw [← key]
    congr 1
  | succ n ih =>
    have hfd : ∀ y, fderiv ℝ (fun y => ∫ t, ρ t • G (y - t)) y = ∫ t, ρ t • fderiv ℝ G (y - t) := by
      intro y
      have h1 := hGc.hasFDerivAt_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F)
        (μ := volume) (hρ.locallyIntegrable (μ := volume))
        (hG.of_le (by exact_mod_cast Nat.le_add_left 1 n)) y
      have e1 : (ρ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] G) = fun y => ∫ t, ρ t • G (y - t) :=
        funext fun y => by rw [convolution_lsmul]
      rw [e1] at h1
      rw [h1.fderiv, convolution_def]
      congr 1
    rw [iteratedFDeriv_succ_eq_comp_right]
    simp only [Function.comp_apply]
    have e2 : (fun y => fderiv ℝ (fun y => ∫ t, ρ t • G (y - t)) y) =
        fun y => ∫ t, ρ t • fderiv ℝ G (y - t) := funext hfd
    rw [e2]
    have ihG := ih (F := EuclideanSpace ℝ (Fin d) →L[ℝ] F) (fderiv ℝ G)
      (hG.fderiv_right (m := n) (by exact_mod_cast le_rfl)) (hGc.fderiv ℝ)
    rw [ihG]
    have key := LinearIsometry.integral_comp_comm
      (continuousMultilinearCurryRightEquiv' ℝ n (EuclideanSpace ℝ (Fin d)) F).symm.toLinearIsometry
      (fun t => ρ t • iteratedFDeriv ℝ n (fderiv ℝ G) (x - t)) (μ := volume)
    simp only [LinearIsometryEquiv.coe_toLinearIsometry] at key
    rw [← key]
    congr 1; ext t
    rw [map_smul, iteratedFDeriv_succ_eq_comp_right]
    rfl

theorem u3_conv_iter_local (ρ : EuclideanSpace ℝ (Fin d) → ℝ) (hρ : Continuous ρ)
    (hρs : Function.support ρ ⊆ ball (0 : EuclideanSpace ℝ (Fin d)) 1)
    (n : ℕ) {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (G : EuclideanSpace ℝ (Fin d) → F) (hG : ContDiff ℝ n G)
    (x : EuclideanSpace ℝ (Fin d)) :
    iteratedFDeriv ℝ n (fun y => ∫ t, ρ t • G (y - t)) x = ∫ t, ρ t • iteratedFDeriv ℝ n G (x - t) := by
  let κ : ContDiffBump x := ⟨2, 3, by norm_num, by norm_num⟩
  set Gk : EuclideanSpace ℝ (Fin d) → F := fun y => κ y • G y with hGk
  have hGkd : ContDiff ℝ n Gk := (κ.contDiff.of_le (by exact_mod_cast le_top)).smul hG
  have hGkc : HasCompactSupport Gk := κ.hasCompactSupport.smul_right
  have hκ1 : ∀ y, ‖y - x‖ < 2 → Gk y = G y := by
    intro y hy
    have : κ y = 1 := κ.one_of_mem_closedBall (by rw [mem_closedBall, dist_eq_norm]; exact hy.le)
    simp [hGk, this]
  have hEq : (fun y => ∫ t, ρ t • G (y - t)) =ᶠ[𝓝 x] (fun y => ∫ t, ρ t • Gk (y - t)) := by
    filter_upwards [ball_mem_nhds x one_pos] with y hy
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    by_cases ht : ρ t = 0
    · simp [ht]
    · have h1 : ‖t‖ < 1 := by simpa using hρs (Function.mem_support.2 ht)
      have h2 : ‖y - x‖ < 1 := by simpa [dist_eq_norm] using hy
      have : ‖y - t - x‖ < 2 := by
        calc ‖y - t - x‖ = ‖(y - x) - t‖ := by congr 1; abel
          _ ≤ ‖y - x‖ + ‖t‖ := norm_sub_le _ _
          _ < 2 := by linarith
      simp only [hκ1 _ this]
  rw [(hEq.iteratedFDeriv ℝ n).eq_of_nhds, u3_conv_iter ρ hρ n Gk hGkd hGkc x]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  by_cases ht : ρ t = 0
  · simp [ht]
  · have h1 : ‖t‖ < 1 := by simpa using hρs (Function.mem_support.2 ht)
    have hev : Gk =ᶠ[𝓝 (x - t)] G := by
      filter_upwards [ball_mem_nhds (x - t) (show (0:ℝ) < 1 by norm_num)] with y hy
      apply hκ1
      have h2 : ‖y - (x - t)‖ < 1 := by simpa [dist_eq_norm] using hy
      calc ‖y - x‖ = ‖(y - (x - t)) - t‖ := by congr 1; abel
        _ ≤ ‖y - (x - t)‖ + ‖t‖ := norm_sub_le _ _
        _ < 2 := by linarith
    simp only [(hev.iteratedFDeriv ℝ n).eq_of_nhds]

end HRS.MS.SuppU3
