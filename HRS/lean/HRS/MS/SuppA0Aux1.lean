import HRS.Whole.MovingDyn
import HRS.MH.DualityRdB3

/-!
# A0 auxiliary 1: translation of densities, pairings and the shifted test functions (S6.8 (2))
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.A0

open HRS.Whole HRS.MH.DualityRd HRS.Whole.AppendixA

variable {d : ℕ}

lemma a0_integral_shift (μ : Measure (Euc d)) (a : Euc d) (g : Euc d → ℝ) :
    ∫ x, g x ∂(μ.map (fun y => y + a)) = ∫ x, g (x + a) ∂μ :=
  (MeasurableEquiv.addRight a).measurableEmbedding.integral_map g

lemma a0_map_withDensity (ρ : Euc d → ℝ) (a : Euc d) :
    (Whole.withDensityReal ρ).map (fun y => y + a) = Whole.withDensityReal (fun x => ρ (x - a)) := by
  have h := movtr_map_withDensity (MeasurableEquiv.addRight a) (volume : Measure (Euc d))
    (fun x => ENNReal.ofReal (ρ (x - a)))
  unfold Whole.withDensityReal
  have e1 : ((fun x => ENNReal.ofReal (ρ (x - a))) ∘ (MeasurableEquiv.addRight a)) =
      fun x => ENNReal.ofReal (ρ x) := by
    funext x; simp
  rw [e1] at h
  have e2 : (volume : Measure (Euc d)).map (MeasurableEquiv.addRight a) = volume :=
    map_add_right_eq_self volume a
  rw [e2] at h
  exact h

lemma a0_pair_shift (ρ : Euc d → ℝ) (a : Euc d) (g : Euc d → ℝ) :
    Whole.pair (Whole.withDensityReal (fun x => ρ (x - a))) g = Whole.pair (Whole.withDensityReal ρ) (fun y => g (y + a)) := by
  unfold Whole.pair
  rw [← a0_map_withDensity, a0_integral_shift]

lemma a0_gradient_comp_add (f : Euc d → ℝ) (a x : Euc d) :
    gradient (fun y => f (y + a)) x = gradient f (x + a) := by
  unfold gradient
  rw [fderiv_comp_add_right]

lemma a0_laplacian_comp_add (f : Euc d → ℝ) (a x : Euc d) :
    Laplacian.laplacian (fun y => f (y + a)) x = Laplacian.laplacian f (x + a) := by
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    iteratedFDeriv_comp_add_right]

lemma a0_interaction_shift (D : WholeDyn d) (ψ : Euc d → ℝ) (μ : Measure (Euc d)) (a : Euc d) :
    interactionPairingW D (fun x => ψ (x + a)) μ μ =
      interactionPairingW D ψ (μ.map (fun y => y + a)) (μ.map (fun y => y + a)) := by
  unfold interactionPairingW
  congr 1
  rw [a0_integral_shift]
  congr 1
  funext x
  rw [a0_integral_shift]
  congr 1
  funext y
  simp only [add_sub_add_right_eq_sub, a0_gradient_comp_add, add_left_inj]

lemma a0_inner_gradient (ψ : Euc d → ℝ) (z v : Euc d) :
    inner ℝ (gradient ψ z) v = fderiv ℝ ψ z v := by
  unfold gradient
  rw [InnerProductSpace.toDual_symm_apply]

lemma a0_continuous_gradient {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 2 ψ) : Continuous (gradient ψ) := by
  have hc : Continuous (fderiv ℝ ψ) := hψ.continuous_fderiv (by simp)
  unfold gradient
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp hc

lemma a0_norm_gradient (ψ : Euc d → ℝ) (z : Euc d) : ‖gradient ψ z‖ = ‖fderiv ℝ ψ z‖ := by
  unfold gradient
  exact LinearIsometryEquiv.norm_map _ _

end HRS.MS.A0
