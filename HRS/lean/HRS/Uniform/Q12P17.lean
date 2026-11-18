import HRS.Uniform.Q12P16
import HRS.PDE.MeanFieldSemigroup

/-!
# Q12, Peyre part 17: the Dirichlet energy of the Poisson solution
-/

noncomputable section

open HRS MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Real

namespace HRS.Uniform.Q12

variable {d : ℕ}

namespace PeyreData

variable (D : PeyreData d)

/-- `∫ |∇u|² = -∫ u Δu = ∫ u (f - g)`. -/
lemma energy_eq : D.energy = ∫ x : Torus d, D.u x * (D.f x - D.g x) := by
  have hu2 := D.isCk_u
  have hu1 : Torus.IsCk 1 D.u := hu2.of_le (by norm_num)
  have hnorm : ∀ x : Torus d, ‖D.gradU (Torus.rep x)‖ ^ 2 =
      ∑ j : Fin d, (Torus.partialDeriv j D.u x * Torus.partialDeriv j D.u x) := by
    intro x
    unfold PeyreData.gradU
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Real.norm_eq_abs, sq_abs, q12_gradient_coord]
    unfold Torus.partialDeriv; ring
  unfold energy
  simp_rw [hnorm]
  have hc : ∀ j : Fin d, Continuous fun x : Torus d =>
      Torus.partialDeriv j D.u x * Torus.partialDeriv j D.u x := fun j =>
    (PDE.continuous_partialDeriv j D.u hu1).mul (PDE.continuous_partialDeriv j D.u hu1)
  rw [integral_finset_sum _ fun j _ =>
    (hc j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)]
  have hibp : ∀ j : Fin d, ∫ x : Torus d, Torus.partialDeriv j D.u x * Torus.partialDeriv j D.u x =
      -∫ x : Torus d, D.u x * Torus.partialDeriv j (Torus.partialDeriv j D.u) x := fun j =>
    PDE.integral_partialDeriv_mul j D.u (Torus.partialDeriv j D.u) hu1
      (PDE.isCk_one_partialDeriv j D.u hu2)
  simp_rw [hibp]
  rw [Finset.sum_neg_distrib]
  have huc : Continuous D.u := Torus.continuous_of_continuous_lift D.contDiff_lift_u.continuous
  have hc2 : ∀ j : Fin d, Continuous fun x : Torus d =>
      D.u x * Torus.partialDeriv j (Torus.partialDeriv j D.u) x := fun j =>
    huc.mul (PDE.continuous_partialDeriv j _ (PDE.isCk_one_partialDeriv j D.u hu2))
  rw [← integral_finset_sum _ fun j _ =>
    (hc2 j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)]
  rw [← integral_neg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show -∑ j : Fin d, D.u x * Torus.partialDeriv j (Torus.partialDeriv j D.u) x = D.u x * (D.f x - D.g x)
  rw [← Finset.mul_sum, ← PDE.laplacian_eq_sum D.u hu2 x, D.hΔ x]
  ring

end PeyreData

end HRS.Uniform.Q12
