import HRS.MS.ProClosureS111InitialTests
import HRS.MS.ProClosureS111InitialCubic
import HRS.MS.R26T6CD03

/-!
The physical initial cubic tensor with the exact frozen all-test
`r26t6_InitialCoordinates` predicate. Constants are selected before the
thermal density, every preparation parameter in the closed interval,
and every nonnegative time shift, including the independent endpoint.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.R26T6

variable {d : ℕ}

/-- Actual physical initial projective tensors, satisfying every test and
time quantifier of the frozen initial-coordinate predicate. -/
theorem physical_initial_tensor (hd : 2 ≤ d)
    (s a beta Gamma T : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) (hGamma : 0 ≤ Gamma) (hT : 0 < T) :
    ∃ c0 B : ℝ, 0 < c0 ∧ 0 ≤ B ∧
      ∀ rho : Euc d → ℝ, IsThermalEquilibrium d s a beta rho →
      ∀ gamma ∈ Icc (0 : ℝ) Gamma, ∀ u : ℝ, 0 ≤ u →
      ∃ I : projTensor (R2X d T) 3,
        r26t6_InitialCoordinates d s a beta gamma rho T u I ∧
        ‖I‖ ≤ B * Real.exp (-3 * c0 * u) := by
  obtain ⟨c0, B, hc0, hB, hphysical⟩ :=
    physical_initial_cubic_lift hd s a beta Gamma T hs0 hs ha hbeta hGamma hT
  refine ⟨c0, B, hc0, hB, ?_⟩
  intro rho hrho gamma hgamma u hu
  obtain ⟨L, hL3, hcoord, hLbound, I, hIpair, hInorm⟩ :=
    hphysical rho hrho gamma hgamma u hu
  refine ⟨I, ?_, hInorm⟩
  intro tau phi hphi M hM
  let C := r26t6_thermalCoeff d s a beta rho
  let mu := HRS.Whole.withDensityReal rho
  let h := fun i : Fin 3 => HRS.Whole.responseInverse (rieszKernel d s) mu gamma
    (propagatorW C 0 (u + tau i) (phi i))
  change (I : TensorDual (R2X d T) 3) M = ∫ x, h 0 x * h 1 x * h 2 x ∂mu
  have hobs : ∀ i : Fin 3,
      (fun x => r26t6_obs (L x) (tau i) (phi i)) =ᵐ[mu] h i := by
    intro i
    exact physical_initial_all_tests hd hs0 hs ha hbeta hgamma.1 hrho
      (add_nonneg hu (tau i).property.1)
      (fun x => OscPath.at' (L x) (tau i)) (hcoord (tau i)) (phi i) (hphi i)
  rw [hIpair M]
  apply integral_congr_ae
  filter_upwards [ae_all_iff.2 hobs] with x hx
  rw [hM]
  have hdiag : (![L x, L x, L x] : Fin 3 → R2X d T) = fun _ => L x := by
    funext i
    fin_cases i <;> rfl
  rw [hdiag]
  calc
    _ = ∏ i : Fin 3, h i x := Finset.prod_congr rfl fun i _ => hx i
    _ = h 0 x * h 1 x * h 2 x := by simp [Fin.prod_univ_succ, mul_assoc]

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.physical_initial_tensor
