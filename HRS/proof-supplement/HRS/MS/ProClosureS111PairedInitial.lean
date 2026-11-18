import HRS.MS.ProClosureS111InitialEndpoint

/-!
The exact initial-data branch of the paired physical source estimate.
This is a nonauthor consumer of the all-test initial tensor producer.
The frozen initial-coordinate predicate is retained for both preparations.
No Poincaré or coupling input is needed for this branch.
-/
set_option autoImplicit false
noncomputable section
open Classical MeasureTheory Set
open scoped ENNReal NNReal Topology BigOperators

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.R26T6

/-- Actual physical initial tensors at preparations `gamma` and `beta`,
with the exact frozen all-test coordinates and the V01 initial-difference rate. -/
theorem physical_paired_initial_tensors {d : ℕ} (hd : 2 ≤ d)
    (s a beta gamma T : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    (ha : 0 < a) (hbeta : 0 < beta) (hgamma : 0 ≤ gamma) (hT : 0 < T) :
    ∃ c0 B : ℝ, 0 < c0 ∧ 0 ≤ B ∧
      ∀ rho : Euc d → ℝ, IsThermalEquilibrium d s a beta rho →
      ∀ u : ℝ, 0 ≤ u →
      ∃ Iu Ib : projTensor (R2X d T) 3,
        r26t6_InitialCoordinates d s a beta gamma rho T u Iu ∧
        r26t6_InitialCoordinates d s a beta beta rho T u Ib ∧
        ‖Iu - Ib‖ ≤ B * Real.exp (-3 * c0 * u) := by
  have hGamma : 0 ≤ max beta gamma := hbeta.le.trans (le_max_left _ _)
  obtain ⟨c0, B, hc0, hB, hphysical⟩ :=
    physical_initial_tensor hd s a beta (max beta gamma) T
      hs0 hs ha hbeta hGamma hT
  refine ⟨c0, 2 * B, hc0, mul_nonneg (by norm_num) hB, ?_⟩
  intro rho hrho u hu
  obtain ⟨Iu, hIu, hIunorm⟩ :=
    hphysical rho hrho gamma ⟨hgamma, le_max_right _ _⟩ u hu
  obtain ⟨Ib, hIb, hIbnorm⟩ :=
    hphysical rho hrho beta ⟨hbeta.le, le_max_left _ _⟩ u hu
  refine ⟨Iu, Ib, hIu, hIb, ?_⟩
  calc
    ‖Iu - Ib‖ ≤ ‖Iu‖ + ‖Ib‖ := norm_sub_le _ _
    _ ≤ B * Real.exp (-3 * c0 * u) + B * Real.exp (-3 * c0 * u) :=
      add_le_add hIunorm hIbnorm
    _ = (2 * B) * Real.exp (-3 * c0 * u) := by ring

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.physical_paired_initial_tensors
