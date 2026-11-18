import HRS.MS.Fp81S21GaussWindowSixth
import HRS.MS.Fp81S21JointL2

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
open HRS HRS.Whole HRS.MS.R26T3 Set

namespace HRS.Fp81.S21

/-- The arbitrary-horizon raw path coupling profile, with its Gaussian
sixth-moment input discharged by the uniform physical Gaussian window bound. -/
theorem fp81s21_jointL_arbitrary_horizon_raw_profile_unconditional (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∀ H : ℝ, 0 < H →
          ∃ d : ℕ → ℝ, fp81s21_NonnegativeVanishing d ∧
          ∃ Mpath : ℝ, 0 ≤ Mpath ∧
            ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
              ∀ G : GaussianRealization R, ∀ a : ℝ, 0 ≤ a →
              ∀ ε : ℝ, 0 < ε →
                ∃ π : Measure
                    (OscPath p.d ((wholeSpaceIndex p.d : ℕ) : ℝ) H ×
                     OscPath p.d ((wholeSpaceIndex p.d : ℕ) : ℝ) H),
                  IsProbabilityMeasure π ∧
                  π.map Prod.fst =
                    law A.P (flucPathW ((wholeSpaceIndex p.d : ℕ) : ℝ) H a
                      (Real.sqrt (N : ℝ)) A.X R.ρ) ∧
                  π.map Prod.snd =
                    law G.P (processWindow ((wholeSpaceIndex p.d : ℕ) : ℝ) H a G.Z) ∧
                  Integrable (fun z => ‖z.1‖ ^ 6) π ∧
                  Integrable (fun z => ‖z.2‖ ^ 6) π ∧
                  (∫ z, ‖z.1‖ ^ 6 ∂π) ≤ Mpath ∧
                  (∫ z, ‖z.2‖ ^ 6 ∂π) ≤ Mpath ∧
                  Integrable (fun z => ‖z.1 - z.2‖) π ∧
                  ((∫ z, ‖z.1 - z.2‖ ∂π) ≤ d N + ε) := by
  obtain ⟨δG, hδG, hδGhalf, hG⟩ := fp81s21_gauss_unif_window_sixth p
  obtain ⟨δL, hδL, hδLhalf, hL⟩ :=
    fp81s21_jointL_arbitrary_horizon_raw_profile p
  let δ0 : ℝ := min δG δL
  have hδ0 : 0 < δ0 := lt_min hδG hδL
  have hδ0half : δ0 ≤ 1 / 2 :=
    (min_le_left _ _).trans hδGhalf
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R H hH
  have hδGle : δ ≤ δG := hδle.trans (min_le_left _ _)
  have hδLle : δ ≤ δL := hδle.trans (min_le_right _ _)
  have hsix :
      ∀ H' : ℝ, 0 < H' →
        ∃ M6 : ℝ, 0 ≤ M6 ∧
          ∀ G : GaussianRealization R, ∀ a : ℝ, 0 ≤ a →
            fp81s21_Moment6 G.P
              (processWindow ((wholeSpaceIndex p.d : ℕ) : ℝ) H' a G.Z) M6 := by
    intro H' hH'
    obtain ⟨M6, hM6, hG6⟩ := hG δ hδ hδGle R H' hH'
    refine ⟨M6, hM6, ?_⟩
    intro G a ha
    exact hG6 G a ha
  exact hL δ hδ hδLle R hsix H hH

#print axioms fp81s21_jointL_arbitrary_horizon_raw_profile_unconditional

end HRS.Fp81.S21

end
