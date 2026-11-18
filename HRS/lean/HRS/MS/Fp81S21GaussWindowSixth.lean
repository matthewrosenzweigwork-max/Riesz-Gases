import HRS.MS.Fp81S21GaussSixth2
import HRS.MS.Fp81S21GaussUnif3
import HRS.MS.Fp81S21NoisePath6
import HRS.MS.S111BDAux4

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory
open HRS HRS.Whole HRS.MS.R26T3

namespace HRS.Fp81.S21

/-- A uniform sixth moment for the physical Gaussian shifted windows. -/
theorem fp81s21_gauss_unif_window_sixth (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∀ H : ℝ, 0 < H →
          ∃ M6 : ℝ, 0 ≤ M6 ∧
            ∀ G : GaussianRealization R, ∀ a : ℝ, 0 ≤ a →
              fp81s21_Moment6 G.P
                (processWindow (wholeSpaceIndex p.d : ℝ) H a G.Z) M6 := by
  obtain ⟨δ0, hδ0, hδhalf, hfour⟩ := fp81s21_gauss_unif_window_fourth p
  refine ⟨δ0, hδ0, hδhalf, ?_⟩
  intro δ hδ hδle R H hH
  obtain ⟨B4, hB4, hfourR⟩ := hfour δ hδ hδle R H hH
  let X := OscPath p.d (wholeSpaceIndex p.d : ℝ) H
  obtain ⟨C6, hC6, hsix⟩ := fp81s21_gauss_sixth_bound (B := X)
  refine ⟨C6 * (1 + B4) ^ 6, by positivity, ?_⟩
  intro G a ha
  let W : G.Ω → X := processWindow (wholeSpaceIndex p.d : ℝ) H a G.Z
  obtain ⟨hW, hgauss, -⟩ := HRS.MS.S111BD.s111_shifted_window_gaussian
    p.d G.P (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) p.β⁻¹ H a (a + H)
    (HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ)
    G.Z (G.evolution (a + H)) hH ha le_rfl
  have hprob : IsProbabilityMeasure (G.P.map W) :=
    ⟨by simp [Measure.map_apply_of_aemeasurable hW MeasurableSet.univ, W]⟩
  have hcont4 : Continuous (fun x : X => ‖x‖ ^ 4) := by fun_prop
  have hcont6 : Continuous (fun x : X => ‖x‖ ^ 6) := by fun_prop
  obtain ⟨hi4, hb4⟩ := hfourR a ha G
  have hi4map : Integrable (fun x : X => ‖x‖ ^ 4) (G.P.map W) :=
    (integrable_map_measure hcont4.aestronglyMeasurable hW).2 hi4
  have hb4map : (∫ x : X, ‖x‖ ^ 4 ∂G.P.map W) ≤ B4 := by
    rw [integral_map hW hcont4.aestronglyMeasurable]
    exact hb4
  obtain ⟨hi6, hb6⟩ := hsix (G.P.map W) hprob hgauss B4 hB4 hi4map hb4map
  refine ⟨hW, (integrable_map_measure hcont6.aestronglyMeasurable hW).1 hi6, ?_⟩
  rw [integral_map hW hcont6.aestronglyMeasurable] at hb6
  exact hb6

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_gauss_unif_window_sixth
