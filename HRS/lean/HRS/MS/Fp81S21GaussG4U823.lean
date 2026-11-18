import HRS.MS.Fp81S21GaussG4U8
import HRS.MS.Fp81S21GaussG4U822

/-! The compact reference estimates follow from the propagated energy limits. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Filter Topology
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.S111K4AT

/-- Passing the finite-combination estimates to compact tests, conditional on
continuity of the three propagated pieces along the Hermite truncations. -/
theorem fp81s21_g4_compact_reference_pieces_of_continuity (p : Parameters)
    (hcont : fp81s21_g4Phys p (fun _ R =>
      ∀ f, IsR2Test f → ∀ v w, 0 ≤ v → v ≤ w →
        Tendsto (fun n => fp81s21_g4_initialValue R
          (k4hs (wholeSpaceIndex p.d : ℝ) n f) v w) atTop
          (𝓝 (fp81s21_g4_initialValue R f v w)) ∧
        Tendsto (fun n => fp81s21_g4_Old R
          (k4hs (wholeSpaceIndex p.d : ℝ) n f) v w) atTop
          (𝓝 (fp81s21_g4_Old R f v w)) ∧
        Tendsto (fun n => fp81s21_g4_New R
          (k4hs (wholeSpaceIndex p.d : ℝ) n f) v w) atTop
          (𝓝 (fp81s21_g4_New R f v w)))) :
    fp81s21_g4Phys p (fun _ R =>
      ∃ A : ℝ, 0 ≤ A ∧ ∀ f, IsR2Test f → ∀ v w, 0 ≤ v → v ≤ w →
        fp81s21_g4_initialValue R f v w ≤ A * (w-v)^2 * fp81s21_g4_J p.d f ∧
        fp81s21_g4_Old R f v w ≤ A * (w-v)^2 * fp81s21_g4_J p.d f ∧
        fp81s21_g4_New R f v w ≤ A * ((w-v)+(w-v)^2) * fp81s21_g4_J p.d f) := by
  obtain ⟨δa, ha, hahalf, haR⟩ := fp81s21_g4_combo_pieces p
  obtain ⟨δb, hb, _, hbR⟩ := hcont
  refine ⟨min δa δb, lt_min ha hb, (min_le_left _ _).trans hahalf, ?_⟩
  intro δ hδ hδle R
  obtain ⟨A, hA, hcombo⟩ := haR δ hδ (hδle.trans (min_le_left _ _)) R
  have hlim := hbR δ hδ (hδle.trans (min_le_right _ _)) R
  refine ⟨A, hA, ?_⟩
  intro f hf v w hv hvw
  obtain ⟨hi, ho, hn⟩ := hlim f hf v w hv hvw
  have hcost := fp81s21_g4_cost_approx_values p hf
  have hbound (n : ℕ) := hcombo (k4hs (wholeSpaceIndex p.d : ℝ) n f)
    (k4hs_combo (wholeSpaceIndex p.d : ℝ) n f) v w hv hvw
  refine ⟨?_, ?_, ?_⟩
  · exact le_of_tendsto_of_tendsto hi (tendsto_const_nhds.mul hcost)
      (Filter.Eventually.of_forall fun n => (hbound n).1)
  · exact le_of_tendsto_of_tendsto ho (tendsto_const_nhds.mul hcost)
      (Filter.Eventually.of_forall fun n => (hbound n).2.1)
  · exact le_of_tendsto_of_tendsto hn (tendsto_const_nhds.mul hcost)
      (Filter.Eventually.of_forall fun n => (hbound n).2.2)

#print axioms fp81s21_g4_compact_reference_pieces_of_continuity
end HRS.Fp81.S21
end
