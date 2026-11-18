import HRS.MS.SA16TGc3

/-!
# S.A.16 (SA16T) Gc4: strong continuity of the nonlocal operators of the mollified path

`sa16t_strong_of_dense`: a uniformly bounded family of operators that is strongly continuous on a dense set is strongly
continuous.  `sa16t_cont_jet`: for `φ ∈ C_c^∞` the map `r ↦ T_r (J φ)` is continuous, where `T_r` realizes `eucNonlocal` for
`ρ_n ⋆ μ_r` and `(r, y) ↦ μ_r(y)` is continuous (locality of `eucNonlocal` plus `sa16t_G_small` for the cut-off difference).
`sa16t_G_strong`: strong continuity of `r ↦ T_r`.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16P Phase2SA16Q

section Gc4
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16t_strong_of_dense {α Y Z : Type*} [TopologicalSpace α] [NormedAddCommGroup Y] [NormedAddCommGroup Z]
    [NormedSpace ℝ Y] [NormedSpace ℝ Z] {T : α → Y →L[ℝ] Z} {S : Set α} {a : α} (ha : a ∈ S) {B : ℝ}
    (hB : ∀ q ∈ S, ‖T q‖ ≤ B) {D : Set Y} (hD : Dense D)
    (hT : ∀ v ∈ D, ContinuousWithinAt (fun q => T q v) S a) (y : Y) :
    ContinuousWithinAt (fun q => T q y) S a := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB a ha)
  rw [Metric.continuousWithinAt_iff']
  intro ε hε
  set η : ℝ := ε / (4 * (B + 1)) with hη
  have hη0 : 0 < η := by positivity
  obtain ⟨y', hy'D, hy'⟩ := hD.exists_dist_lt y hη0
  have hcont := (Metric.continuousWithinAt_iff'.1 (hT y' hy'D)) (ε / 2) (by positivity)
  filter_upwards [hcont, self_mem_nhdsWithin] with q hq hqS
  have hyy : ‖y - y'‖ < η := by simpa [dist_eq_norm] using hy'
  have hq' : ‖T q y' - T a y'‖ < ε / 2 := by simpa [dist_eq_norm] using hq
  have b1 : ‖T q (y - y')‖ ≤ B * η :=
    ((T q).le_opNorm _).trans (mul_le_mul (hB q hqS) hyy.le (norm_nonneg _) hB0)
  have b2 : ‖T a (y' - y)‖ ≤ B * η := by
    refine ((T a).le_opNorm _).trans (mul_le_mul (hB a ha) ?_ (norm_nonneg _) hB0)
    rw [norm_sub_rev]; exact hyy.le
  have h1 : T q y - T a y = T q (y - y') + (T q y' - T a y') + T a (y' - y) := by
    simp only [map_sub]; abel
  have hBη : B * η ≤ ε / 4 := by
    rw [hη, mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  rw [dist_eq_norm, h1]
  calc ‖T q (y - y') + (T q y' - T a y') + T a (y' - y)‖
      ≤ ‖T q (y - y') + (T q y' - T a y')‖ + ‖T a (y' - y)‖ := norm_add_le _ _
    _ ≤ ‖T q (y - y')‖ + ‖T q y' - T a y'‖ + ‖T a (y' - y)‖ := by
        gcongr; exact norm_add_le _ _
    _ < ε := by linarith

end Gc4

end HRS.Whole.AppendixA.Phase2SA16R
