import HRS.MS.S82P2Mom

/-!
# S8.2 (S82P2): variance under a dominated probability law
If `P ≤ c • Q` for probability laws `P`, `Q` then `evariance F P ≤ c * evariance F Q`,
because the variance minimises the mean square error and `P` is dominated.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82P2

lemma s82p2_evariance_le_sub_const {E : Type*} [MeasurableSpace E] (P : Measure E)
    [IsProbabilityMeasure P] (F : E → ℝ) (hF : MemLp F 2 P) (a : ℝ) :
    evariance F P ≤ ∫⁻ x, ‖F x - a‖ₑ ^ 2 ∂P := by
  have hint : Integrable F P := hF.integrable (by norm_num)
  have hG : MemLp (fun x => F x - a) 2 P := hF.sub (memLp_const a)
  have h1 : evariance (fun x => F x - a) P = evariance F P := by
    unfold evariance
    have : ∫ x, (F x - a) ∂P = (∫ x, F x ∂P) - a := by
      rw [integral_sub hint (integrable_const a), integral_const]
      simp
    have h2 : ∀ x, F x - a - ((∫ x, F x ∂P) - a) = F x - ∫ x, F x ∂P := fun x => by ring
    simp only [this, h2]
  rw [← h1, evariance_def' hG.aestronglyMeasurable]
  exact tsub_le_self

lemma s82p2_evariance_le_of_le_smul {E : Type*} [MeasurableSpace E] {P Q : Measure E}
    [IsProbabilityMeasure P] {c : ℝ≥0∞} (hc : c ≠ ⊤) (hPQ : P ≤ c • Q) (F : E → ℝ)
    (hF : AEStronglyMeasurable F Q) [IsFiniteMeasure Q] :
    evariance F P ≤ c * evariance F Q := by
  by_cases hmem : MemLp F 2 Q
  · have hmemP : MemLp F 2 P := (hmem.smul_measure hc).mono_measure hPQ
    refine (s82p2_evariance_le_sub_const P F hmemP (∫ x, F x ∂Q)).trans ?_
    calc ∫⁻ x, ‖F x - ∫ x, F x ∂Q‖ₑ ^ 2 ∂P
        ≤ ∫⁻ x, ‖F x - ∫ x, F x ∂Q‖ₑ ^ 2 ∂(c • Q) := lintegral_mono' hPQ le_rfl
      _ = c * evariance F Q := by
        rw [lintegral_smul_measure, smul_eq_mul]
        rfl
  · have hc0 : c ≠ 0 := by
      rintro rfl
      have := hPQ Set.univ
      simp at this
    have h := evariance_eq_top hF hmem
    rw [h, ENNReal.mul_top hc0]
    exact le_top

end HRS.MS.S82P2
