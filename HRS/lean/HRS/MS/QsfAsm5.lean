import HRS.MS.QsfAsm4
import HRS.PDE.MeanFieldLinearGaussian
import HRS.Prob.HilbertMartingale

/-!
# S4.5 packet B5 (assembly), part 5: product-measure and trace-norm helpers
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace ContDiff

noncomputable section

namespace S45

open HRS.Whole
open HRS (Euc cbNorm MemCb)

section Prod

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {P : Measure α} {γ : Measure β}
  [IsProbabilityMeasure P] [IsProbabilityMeasure γ] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem s45_integral_fst {g : α → E} (hg : AEStronglyMeasurable g P) :
    ∫ w, g w.1 ∂(P.prod γ) = ∫ x, g x ∂P := by
  have h := (measurePreserving_fst (μ := P) (ν := γ)).map_eq
  have h2 := integral_map (μ := P.prod γ) (φ := Prod.fst) measurable_fst.aemeasurable
    (f := g) (by rw [h]; exact hg)
  rw [h] at h2
  exact h2.symm

theorem s45_integral_snd {g : β → E} (hg : AEStronglyMeasurable g γ) :
    ∫ w, g w.2 ∂(P.prod γ) = ∫ x, g x ∂γ := by
  have h := (measurePreserving_snd (μ := P) (ν := γ)).map_eq
  have h2 := integral_map (μ := P.prod γ) (φ := Prod.snd) measurable_snd.aemeasurable
    (f := g) (by rw [h]; exact hg)
  rw [h] at h2
  exact h2.symm

theorem s45_integrable_fst {g : α → E} (hg : Integrable g P) :
    Integrable (fun w : α × β => g w.1) (P.prod γ) :=
  (measurePreserving_fst (μ := P) (ν := γ)).integrable_comp_of_integrable hg

theorem s45_map_snd : (P.prod γ).map Prod.snd = γ :=
  (measurePreserving_snd (μ := P) (ν := γ)).map_eq

end Prod

/-- A bounded measurable matrix field has integrable trace norm. -/
theorem s45_traceNorm_integrable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {n : ℕ} {D : α → Matrix (Fin n) (Fin n) ℝ} (hD : ∀ i j, Measurable fun w => D w i j) {b : ℝ}
    (hb : ∀ w i j, |D w i j| ≤ b) : Integrable (fun w => HRS.traceNormMatrix (D w)) μ := by
  refine Integrable.of_bound (C := n * (n * b)) (HRS.measurable_traceNormMatrix D hD).aestronglyMeasurable
    (Filter.Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (HRS.traceNormMatrix_nonneg _)]
  refine (HRS.PDE.MFLinear.traceNormMatrix_le_sum _).trans ?_
  calc ∑ i, ∑ j, |D w i j| ≤ ∑ _i : Fin n, ∑ _j : Fin n, b :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hb w i j
    _ = _ := by simp

end S45

end
