import HRS.MS.R2InterpAux62
import HRS.MS.R2QtAux1

/-!
# S10.2 (worker S102), part 66 (packet M1, reweighting): removing a density of the initial law

If the initial law is `Q.withDensity φ` with `φ > 0`, then `P' = P.withDensity (φ(X₀)⁻¹)` is a probability measure under which `X₀ ∼ Q` and every random
variable independent of `X₀` under `P` has the same law and is still independent of `X₀`.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]

/-- The reweighted measure. -/
def s102_rew (P : Measure Ω) (X0 : Ω → E) (φ : E → ℝ≥0∞) : Measure Ω :=
  P.withDensity (fun ω => (φ (X0 ω))⁻¹)

section Reweight

variable (P : Measure Ω) [IsProbabilityMeasure P] (X0 : Ω → E) (hX0 : Measurable X0)
  (Q : Measure E) [IsProbabilityMeasure Q] (φ : E → ℝ≥0∞) (hφ : Measurable φ)
  (hpos : ∀ x, 0 < φ x) (hfin : ∀ x, φ x ≠ ⊤) (hlaw : P.map X0 = Q.withDensity φ)

include hX0 hφ hpos hfin hlaw

theorem s102_rew_lintegral {f : E → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ ω, f (X0 ω) * (φ (X0 ω))⁻¹ ∂P = ∫⁻ x, f x ∂Q := by
  have h1 : ∫⁻ ω, f (X0 ω) * (φ (X0 ω))⁻¹ ∂P = ∫⁻ x, f x * (φ x)⁻¹ ∂(P.map X0) :=
    (lintegral_map (f := fun x => f x * (φ x)⁻¹) (hf.mul hφ.inv) hX0).symm
  rw [h1, hlaw, lintegral_withDensity_eq_lintegral_mul (g := fun x => f x * (φ x)⁻¹) Q hφ (hf.mul hφ.inv)]
  refine lintegral_congr fun x => ?_
  simp only [Pi.mul_apply]
  rw [mul_comm (φ x), mul_assoc, ENNReal.inv_mul_cancel (hpos x).ne' (hfin x), mul_one]

theorem s102_rew_apply {S : Set Ω} (hS : MeasurableSet S) :
    s102_rew P X0 φ S = ∫⁻ ω, S.indicator 1 ω * (φ (X0 ω))⁻¹ ∂P := by
  rw [s102_rew, withDensity_apply _ hS, ← lintegral_indicator hS]
  refine lintegral_congr fun ω => ?_
  by_cases h : ω ∈ S <;> simp [h]

theorem s102_rew_prob : IsProbabilityMeasure (s102_rew P X0 φ) := by
  refine ⟨?_⟩
  rw [s102_rew_apply P X0 hX0 Q φ hφ hpos hfin hlaw MeasurableSet.univ]
  have := s102_rew_lintegral P X0 hX0 Q φ hφ hpos hfin hlaw (f := fun _ => 1) measurable_const
  simpa using this

theorem s102_rew_inter {β : Type*} [MeasurableSpace β] (Y : Ω → β) (hY : Measurable Y) (hind : IndepFun X0 Y P)
    {A : Set E} {B : Set β} (hA : MeasurableSet A) (hB : MeasurableSet B) :
    s102_rew P X0 φ (X0 ⁻¹' A ∩ Y ⁻¹' B) = Q A * P (Y ⁻¹' B) := by
  rw [s102_rew_apply P X0 hX0 Q φ hφ hpos hfin hlaw ((hX0 hA).inter (hY hB))]
  have hfA : Measurable (A.indicator (fun x => (φ x)⁻¹)) := (hφ.inv).indicator hA
  have hgB : Measurable (B.indicator (1 : β → ℝ≥0∞)) := measurable_one.indicator hB
  have hind' : IndepFun (fun ω => A.indicator (fun x => (φ x)⁻¹) (X0 ω)) (fun ω => B.indicator (1 : β → ℝ≥0∞) (Y ω)) P :=
    hind.comp hfA hgB
  have h1 := lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun (μ := P) (hfA.comp hX0) (hgB.comp hY) hind'
  have e1 : ∀ ω, (X0 ⁻¹' A ∩ Y ⁻¹' B).indicator (1 : Ω → ℝ≥0∞) ω * (φ (X0 ω))⁻¹ =
      (A.indicator (fun x => (φ x)⁻¹) ∘ X0 * (B.indicator (1 : β → ℝ≥0∞)) ∘ Y) ω := by
    intro ω
    by_cases ha : X0 ω ∈ A <;> by_cases hb : Y ω ∈ B <;> simp [ha, hb, Set.indicator]
  simp_rw [e1]
  rw [h1]
  have e2 : ∫⁻ ω, (A.indicator (fun x => (φ x)⁻¹) ∘ X0) ω ∂P = Q A := by
    have := s102_rew_lintegral P X0 hX0 Q φ hφ hpos hfin hlaw (f := A.indicator 1) (measurable_one.indicator hA)
    have e3 : ∀ ω, (A.indicator (fun x => (φ x)⁻¹) ∘ X0) ω = A.indicator 1 (X0 ω) * (φ (X0 ω))⁻¹ := by
      intro ω
      by_cases ha : X0 ω ∈ A <;> simp [ha, Set.indicator]
    simp_rw [e3]
    rw [this, lintegral_indicator_one hA]
  have e4 : ∫⁻ ω, (B.indicator (1 : β → ℝ≥0∞) ∘ Y) ω ∂P = P (Y ⁻¹' B) := by
    have : (B.indicator (1 : β → ℝ≥0∞) ∘ Y) = (Y ⁻¹' B).indicator 1 := by
      funext ω; by_cases hb : Y ω ∈ B <;> simp [hb, Set.indicator]
    rw [this, lintegral_indicator_one (hY hB)]
  rw [e2, e4]

theorem s102_rew_map : (s102_rew P X0 φ).map X0 = Q := by
  ext A hA
  rw [Measure.map_apply hX0 hA, s102_rew_apply P X0 hX0 Q φ hφ hpos hfin hlaw (hX0 hA)]
  have := s102_rew_lintegral P X0 hX0 Q φ hφ hpos hfin hlaw (f := A.indicator 1) (measurable_one.indicator hA)
  rw [lintegral_indicator_one hA] at this
  rw [← this]
  refine lintegral_congr fun ω => ?_
  by_cases h : X0 ω ∈ A <;> simp [h, Set.indicator]

/-- Independence and the law of a random variable independent of `X₀` are unchanged. -/
theorem s102_rew_indep {β : Type*} [MeasurableSpace β] (Y : Ω → β) (hY : Measurable Y) (hind : IndepFun X0 Y P) :
    (s102_rew P X0 φ).map Y = P.map Y ∧ IndepFun X0 Y (s102_rew P X0 φ) := by
  haveI := s102_rew_prob P X0 hX0 Q φ hφ hpos hfin hlaw
  have hmap : (s102_rew P X0 φ).map Y = P.map Y := by
    ext B hB
    rw [Measure.map_apply hY hB, Measure.map_apply hY hB]
    have := s102_rew_inter P X0 hX0 Q φ hφ hpos hfin hlaw Y hY hind MeasurableSet.univ hB
    simpa using this
  refine ⟨hmap, ?_⟩
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro A B hA hB
  rw [s102_rew_inter P X0 hX0 Q φ hφ hpos hfin hlaw Y hY hind hA hB]
  have h2 := s102_rew_map P X0 hX0 Q φ hφ hpos hfin hlaw
  have h3 : s102_rew P X0 φ (X0 ⁻¹' A) = Q A := by
    rw [← h2, Measure.map_apply hX0 hA]
  have h4 : s102_rew P X0 φ (Y ⁻¹' B) = P (Y ⁻¹' B) := by
    have := congrArg (fun μ => μ B) hmap
    simpa [Measure.map_apply hY hB] using this
  rw [h3, h4]

end Reweight

end HRS.MS.R2Interp

end
