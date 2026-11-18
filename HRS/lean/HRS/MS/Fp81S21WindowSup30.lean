import HRS.MS.Fp81S21WindowSup29

/-! Product integrability needed to center a frozen-source FTC. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace HRS.Fp81.S21

/-- A jointly measurable family with uniformly bounded sixth moments on a
finite time-measure space is integrable on the product. -/
theorem fp81s21_sixth_slices_product_integrable
    {S Ω : Type*} [MeasurableSpace S] [MeasurableSpace Ω]
    (ν : Measure S) [IsFiniteMeasure ν]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : S × Ω → ℝ) (hF : Measurable F) (M : ℝ)
    (hM : 0 ≤ M) (hSix : ∀ s, SixthBound P (fun ω => F (s, ω)) M) :
    Integrable F (ν.prod P) := by
  let G : S × Ω → ℝ := fun z => ‖F z‖ ^ 6
  have hG : Measurable G := hF.norm.pow_const 6
  have hSec : ∀ᵐ s ∂ν, Integrable (fun ω => G (s, ω)) P :=
    Filter.Eventually.of_forall fun s => (hSix s).1
  have hRowMeas : Measurable (fun s => ∫ ω, G (s, ω) ∂P) :=
    (hG.stronglyMeasurable.integral_prod_right' (ν := P)).measurable
  have hRowInt : Integrable (fun s => ∫ ω, ‖G (s, ω)‖ ∂P) ν := by
    have heq : (fun s => ∫ ω, ‖G (s, ω)‖ ∂P) =
        (fun s => ∫ ω, G (s, ω) ∂P) := by
      funext s
      congr 1
      funext ω
      exact Real.norm_of_nonneg (by dsimp [G]; positivity)
    rw [heq]
    apply Integrable.of_bound hRowMeas.aestronglyMeasurable M
    filter_upwards [] with s
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun ω => by dsimp [G]; positivity))]
    exact (hSix s).2
  have hGInt : Integrable G (ν.prod P) :=
    (integrable_prod_iff hG.aestronglyMeasurable).2 ⟨hSec, hRowInt⟩
  have hMem : MemLp F (ENNReal.ofReal 6) (ν.prod P) := by
    apply (integrable_norm_rpow_iff hF.aestronglyMeasurable
      (by norm_num) (by norm_num)).1
    simpa [G, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 6)] using hGInt
  exact hMem.integrable (by norm_num)

#print axioms fp81s21_sixth_slices_product_integrable
end HRS.Fp81.S21
end
