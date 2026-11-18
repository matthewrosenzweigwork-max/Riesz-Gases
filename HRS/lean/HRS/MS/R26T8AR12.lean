import HRS.MS.S82P2Mom

/-!
# S8.2 observed-time layer, packet T8A.R12 (with measurability): transfer of single-site updates to a.e.-equal representatives

Packet statement defect: the contract has no measurability hypothesis on the update kernel `K`.  Without it the conclusion
does not follow from `hinv`, because `hinv` only says the lower integral `∫⁻ X, φ X ∂P` of
`φ X = K i X {y | update X i y ∈ B}` vanishes, which for a non-measurable `φ` does not force `φ = 0` a.e.
The corrected statement `r26t8a_update_ae_transfer_meas` assumes `K i` measurable into `Measure (Euc d)` with probability values
(the heat-bath laws), i.e. `K i` is a Markov kernel.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal
namespace HRS.MS.R26T8A
open HRS HRS.Whole

theorem r26t8a_update_ae_transfer_meas {d n : ℕ} (P : Measure (EucConfig d n))
    (K : Fin n → EucConfig d n → Measure (Euc d)) (hK : ∀ i, Measurable (K i))
    [hprob : ∀ i X, IsProbabilityMeasure (K i X)]
    (hinv : ∀ i, ∀ F : EucConfig d n → ℝ≥0∞, Measurable F →
      ∫⁻ X, ∫⁻ y, F (Function.update X i y) ∂K i X ∂P = ∫⁻ X, F X ∂P)
    (F G : EucConfig d n → ℝ) (heq : F =ᵐ[P] G) :
    ∀ i, ∀ᵐ X ∂P, ∀ᵐ y ∂K i X,
      F (Function.update X i y) - F X = G (Function.update X i y) - G X := by
  intro i
  obtain ⟨B, hBsub, hBm, hB0⟩ := exists_measurable_superset_of_null (μ := P)
    (s := {X | ¬ F X = G X}) (ae_iff.1 heq)
  let κ : ProbabilityTheory.Kernel (EucConfig d n) (Euc d) := ⟨K i, hK i⟩
  haveI : ProbabilityTheory.IsMarkovKernel κ := ⟨fun X => hprob i X⟩
  have hupd : Measurable fun p : EucConfig d n × Euc d => Function.update p.1 i p.2 :=
    measurable_update' (a := i)
  have hφ : Measurable fun X : EucConfig d n => K i X {y | Function.update X i y ∈ B} :=
    ProbabilityTheory.Kernel.measurable_kernel_prodMk_left (κ := κ) (hupd hBm)
  have hupd1 : ∀ X : EucConfig d n, Measurable fun y : Euc d => Function.update X i y := fun X =>
    hupd.comp (measurable_const.prodMk measurable_id)
  have h0 : ∫⁻ X, K i X {y | Function.update X i y ∈ B} ∂P = 0 := by
    have := hinv i (B.indicator 1) (measurable_one.indicator hBm)
    have e1 : ∀ X, ∫⁻ y, B.indicator (1 : EucConfig d n → ℝ≥0∞) (Function.update X i y) ∂K i X =
        K i X {y | Function.update X i y ∈ B} := fun X => by
      have : (fun y => B.indicator (1 : EucConfig d n → ℝ≥0∞) (Function.update X i y)) =
          {y | Function.update X i y ∈ B}.indicator (fun _ => (1 : ℝ≥0∞)) := by
        funext y; by_cases h : Function.update X i y ∈ B <;> simp [h]
      rw [this]
      have h2 := lintegral_indicator_const (μ := K i X) (hupd1 X hBm) (1 : ℝ≥0∞)
      rw [one_mul] at h2
      exact h2
    simp_rw [e1] at this
    rw [this, show ∫⁻ X, B.indicator (1 : EucConfig d n → ℝ≥0∞) X ∂P = P B by
      have : B.indicator (1 : EucConfig d n → ℝ≥0∞) = B.indicator (fun _ => (1 : ℝ≥0∞)) := rfl
      rw [this, lintegral_indicator_const hBm, one_mul], hB0]
  have hz : (fun X => K i X {y | Function.update X i y ∈ B}) =ᵐ[P] 0 :=
    (lintegral_eq_zero_iff hφ).1 h0
  have hXB : ∀ᵐ X ∂P, X ∉ B := measure_eq_zero_iff_ae_notMem.1 hB0
  filter_upwards [hz, hXB] with X hX hXn
  have hy : ∀ᵐ y ∂K i X, Function.update X i y ∉ B :=
    measure_eq_zero_iff_ae_notMem.1 hX
  have hXFG : F X = G X := by
    by_contra h; exact hXn (hBsub h)
  filter_upwards [hy] with y hyn
  have hyFG : F (Function.update X i y) = G (Function.update X i y) := by
    by_contra h; exact hyn (hBsub h)
  rw [hyFG, hXFG]

end HRS.MS.R26T8A
