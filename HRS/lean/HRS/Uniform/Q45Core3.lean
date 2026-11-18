import HRS.Uniform.Q45Core2

/-!
# Q45: the Riemann-sum limit `κ → ∞` of the test-function expectations
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

open HRS HRS.LindebergAux

variable {H E : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]

theorem core_close {T : ℝ} (hT : 0 < T) {g : ℕ} (hg : 1 ≤ g) {d : ℕ} (b : Fin d → E)
    (hb : Orthonormal ℝ b) (S : EvolData H E) {ℱ : Filtration ℝ mΩ} {M : ℝ → Ω → H}
    {Sg : ℝ → Ω → (H →L[ℝ] H →L[ℝ] ℝ)} (hM : IsHilbertMartingaleWithCovariation P ℱ T M Sg)
    (X₀ : Ω → H) (hX : Measurable[ℱ 0] X₀) (Z : ℝ → Ω → E)
    (hZ : ∀ t ∈ Set.Icc (0 : ℝ) T, IsStochConv P S.VE S.j M 0 t (Z t))
    (hZm : ∀ t ∈ Set.Icc (0 : ℝ) T, Measurable (Z t))
    {Φ : PathSp T E → ℝ} (hΦ : Φ ∈ CbUnitBall (PathSp T E) 2) {η : ℝ} (hη : 0 < η) :
    ∃ κ0 : ℕ, ∀ κ ≥ κ0, 1 ≤ κ →
      |∫ ω, Φ (hatPath T g (fun i => projB b (S.VE (unifPart T g i) 0 (S.j (X₀ ω)) +
          Z (unifPart T g i) ω))) ∂P -
        ∫ ω, Φ (hatPath T g (fun i => projB b (S.VE (unifPart T g i) 0 (S.j (X₀ ω)) +
          rsum S T g κ M i ω))) ∂P| ≤ (g + 1) * η := by
  obtain ⟨κ0, hκ0⟩ := rsum_L1_close hT hg P S M Z hZ hη
  refine ⟨κ0, fun κ hκ hκ1 => ?_⟩
  have hX' : Measurable X₀ := hX.mono (ℱ.le 0) le_rfl
  have hmemT : ∀ i : Fin (g + 1), unifPart T g i ∈ Set.Icc (0 : ℝ) T := fun i =>
    ⟨unifPart_nonneg hT.le _ _, gridT_le hT hg i⟩
  have hBm : Measurable fun ω => hatPath T g (fun i => projB b (S.VE (unifPart T g i) 0 (S.j (X₀ ω)) +
      Z (unifPart T g i) ω)) := by
    have : Measurable fun ω => (fun i : Fin (g + 1) =>
        projB b (S.VE (unifPart T g i) 0 (S.j (X₀ ω)) + Z (unifPart T g i) ω)) :=
      measurable_pi_iff.2 fun i =>
        (continuous_projB b).measurable.comp
          ((((S.VE _ 0).continuous.comp S.j.continuous).measurable.comp hX').add (hZm _ (hmemT i)))
    exact (continuous_hatPath hT hg).measurable.comp this
  have hAm := aemeasurable_gridPath P hT hg hκ1 b S hM X₀ hX'
  have hpt : ∀ ω, ‖hatPath T g (fun i => projB b (S.VE (unifPart T g i) 0 (S.j (X₀ ω)) +
        Z (unifPart T g i) ω)) -
      hatPath T g (fun i => projB b (S.VE (unifPart T g i) 0 (S.j (X₀ ω)) +
        rsum S T g κ M i ω))‖ₑ ≤
      ∑ i : Fin (g + 1), ‖Z (unifPart T g i) ω - rsum S T g κ M i ω‖ₑ := by
    intro ω
    have := grid_path_diff_le hT hg b hb (fun i => S.VE (unifPart T g i) 0 (S.j (X₀ ω)))
      (fun i => Z (unifPart T g i) ω) (fun i => rsum S T g κ M i ω)
    have e : ∑ i : Fin (g + 1), ‖Z (unifPart T g i) ω - rsum S T g κ M i ω‖ₑ =
        ENNReal.ofReal (∑ i : Fin (g + 1), ‖Z (unifPart T g i) ω - rsum S T g κ M i ω‖) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => norm_nonneg _)]
      exact Finset.sum_congr rfl fun i _ => (ofReal_norm _).symm
    rw [← ofReal_norm, e]
    exact ENNReal.ofReal_le_ofReal this
  have hZmeas : ∀ i : Fin (g + 1), AEMeasurable (fun ω => ‖Z (unifPart T g i) ω -
      rsum S T g κ M i ω‖ₑ) P := fun i =>
    ((hZm _ (hmemT i)).aemeasurable.sub (aemeasurable_rsum P hT hg hκ1 S hM i)).enorm
  have hint : ∫⁻ ω, ‖hatPath T g (fun i => projB b (S.VE (unifPart T g i) 0 (S.j (X₀ ω)) +
        Z (unifPart T g i) ω)) -
      hatPath T g (fun i => projB b (S.VE (unifPart T g i) 0 (S.j (X₀ ω)) +
        rsum S T g κ M i ω))‖ₑ ∂P ≤ ((g + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal η := by
    calc _ ≤ ∫⁻ ω, ∑ i : Fin (g + 1), ‖Z (unifPart T g i) ω - rsum S T g κ M i ω‖ₑ ∂P :=
          lintegral_mono hpt
      _ = ∑ i : Fin (g + 1), ∫⁻ ω, ‖Z (unifPart T g i) ω - rsum S T g κ M i ω‖ₑ ∂P :=
          lintegral_finset_sum' _ fun i _ => hZmeas i
      _ ≤ ∑ i : Fin (g + 1), ENNReal.ofReal η :=
          Finset.sum_le_sum fun i _ => hκ0 κ hκ hκ1 i
      _ = ((g + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal η := by
          simp [Finset.sum_const, nsmul_eq_mul]
  have hfin : ((g + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal η ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) ENNReal.ofReal_ne_top
  have key := cb_integral_diff_le P hΦ hBm.aemeasurable hAm (ne_top_of_le_ne_top hfin hint)
  refine key.trans ?_
  calc (∫⁻ ω, _ ∂P).toReal ≤ (((g + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal η).toReal :=
        ENNReal.toReal_mono hfin hint
    _ = (g + 1) * η := by
        rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal hη.le]
        push_cast; ring

end HRS.Uniform.Q45
