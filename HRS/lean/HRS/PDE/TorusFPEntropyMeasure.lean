import HRS.PDE.TorusFPEntropyMeasureAux6

/-!
# D3-b: the measure layer of the free-energy inequality (proofs of the D3-b specifications)

Relocated proofs of the frozen specifications `HRS.d3_tilted_inequality`, `HRS.d3_entropy_moving`
(`HRS/PDE/TorusFPEntropySpec.lean`) and `HRS.d1_fp_entropy` (`HRS/PDE/TorusFPSpec.lean`); the statements
there are unchanged and keep their `sorry`.  Each theorem below is tied to its specification by
`example := (@..._proof : type_of% @...)`.  Helpers: `TorusFPEntropyMeasureAux1`-`Aux6`, names `d3b_*`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS

variable {n : ℕ}

theorem d3_tilted_inequality_proof (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ}
    (hU : Torus.IsSmooth U)
    {T : ℝ} (hT : 0 < T) {μ : ℝ → Measure (Torus n)}
    (hμ : D1WeakSolution κ (d1_gradDrift U) T μ) [IsProbabilityMeasure (μ 0)]
    (hfin : relEntropy (μ 0) (d1_gibbsMeasure κ U) ≠ ⊤)
    {ψ ψt : ℝ → Torus n → ℝ} (hψ : IsC12Test T ψ ψt) :
    ∀ t ∈ Set.Icc 0 T,
      relEntropy (μ t) (d1_gibbsMeasure κ U) ≠ ⊤ ∧
      ∫⁻ r in Set.Icc 0 t, d1_fisherInfo κ (d3_tiltPot κ U (ψ r)) (μ r) < ⊤ ∧
      ((relEntropy (μ t) (d1_gibbsMeasure κ U)).toReal - ∫ x, ψ t x ∂(μ t))
        + κ * (∫⁻ r in Set.Icc 0 t, d1_fisherInfo κ (d3_tiltPot κ U (ψ r)) (μ r)).toReal
      ≤ ((relEntropy (μ 0) (d1_gibbsMeasure κ U)).toReal - ∫ x, ψ 0 x ∂(μ 0))
        + ∫ r in Set.Icc 0 t, ∫ x, d3_source κ U ψ ψt r x ∂(μ r) :=
  d3b_tilted_main hn hκ hU hT hμ hfin hψ

example := (@d3_tilted_inequality_proof : type_of% @d3_tilted_inequality)

theorem d3_entropy_moving_proof (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ}
    (hU : Torus.IsSmooth U)
    {T : ℝ} (hT : 0 < T) {μ : ℝ → Measure (Torus n)}
    (hμ : D1WeakSolution κ (d1_gradDrift U) T μ) [IsProbabilityMeasure (μ 0)]
    {ψ ψt : ℝ → Torus n → ℝ} (hψ : IsC12Test T ψ ψt)
    (hfin : relEntropy (μ 0) (d1_gibbsMeasure κ (d3_tiltPot κ U (ψ 0))) ≠ ⊤) :
    ∀ t ∈ Set.Icc 0 T,
      relEntropy (μ t) (d1_gibbsMeasure κ (d3_tiltPot κ U (ψ t))) ≠ ⊤ ∧
      ∫⁻ r in Set.Icc 0 t, d1_fisherInfo κ (d3_tiltPot κ U (ψ r)) (μ r) < ⊤ ∧
      (relEntropy (μ t) (d1_gibbsMeasure κ (d3_tiltPot κ U (ψ t)))).toReal
        + κ * (∫⁻ r in Set.Icc 0 t, d1_fisherInfo κ (d3_tiltPot κ U (ψ r)) (μ r)).toReal
      ≤ (relEntropy (μ 0) (d1_gibbsMeasure κ (d3_tiltPot κ U (ψ 0)))).toReal
        + ∫ r in Set.Icc 0 t, ∫ x, (d3_source κ U ψ ψt r x
            + ∫ y, ψt r y ∂(d1_gibbsMeasure κ (d3_tiltPot κ U (ψ r)))) ∂(μ r) :=
  d3b_moving_main hn hκ hU hT hμ hψ hfin

example := (@d3_entropy_moving_proof : type_of% @d3_entropy_moving)

/-- `d1_fp_entropy`, as the `ψ = 0` case of `d3_entropy_moving_proof` (the proof of
`d3_fp_entropy_of_moving` with the proved moving-reference inequality). -/
theorem d1_fp_entropy_proof (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ}
    (hU : Torus.IsSmooth U)
    {T : ℝ} (hT : 0 < T) {μ : ℝ → Measure (Torus n)}
    (hμ : D1WeakSolution κ (d1_gradDrift U) T μ) [IsProbabilityMeasure (μ 0)]
    (hfin : relEntropy (μ 0) (d1_gibbsMeasure κ U) < ⊤) :
    ∀ t ∈ Set.Icc 0 T,
      relEntropy (μ t) (d1_gibbsMeasure κ U) +
        ENNReal.ofReal κ * ∫⁻ r in Set.Icc 0 t, d1_fisherInfo κ U (μ r)
      ≤ relEntropy (μ 0) (d1_gibbsMeasure κ U) := by
  intro t ht
  have hC : IsC12Test T (fun _ : ℝ => fun _ : Torus n => (0 : ℝ)) (fun _ _ => 0) :=
    d1_isC12Test_const ((show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Torus.lift (fun _ : Torus n => (0 : ℝ))) from d1_isSmooth_const 0).of_le (by norm_num))
  have hf0 : relEntropy (μ 0) (d1_gibbsMeasure κ (d3_tiltPot κ U (fun _ : Torus n => (0 : ℝ)))) ≠ ⊤ := by
    rw [d3_tiltPot_zero]; exact hfin.ne
  obtain ⟨h1, h2, h3⟩ := d3_entropy_moving_proof hn hκ hU hT hμ hC hf0 t ht
  simp only [d3_tiltPot_zero, d3_source_zero, integral_zero, add_zero] at h1 h2 h3
  have hA : relEntropy (μ 0) (d1_gibbsMeasure κ U) ≠ ⊤ := hfin.ne
  have hlhs : relEntropy (μ t) (d1_gibbsMeasure κ U) +
      ENNReal.ofReal κ * ∫⁻ r in Set.Icc 0 t, d1_fisherInfo κ U (μ r) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨h1, ENNReal.mul_ne_top ENNReal.ofReal_ne_top h2.ne⟩
  rw [← ENNReal.toReal_le_toReal hlhs hA, ENNReal.toReal_add h1 (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h2.ne),
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hκ.le]
  simpa using h3

example := (@d1_fp_entropy_proof : type_of% @d1_fp_entropy)

end HRS
