import HRS.MC.S7PIF5C

/-!
# Packet piF5, part D: the diffusion integrand `Φc` is progressive and pathwise locally square integrable

`Φc s ω k i = √N · empiricalNoiseIntegrand (t i) (U^{·,t_i} φ_i) X s ω k`.  Each coordinate is progressive and `L²`
(`S7PIF4_prog_zero`, `S7PIF4_prog_pos`); the Euclidean norm squared is the sum of the coordinate squares.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIF5

open HRS HRS.PDE HRS.A33 HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIF4 HRS.MC.Sec7.S7PIM

variable {d : ℕ}

theorem S7PIF5_enorm_sq {q : ℕ} (v : EuclideanSpace ℝ (Fin q)) : ‖v‖ₑ ^ 2 = ∑ i, ‖v i‖ₑ ^ 2 := by
  have h1 : ‖v‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 := EuclideanSpace.norm_sq_eq v
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), h1,
    ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]

/-- local square integrability of a Euclidean combination of locally square integrable integrands -/
theorem S7PIF5_sq_euclid {Ω : Type} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
    {ι : Type*} [Fintype ι] {q : ℕ} (Ψ : Fin q → ℝ → Ω → ι → ℝ) (c : ℝ)
    (hΨ : ∀ i, IsProgressiveLocL2 P ℱ (Ψ i)) (T' : ℝ) :
    ∀ᵐ ω ∂P, ∫⁻ s in Set.Icc 0 T', ∑ k, ‖(WithLp.toLp 2 (fun i => c * Ψ i s ω k) : EuclideanSpace ℝ (Fin q))‖ₑ ^ 2 < ∞ := by
  filter_upwards [ae_all_iff.2 fun i => (hΨ i).sq T'] with ω hω
  have hpt : ∀ s, ∑ k, ‖(WithLp.toLp 2 (fun i => c * Ψ i s ω k) : EuclideanSpace ℝ (Fin q))‖ₑ ^ 2 =
      ∑ i, ‖c‖ₑ ^ 2 * ∑ k, ‖Ψ i s ω k‖ₑ ^ 2 := by
    intro s
    simp_rw [S7PIF5_enorm_sq]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    show ‖c * Ψ i s ω k‖ₑ ^ 2 = _
    rw [enorm_mul, mul_pow]
  simp_rw [hpt]
  have hmeas : ∀ i, AEMeasurable (fun s => ‖c‖ₑ ^ 2 * ∑ k, ‖Ψ i s ω k‖ₑ ^ 2) (volume.restrict (Set.Icc 0 T')) := by
    intro i
    have h := S7PIF5_sec_aemeas (hΨ i).prog ω T'
    have : Measurable fun v : ι → ℝ => ‖c‖ₑ ^ 2 * ∑ k, ‖v k‖ₑ ^ 2 :=
      (Finset.measurable_sum _ fun k _ => (((measurable_pi_apply k).enorm).pow_const 2)).const_mul _
    exact this.comp_aemeasurable h
  rw [lintegral_finset_sum' _ fun i _ => hmeas i]
  refine ENNReal.sum_lt_top.2 fun i _ => ?_
  rw [lintegral_const_mul' _ _ (by simp)]
  exact ENNReal.mul_lt_top (by simp) (hω i)

section Prob

variable (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) (N : ℕ) (hN : 1 ≤ N)
  {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
  (hreal : PreparedRealization R.D P
    (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) X₀ W X)

include hm hT hN hreal

/-- each coordinate noise integrand is progressive and `L²` for an observation time in `[0,T]` -/
theorem S7PIF5_eni_L2 {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution P ℱ W' W X) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) T) {ψ : Torus d → ℝ}
    (hψ : Torus.IsSmooth ψ) :
    IsProgressiveL2 P ℱ (empiricalNoiseIntegrand R.D τ (fun r => propagator R.D R.ρ r τ ψ) X) := by
  rcases hτ.1.eq_or_lt with h0 | hpos
  · rw [← h0]; exact S7PIF4_prog_zero R m hm T hT N hN P X₀ W X hreal hF hψ
  · exact S7PIF4_prog_pos R m hm T hT N hN P X₀ W X hreal hF hψ ⟨hpos, hτ.2⟩

end Prob

/-- the diffusion integrand of the observation vector -/
def S7PIF5_Phi (R : Regime d) {N : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → Config d N) {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ) :
    ℝ → Ω → (Fin N × Fin d) → EuclideanSpace ℝ (Fin q) :=
  fun s ω k => WithLp.toLp 2 fun i => Real.sqrt N *
    empiricalNoiseIntegrand R.D (t i) (fun r => propagator R.D R.ρ r (t i) (φ i)) X s ω k

section Prob2

variable (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) (N : ℕ) (hN : 1 ≤ N)
  {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
  (hreal : PreparedRealization R.D P
    (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) X₀ W X)

include hm hT hN hreal

theorem S7PIF5_Phi_L2E {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution P ℱ W' W X) {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T) (hφ : ∀ i, Torus.IsSmooth (φ i)) :
    IsProgressiveLocL2E P ℱ (S7PIF5_Phi R X t φ) := by
  have hL := fun i => S7PIF5_eni_L2 R m hm T hT N hN P X₀ W X hreal hF (ht i) (hφ i)
  refine ⟨?_, fun T' => ?_⟩
  · intro s
    refine @measurable_pi_iff _ _ _ (Subtype.instMeasurableSpace.prod (ℱ s)) _ _ |>.2 fun k => ?_
    refine @Measurable.comp _ _ _ (Subtype.instMeasurableSpace.prod (ℱ s)) _ _ _ _
      (MeasurableEquiv.toLp 2 (Fin q → ℝ)).measurable
      (@measurable_pi_iff _ _ _ (Subtype.instMeasurableSpace.prod (ℱ s)) _ _ |>.2 fun i => ?_)
    have h := (hL i).prog s
    have h2 := (@measurable_pi_iff _ _ _ (Subtype.instMeasurableSpace.prod (ℱ s)) _ _ |>.1 h) k
    exact h2.const_mul _
  · exact S7PIF5_sq_euclid (P := P) (ℱ := ℱ) (fun i => empiricalNoiseIntegrand R.D (t i)
      (fun r => propagator R.D R.ρ r (t i) (φ i)) X) (Real.sqrt N) (fun i => (hL i).locL2) T'

end Prob2

end HRS.MC.Sec7.S7PIF5

end
