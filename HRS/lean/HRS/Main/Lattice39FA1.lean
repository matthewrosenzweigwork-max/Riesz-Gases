import HRS.Main.Lattice39FinalSpec

/-!
# Example A.39 final form: D2 (field moments of the perturbed lattice), relocated proof
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory BoundedContinuousFunction

namespace HRS

namespace Main

variable {d : ℕ}

theorem lat39fa_gamma_gt (d : ℕ) : (d : ℝ) / 2 + 2 < (gammaIdx d : ℝ) := by
  have h : (3 : ℕ) ≤ PDE.mStar d := by
    unfold PDE.mStar; omega
  unfold gammaIdx
  push_cast
  have : (3 : ℝ) ≤ (PDE.mStar d : ℝ) := by exact_mod_cast h
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  linarith

theorem lat39fa_isCk1 {a : Torus d → Euc d} (ha : Torus.IsSmooth a) : Torus.IsCk 1 a :=
  ContDiff.of_le (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift a) from ha)
    (by exact_mod_cast (le_top : ((1 : ℕ) : ℕ∞) ≤ ⊤))

/-- D2 relocated. -/
theorem lattice39f_field_moments_proof (hd : 1 ≤ d) (a : Torus d → Euc d) (ha : Torus.IsSmooth a) :
    ∃ Cf : ℝ, 0 ≤ Cf ∧ ∀ (n : ℕ), 1 ≤ n → ∀ κ : ℝ, 0 < κ →
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X₀ : Ω → Config d (n ^ d)), (∀ᵐ ω ∂P, X₀ ω = perturbedLattice n κ a) →
      ∫⁻ ω, ‖κ • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ) (empirical (X₀ ω)) volume -
          lattice39fEta a‖ₑ ∂P ≤
        ENNReal.ofReal (Cf * (κ⁻¹ + κ * ((n ^ d : ℕ) : ℝ) ^ (-(2 : ℝ) / (d : ℝ)))) ∧
      ∫⁻ ω, ‖κ • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ) (empirical (X₀ ω)) volume‖ₑ ^ 2 ∂P +
        ∫⁻ _ω, ‖lattice39fEta a‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal ((‖lattice39fEta a‖ +
          Cf * (κ⁻¹ + κ * ((n ^ d : ℕ) : ℝ) ^ (-(2 : ℝ) / (d : ℝ)))) ^ 2 + ‖lattice39fEta a‖ ^ 2) := by
  obtain ⟨C, hC⟩ := perturbedLattice_field hd (gammaIdx d : ℝ) (lat39fa_gamma_gt d)
  have hca : Torus.IsCk 1 a := lat39fa_isCk1 ha
  set B : ℝ := Torus.cbNorm 1 a ^ 2 with hB
  refine ⟨|C| * max 1 B, by positivity, ?_⟩
  intro n hn κ hκ Ω _ P _ X₀ hX
  set L : ℝ := ((n ^ d : ℕ) : ℝ) ^ (-(2 : ℝ) / (d : ℝ)) with hL
  have hL0 : 0 ≤ L := Real.rpow_nonneg (Nat.cast_nonneg _) _
  set E : ℝ := |C| * max 1 B * (κ⁻¹ + κ * L) with hE
  have hE0 : 0 ≤ E := by positivity
  set A : ℝ := ‖κ • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ) (empirical (perturbedLattice n κ a))
    volume - lattice39fEta a‖ with hA
  have hAE : A ≤ E := by
    have h1 := hC n hn κ hκ a hca
    refine h1.trans ?_
    have hB0 : 0 ≤ B := by positivity
    have hκi : 0 ≤ κ⁻¹ := by positivity
    calc C * (κ⁻¹ * Torus.cbNorm 1 a ^ 2 + κ * L)
        ≤ |C| * (κ⁻¹ * Torus.cbNorm 1 a ^ 2 + κ * L) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
      _ ≤ |C| * (max 1 B * (κ⁻¹ + κ * L)) := by
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg C)
          have : κ⁻¹ * B ≤ κ⁻¹ * max 1 B := mul_le_mul_of_nonneg_left (le_max_right _ _) hκi
          have h2 : κ * L ≤ max 1 B * (κ * L) :=
            le_mul_of_one_le_left (by positivity) (le_max_left _ _)
          nlinarith
      _ = E := by rw [hE]; ring
  have hQ : ∀ᵐ ω ∂P, ‖κ • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ) (empirical (X₀ ω)) volume -
      lattice39fEta a‖ₑ = ENNReal.ofReal A := by
    filter_upwards [hX] with ω hω
    rw [hω, hA, ofReal_norm_eq_enorm]
  have hQ2 : ∀ᵐ ω ∂P, ‖κ • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ) (empirical (X₀ ω)) volume‖ₑ =
      ENNReal.ofReal ‖κ • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ)
        (empirical (perturbedLattice n κ a)) volume‖ := by
    filter_upwards [hX] with ω hω
    rw [hω, ofReal_norm_eq_enorm]
  refine ⟨?_, ?_⟩
  · rw [lintegral_congr_ae hQ, lintegral_const, measure_univ, mul_one]
    exact ENNReal.ofReal_le_ofReal hAE
  · set Z := ‖κ • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ)
        (empirical (perturbedLattice n κ a)) volume‖ with hZ
    set H : ℝ := ‖lattice39fEta a‖ with hH
    have hZle : Z ≤ H + E := by
      have : Z ≤ ‖κ • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ)
          (empirical (perturbedLattice n κ a)) volume - lattice39fEta a‖ + ‖lattice39fEta a‖ := by
        simpa using norm_add_le (κ • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ)
          (empirical (perturbedLattice n κ a)) volume - lattice39fEta a) (lattice39fEta a)
      linarith
    have hZ0 : 0 ≤ Z := norm_nonneg _
    have hH0 : 0 ≤ H := norm_nonneg _
    rw [lintegral_congr_ae (hQ2.mono fun ω h => by rw [h]), lintegral_const, measure_univ,
      mul_one, lintegral_const, measure_univ, mul_one]
    rw [← ofReal_norm_eq_enorm (lattice39fEta a), ← hH, ← ENNReal.ofReal_pow hZ0,
      ← ENNReal.ofReal_pow hH0, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have : Z ^ 2 ≤ (H + E) ^ 2 := pow_le_pow_left₀ hZ0 hZle 2
    linarith
example := (@lattice39f_field_moments_proof : type_of% @lattice39f_field_moments)

end Main

end HRS
