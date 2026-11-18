import HRS.MC.E214T1
import HRS.MC.E214P2
import HRS.MC.E214P3
import HRS.MC.E214P5
import HRS.MC.E213Q2
import HRS.Main.HeadlineEdgeworth

/-!
# E214T2: proof of `HRS.Main.two_parameter_expansion` (Corollary 2.14, two-parameter expansion)

Route: `hK.expansion` at the SAME `a` gives `E Φ(ζ) = E Φ(Z^a) + (6√N)⁻¹ E K_a(D³Φ(Z^a)) + O(ε_N/√N)`; the Hessian step
(`t1_hessian`) replaces `Z^a` by the stationary window up to `½ E Δ(D²Φ) + covDist²/8`; the cubic term is moved from `K_a`
to `Kst` by `hrel` (`p5_cubic_diff`) and from `Z^a` to the stationary window by first-order comparison (`p3_compare` for
the `C²` function `Kst ∘ D³Φ`) and `hcov` (`covDist ≤ C₁e^{-ca}`, same `c`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E214T

open HRS HRS.Main HRS.MC.E214P

variable {d : ℕ}

set_option maxHeartbeats 600000 in
theorem two_parameter_expansion_proof (S : PreparedData d) (β₀ m T : ℝ) (hE : EdgeworthHyp S β₀ m)
    (hT : 0 < T) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (K : ℝ → projTensor (PathSpace d m T) 3) (ε : ℕ → ℝ)
    (hK : IsWindowEdgeworth S β₀ m T K ε) (Kst : projTensor (PathSpace d m T) 3) (C₁ c : ℝ)
    (hC₁ : 0 < C₁) (hc : 0 < c)
    (hrel : ∀ a' : ℝ, 0 ≤ a' → ‖K a' - Kst‖ ≤ C₁ * Real.exp (-c * a'))
    (hcov : ∀ a' : ℝ, 0 ≤ a' → ∀ (ν : Measure (NegSobolev d m)),
        IsCenteredGaussianWithCov m ν (preparedCov d S.s β₀ S.μ0) →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z₀ : Ω' → NegSobolev d m) (Z : ℝ → Ω' → NegSobolev d m),
        IsPreparedLinear S m (a' + T) ν P' Z₀ Z →
      ∀ {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'')
        [IsProbabilityMeasure P''] (Zs : ℝ → Ω'' → NegSobolev d m),
        IsStationaryGaussianField P'' S.s S.β S.hs0 S.hsd S.hβ S.V ρβ m Zs →
        covDist P' P'' (windowPath m T a' Z) (windowPath m T 0 Zs) ≤ C₁ * Real.exp (-c * a')) :
    ∃ C : ℝ, 0 < C ∧
      ∀ a : ℝ, 0 ≤ a → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        SelectedFlow P S.dyn (a + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        law P X₀ = modulatedGibbs (periodicRiesz d S.s) N β₀ S.μ0 →
      ∀ (ν : Measure (NegSobolev d m)),
        IsCenteredGaussianWithCov m ν (preparedCov d S.s β₀ S.μ0) →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z₀ : Ω' → NegSobolev d m) (Z : ℝ → Ω' → NegSobolev d m),
        IsPreparedLinear S m (a + T) ν P' Z₀ Z →
      ∀ {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'')
        [IsProbabilityMeasure P''] (Zs : ℝ → Ω'' → NegSobolev d m),
        IsStationaryGaussianField P'' S.s S.β S.hs0 S.hsd S.hβ S.V ρβ m Zs →
      ∀ Φ : PathSpace d m T → ℝ, Φ ∈ CbUnitBall (PathSpace d m T) 5 →
        |∫ z, Φ z ∂(law P (windowZeta m T a P X)) - ∫ z, Φ z ∂(law P'' (windowPath m T 0 Zs)) -
            (1 / 2) * ∫ ω'', (∫ ω, (iteratedFDeriv ℝ 2 Φ (windowPath m T 0 Zs ω''))
                ![windowPath m T a Z ω, windowPath m T a Z ω] ∂P' -
              ∫ ω₂, (iteratedFDeriv ℝ 2 Φ (windowPath m T 0 Zs ω''))
                ![windowPath m T 0 Zs ω₂, windowPath m T 0 Zs ω₂] ∂P'') ∂P'' -
            (1 / (6 * Real.sqrt N)) * ∫ ω, ((Kst : projTensor (PathSpace d m T) 3) :
              TensorDual (PathSpace d m T) 3)
                (iteratedFDeriv ℝ 3 Φ (windowPath m T 0 Zs ω)) ∂P''| ≤
          C * (covDist P' P'' (windowPath m T a Z) (windowPath m T 0 Zs) ^ 2 +
            (Real.sqrt N)⁻¹ * (ε N + Real.exp (-c * a))) := by
  set Mb : ℝ := ‖Kst‖ with hMb
  have hMb0 : 0 ≤ Mb := norm_nonneg _
  refine ⟨1 + C₁ * (1 + Mb / 2) / 6, by positivity, ?_⟩
  intro a ha N hN Ω _ P _ X₀ W X hsel hfilt hinit ν hν Ω' _ P' _ Z₀ Z hZ Ω'' _ P'' _ Zs hZs Φ hΦ
  have hexp := hK.expansion a ha N hN P X₀ W X hsel hfilt hinit ν hν P' Z₀ Z hZ Φ hΦ
  obtain ⟨hZm, hZg⟩ := HRS.MC.E213Q.e213q_prepared_window_gaussian S m T a hT ha ν hν.1 P' Z₀ Z hZ
  obtain ⟨hZsm, hZsg⟩ := p2_stationary_window_gaussian S.hd S.hs0 S.hsd S.V S.hβ ρβ m T hT P'' Zs hZs
  have hΦc : Continuous Φ := hΦ.1.continuous
  -- Hessian step
  have hH := t1_hessian P'' (windowPath m T 0 Zs) P' (windowPath m T a Z) hZsm hZm hZsg hZg hΦ
  -- notation
  set δ : ℝ := covDist P' P'' (windowPath m T a Z) (windowPath m T 0 Zs) with hδ
  have hδ0 : 0 ≤ δ := p3_covDist_nonneg _ _ _ _
  have hδc : δ ≤ C₁ * Real.exp (-c * a) := hcov a ha ν hν P' Z₀ Z hZ P'' Zs hZs
  set Ca : ℝ := ∫ ω, ((K a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3)
    (iteratedFDeriv ℝ 3 Φ (windowPath m T a Z ω)) ∂P' with hCa
  set Ca' : ℝ := ∫ ω, ((Kst : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3)
    (iteratedFDeriv ℝ 3 Φ (windowPath m T a Z ω)) ∂P' with hCa'
  set Cst : ℝ := ∫ ω, ((Kst : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3)
    (iteratedFDeriv ℝ 3 Φ (windowPath m T 0 Zs ω)) ∂P'' with hCst
  have hstep3 : |Ca - Ca'| ≤ C₁ * Real.exp (-c * a) := by
    refine (p5_cubic_diff hZm hΦ _ _).trans ?_
    have : ‖((K a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3) -
        ((Kst : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3)‖ =
        ‖K a - Kst‖ := rfl
    rw [this]
    exact hrel _ ha
  have hstep4 : |Ca' - Cst| ≤ (1 / 2) * Mb * (C₁ * Real.exp (-c * a)) := by
    set L : TensorDual (PathSpace d m T) 3 := ((Kst : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3)
      with hL
    have hLn : ‖L‖ = Mb := rfl
    obtain ⟨b0, b1, b2⟩ := p4_bound hΦ L
    have hcmp := p3_compare P'' (windowPath m T 0 Zs) P' (windowPath m T a Z) hZsm hZm hZsg hZg
      (Θ := fun x => L (iteratedFDeriv ℝ 3 Φ x)) (p4_contDiff hΦ L) (M0 := ‖L‖) (M1 := ‖L‖) (K := ‖L‖)
      b0 b1 b2
    rw [hLn] at hcmp
    refine hcmp.trans ?_
    have := mul_le_mul_of_nonneg_left hδc hMb0
    linarith
  -- law = integral conversions
  rw [p5_law_integral hZsm hΦc]
  rw [p5_law_integral hZm hΦc] at hexp
  -- assembling
  set s : ℝ := Real.sqrt N with hs
  have hspos : 0 < s := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < N))
  set A : ℝ := ∫ z, Φ z ∂(law P (windowZeta m T a P X)) with hA
  set Bq : ℝ := ∫ ω, Φ (windowPath m T a Z ω) ∂P' with hB
  set B1 : ℝ := ∫ ω, Φ (windowPath m T 0 Zs ω) ∂P'' with hB1
  set Hq : ℝ := ∫ ω'', (∫ ω, (iteratedFDeriv ℝ 2 Φ (windowPath m T 0 Zs ω''))
                ![windowPath m T a Z ω, windowPath m T a Z ω] ∂P' -
              ∫ ω₂, (iteratedFDeriv ℝ 2 Φ (windowPath m T 0 Zs ω''))
                ![windowPath m T 0 Zs ω₂, windowPath m T 0 Zs ω₂] ∂P'') ∂P'' with hHq
  have hε0 : 0 ≤ ε N := (abs_nonneg _).trans hexp
  have e : A - B1 - (1 / 2) * Hq - (1 / (6 * s)) * Cst =
      (Bq - B1 - (1 / 2) * Hq) +
      ((s * (A - Bq) - (1 / 6) * Ca) + (1 / 6) * ((Ca - Ca') + (Ca' - Cst))) / s := by
    field_simp
    ring
  have hq : |((s * (A - Bq) - (1 / 6) * Ca) + (1 / 6) * ((Ca - Ca') + (Ca' - Cst))) / s| ≤
      (ε N + (1 / 6) * (C₁ * Real.exp (-c * a) + (1 / 2) * Mb * (C₁ * Real.exp (-c * a)))) / s := by
    rw [abs_div, abs_of_pos hspos]
    refine div_le_div_of_nonneg_right ?_ hspos.le
    calc |(s * (A - Bq) - (1 / 6) * Ca) + (1 / 6) * ((Ca - Ca') + (Ca' - Cst))|
        ≤ |s * (A - Bq) - (1 / 6) * Ca| + |(1 / 6) * ((Ca - Ca') + (Ca' - Cst))| := abs_add_le _ _
      _ ≤ _ := by
          refine add_le_add hexp ?_
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 6)]
          exact mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hstep3 hstep4)) (by norm_num)
  rw [e]
  have hex0 : 0 ≤ Real.exp (-c * a) := (Real.exp_pos _).le
  have hsinv : s⁻¹ * (C₁ * (1 + Mb / 2) / 6 * Real.exp (-c * a)) ≥ 0 := by positivity
  calc _ ≤ |Bq - B1 - (1 / 2) * Hq| + |((s * (A - Bq) - (1 / 6) * Ca) + (1 / 6) * ((Ca - Ca') + (Ca' - Cst))) / s| :=
        abs_add_le _ _
    _ ≤ δ ^ 2 / 8 + (ε N + (1 / 6) * (C₁ * Real.exp (-c * a) + (1 / 2) * Mb * (C₁ * Real.exp (-c * a)))) / s :=
        add_le_add hH hq
    _ ≤ _ := by
        have h1 : (ε N + (1 / 6) * (C₁ * Real.exp (-c * a) + (1 / 2) * Mb * (C₁ * Real.exp (-c * a)))) / s =
            s⁻¹ * ε N + s⁻¹ * (C₁ * (1 + Mb / 2) / 6 * Real.exp (-c * a)) := by
          field_simp
        have hsi : 0 ≤ s⁻¹ := inv_nonneg.2 hspos.le
        have hCC : 0 ≤ C₁ * (1 + Mb / 2) / 6 := by positivity
        have h2 : s⁻¹ * ε N ≤ (1 + C₁ * (1 + Mb / 2) / 6) * (s⁻¹ * ε N) := by
          nlinarith [mul_nonneg hsi hε0, mul_nonneg hCC (mul_nonneg hsi hε0)]
        have h3 : s⁻¹ * (C₁ * (1 + Mb / 2) / 6 * Real.exp (-c * a)) ≤
            (1 + C₁ * (1 + Mb / 2) / 6) * (s⁻¹ * Real.exp (-c * a)) := by
          nlinarith [mul_nonneg hsi hex0, mul_nonneg hCC (mul_nonneg hsi hex0)]
        have h4 : δ ^ 2 / 8 ≤ (1 + C₁ * (1 + Mb / 2) / 6) * δ ^ 2 := by
          nlinarith [sq_nonneg δ, mul_nonneg hCC (sq_nonneg δ)]
        rw [h1]
        nlinarith

end HRS.MC.E214T

end
