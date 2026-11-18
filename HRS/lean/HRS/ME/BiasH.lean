import HRS.ME.BiasG

/-!
# Chunk E, row 2.10 (fixed-`β` closure): `critical_bias_constants_fixed`

The three clauses of Proposition 2.10 (`M:H:prop:critical`, TeX L1081-1101, proof L5709-5750) for each fixed
`β > 0`, with the constants chosen after `β` and before `ρ_β`, `u`, `N`, the realization and `Z`.  The frozen
`HRS.Main.critical_bias_constants` chooses the constants before `β ∈ [β₋, β₊]`; that uniform form is not
proved here.  Since the thermal density of a smooth potential is unique, the dependence on `ρ_β` is only
nominal.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.ME.Bias

variable {d : ℕ}

open HRS HRS.Main

theorem critical_bias_constants_fixed (hd : 2 ≤ d) (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (m : ℝ) (hm : 24 * (d : ℝ) + 240 ≤ m) (T : ℝ) (hT : 0 < T) :
    ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp),
    (∃ C : ℝ, 0 < C ∧ ∀ (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) V β ρβ →
      ∀ u : ℝ, 0 ≤ u → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        SelectedFlow P (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β (hβm.trans_le hβ.1)) (u + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        law P X₀ = canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z : ℝ → Ω' → NegSobolev d m),
        IsStationaryGaussianField P' ((d : ℝ) / 2) β hs0 hsd (hβm.trans_le hβ.1) V ρβ m Z →
        ∀ p : ℝ, 1 ≤ p → p ≤ 2 →
          wassersteinE p (law P (windowFluc m T u (Real.sqrt N) X (fun _ => ρβ)))
              (law P' (windowPath m T 0 Z)) ≠ ⊤ ∧
          |(wassersteinE p (law P (windowFluc m T u (Real.sqrt N) X (fun _ => ρβ)))
              (law P' (windowPath m T 0 Z))).toReal / (Real.log N / Real.sqrt N) -
              ‖criticalBias d ((d : ℝ) / 2) β m ρβ‖| ≤ C / Real.sqrt (Real.log N)) ∧
    (∀ k : ℕ, 2 ≤ k → ∃ C : ℝ, 0 < C ∧
      ∀ (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) V β ρβ →
      ∀ u : ℝ, 0 ≤ u → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        SelectedFlow P (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β (hβm.trans_le hβ.1)) (u + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
          (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
        law P X₀ = canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z : ℝ → Ω' → NegSobolev d m),
        IsStationaryGaussianField P' ((d : ℝ) / 2) β hs0 hsd (hβm.trans_le hβ.1) V ρβ m Z →
        (∀ Φ : PathSpace d m T → ℝ, Φ ∈ CbUnitBall (PathSpace d m T) k →
          |(∫ z, Φ z ∂(law P (windowFluc m T u (Real.sqrt N) X (fun _ => ρβ))) -
              ∫ z, Φ z ∂(law P' (windowPath m T 0 Z))) / (Real.log N / Real.sqrt N) -
            ∫ ω, fderiv ℝ Φ (windowPath m T 0 Z ω)
              (constPath m T (criticalBias d ((d : ℝ) / 2) β m ρβ)) ∂P'|
            ≤ C / Real.sqrt (Real.log N)) ∧
        |smoothDist k (law P (windowFluc m T u (Real.sqrt N) X (fun _ => ρβ)))
              (law P' (windowPath m T 0 Z)) / (Real.log N / Real.sqrt N) -
            smoothConstant P' k (windowPath m T 0 Z)
              (constPath m T (criticalBias d ((d : ℝ) / 2) β m ρβ))| ≤ C / Real.sqrt (Real.log N)) ∧
    (∀ k : ℕ, 2 ≤ k → ∀ (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) V β ρβ →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z : ℝ → Ω' → NegSobolev d m),
        IsStationaryGaussianField P' ((d : ℝ) / 2) β hs0 hsd (hβm.trans_le hβ.1) V ρβ m Z →
        criticalBias d ((d : ℝ) / 2) β m ρβ ≠ 0 →
        0 < smoothConstant P' k (windowPath m T 0 Z)
          (constPath m T (criticalBias d ((d : ℝ) / 2) β m ρβ))) := by
  intro β hβ
  have hβ0 : 0 < β := hβm.trans_le hβ.1
  have hm2 : (d : ℝ) < 2 * m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  -- the third clause needs no constants
  have h3 : ∀ k : ℕ, 2 ≤ k → ∀ (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) V β ρβ →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z : ℝ → Ω' → NegSobolev d m),
        IsStationaryGaussianField P' ((d : ℝ) / 2) β hs0 hsd hβ0 V ρβ m Z →
        criticalBias d ((d : ℝ) / 2) β m ρβ ≠ 0 →
        0 < smoothConstant P' k (windowPath m T 0 Z)
          (constPath m T (criticalBias d ((d : ℝ) / 2) β m ρβ)) := by
    intro k hk ρβ hρβ Ω' _ P' _ Z hZ hb
    have hG : AEMeasurable (windowPath m T 0 Z) P' :=
      (HRS.MD.EQGaussWindow.eqgw_fidi hd hs0 hsd V hβ0 ρβ m T P' Z hZ 0 le_rfl).1
    refine smoothConstant_pos_of_aemeasurable P' _ hG k (by omega) _ ?_
    intro h0
    have := norm_constPath (m := m) hT.le (criticalBias d ((d : ℝ) / 2) β m ρβ)
    rw [h0, norm_zero] at this
    exact hb (norm_eq_zero.1 this.symm)
  by_cases hex : ∃ ρ, IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) V β ρ
  · obtain ⟨ρs, hρs⟩ := hex
    have hρsm : SmoothPosDensity ρs := smoothPos_of_thermal hd hs0 hsd hβ0 hV hρs
    obtain ⟨C₁, hC₁⟩ := HRS.ME.Marginal.critical_marginal_expansion_fixed hd β hβ0 ρs hρsm
    have hbound : ∀ N : ℕ, 2 ≤ N →
        firstMarginal (modulatedGibbs (periodicRiesz d ((d : ℝ) / 2)) N β (withDensityReal ρs)) ≪
            withDensityReal ρs ∧
          eLpNorm (fun y =>
              ((firstMarginal (modulatedGibbs (periodicRiesz d ((d : ℝ) / 2)) N β
                  (withDensityReal ρs))).rnDeriv (withDensityReal ρs) y).toReal - 1 -
                Real.log N / N * (β ^ 2 * sphereArea d / d *
                  responseInverse (periodicRiesz d ((d : ℝ) / 2)) (withDensityReal ρs) β ρs y))
            2 (withDensityReal ρs) ≤ ENNReal.ofReal (|C₁| * Real.sqrt (Real.log N) / N) := by
      intro N hN
      obtain ⟨h1, h2⟩ := hC₁ N hN
      refine ⟨h1, h2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
      have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _)) hN0.le
    have hsh := shift_norm_bound_of_L2 hd hβ0 hρsm hm2 (abs_nonneg C₁) hbound
    set Bc : ℝ := Real.sqrt 2 * Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m))) *
      |C₁| with hBc
    have hBc0 : 0 ≤ Bc := by positivity
    obtain ⟨Ccp, hCcp, hcp⟩ := HRS.ME.CritFinalUnif.critical_centered_path_proved hd hs0 hsd V hV
      βm βp hβm hββ m hm T hT
    obtain ⟨C, hC, hdiv⟩ := div_bound Ccp Bc (‖criticalBias d ((d : ℝ) / 2) β m ρs‖ ^ 2)
      hCcp.le hBc0 (sq_nonneg _)
    -- all instance data
    have key : ∀ (ρβ : Torus d → ℝ),
        IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) V β ρβ →
        ∀ u : ℝ, 0 ≤ u → ∀ N : ℕ, 2 ≤ N →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
          SelectedFlow P (PDE.mfData d ((d : ℝ) / 2) hs0 hsd V β hβ0) (u + T) X₀ W X →
          (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
            (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) →
          law P X₀ = canonicalGibbs (periodicRiesz d ((d : ℝ) / 2)) V N β →
        ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
          (Z : ℝ → Ω' → NegSobolev d m),
          IsStationaryGaussianField P' ((d : ℝ) / 2) β hs0 hsd hβ0 V ρβ m Z →
          (∀ p : ℝ, 1 ≤ p → p ≤ 2 →
            wassersteinE p (law P (windowFluc m T u (Real.sqrt N) X (fun _ => ρβ)))
                (law P' (windowPath m T 0 Z)) ≠ ⊤ ∧
              |(wassersteinE p (law P (windowFluc m T u (Real.sqrt N) X (fun _ => ρβ)))
                  (law P' (windowPath m T 0 Z))).toReal / (Real.log N / Real.sqrt N) -
                  ‖criticalBias d ((d : ℝ) / 2) β m ρβ‖| ≤ C / Real.sqrt (Real.log N)) ∧
          (∀ k : ℕ, 2 ≤ k →
            (∀ Φ : PathSpace d m T → ℝ, Φ ∈ CbUnitBall (PathSpace d m T) k →
              |(∫ z, Φ z ∂(law P (windowFluc m T u (Real.sqrt N) X (fun _ => ρβ))) -
                  ∫ z, Φ z ∂(law P' (windowPath m T 0 Z))) / (Real.log N / Real.sqrt N) -
                ∫ ω, fderiv ℝ Φ (windowPath m T 0 Z ω)
                  (constPath m T (criticalBias d ((d : ℝ) / 2) β m ρβ)) ∂P'|
                ≤ C / Real.sqrt (Real.log N)) ∧
            |smoothDist k (law P (windowFluc m T u (Real.sqrt N) X (fun _ => ρβ)))
                  (law P' (windowPath m T 0 Z)) / (Real.log N / Real.sqrt N) -
                smoothConstant P' k (windowPath m T 0 Z)
                  (constPath m T (criticalBias d ((d : ℝ) / 2) β m ρβ))| ≤
              C / Real.sqrt (Real.log N)) := by
      intro ρβ hρβ u hu N hN Ω _ P _ X₀ W X hflow hfilt hinit Ω' _ P' _ Z hZ
      obtain rfl : ρβ = ρs := thermal_unique_of_smooth hd hs0 hsd hβ0 hV hρβ hρs
      have hX : HRS.LZ.IsStationaryGibbsFlow P ((d : ℝ) / 2) hs0 hsd V β hβ0 (u + T) X₀ W X :=
        ⟨hflow, hfilt, hinit⟩
      obtain ⟨hc2, hcp', hcpk⟩ := hcp β hβ ρβ hρβ u hu N hN P X₀ W X hflow hfilt hinit P' Z hZ
      have hshift : ‖shiftE d ((d : ℝ) / 2) V N β m ρβ -
          (Real.log N / Real.sqrt N) • criticalBias d ((d : ℝ) / 2) β m ρβ‖ ≤
          Bc * (Real.sqrt (Real.log N) / Real.sqrt N) := by
        unfold shiftE
        rw [canonical_eq_modulated_thermal hd hs0 hsd hV hβ0 hρβ N]
        have := hsh N hN
        calc _ ≤ _ := this
          _ = _ := by rw [hBc]; ring
      exact instance_clauses hd hs0 hsd V hV hβ0 hρβ hm2 hT hu hN P hX P' Z hZ hCcp.le
        (fun p hp1 hp2 => hcp' p hp1 hp2) (fun k hk => hcpk k hk) hshift (hdiv N hN)
    refine ⟨⟨C, hC, fun ρβ hρβ u hu N hN Ω _ P _ X₀ W X hflow hfilt hinit Ω' _ P' _ Z hZ p hp1 hp2 =>
        (key ρβ hρβ u hu N hN P X₀ W X hflow hfilt hinit P' Z hZ).1 p hp1 hp2⟩,
      fun k hk => ⟨C, hC, fun ρβ hρβ u hu N hN Ω _ P _ X₀ W X hflow hfilt hinit Ω' _ P' _ Z hZ =>
        (key ρβ hρβ u hu N hN P X₀ W X hflow hfilt hinit P' Z hZ).2 k hk⟩, h3⟩
  · refine ⟨⟨1, one_pos, fun ρβ hρβ => absurd ⟨ρβ, hρβ⟩ hex⟩,
      fun k hk => ⟨1, one_pos, fun ρβ hρβ => absurd ⟨ρβ, hρβ⟩ hex⟩, h3⟩

end HRS.ME.Bias
