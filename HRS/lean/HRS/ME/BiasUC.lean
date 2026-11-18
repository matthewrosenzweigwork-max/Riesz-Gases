import HRS.ME.BiasH
import HRS.ME.BiasUA
import HRS.ME.BiasUB
import HRS.ME.UnifP8A

/-!
# Uniform `critical_bias_constants` (packet P3)

Proof of the frozen statement `HRS.Main.critical_bias_constants` (tie in `HRS/ME/BiasUTie.lean`), following
`critical_bias_constants_fixed` with the uniform inputs `critical_marginal_expansion_unif_proof`,
`thermal_lower_cbNorm_unif` and `criticalBias_norm_le`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.ME.Bias

variable {d : ℕ}

open HRS HRS.Main

/-- Monotonicity of the scalar estimate in the quadratic term `D`. -/
theorem p_biasuc_div_mono {A B D D' C : ℝ} {N : ℕ} (hN : 2 ≤ N) (hD : D ≤ D')
    (h : (A * (N : ℝ) ^ (-(1 : ℝ) / 2) + B * (Real.sqrt (Real.log N) / Real.sqrt N) +
          (1 / 2) * (Real.log N / Real.sqrt N) ^ 2 * D') / (Real.log N / Real.sqrt N) ≤
        C / Real.sqrt (Real.log N)) :
    (A * (N : ℝ) ^ (-(1 : ℝ) / 2) + B * (Real.sqrt (Real.log N) / Real.sqrt N) +
          (1 / 2) * (Real.log N / Real.sqrt N) ^ 2 * D) / (Real.log N / Real.sqrt N) ≤
        C / Real.sqrt (Real.log N) := by
  have hx2 : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hr : 0 < Real.log N / Real.sqrt N :=
    div_pos hlogpos (Real.sqrt_pos.2 (by linarith))
  refine le_trans (div_le_div_of_nonneg_right ?_ hr.le) h
  have : (0 : ℝ) ≤ (1 / 2) * (Real.log N / Real.sqrt N) ^ 2 := by positivity
  nlinarith

theorem critical_bias_constants_unif (hd : 2 ≤ d) (hs0 : 0 ≤ (d : ℝ) / 2) (hsd : (d : ℝ) / 2 < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp)
    (m : ℝ) (hm : 24 * (d : ℝ) + 240 ≤ m) (T : ℝ) (hT : 0 < T) :
    (∃ C : ℝ, 0 < C ∧ ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
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
      ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
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
    (∀ k : ℕ, 2 ≤ k → ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) V β ρβ →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z : ℝ → Ω' → NegSobolev d m),
        IsStationaryGaussianField P' ((d : ℝ) / 2) β hs0 hsd (hβm.trans_le hβ.1) V ρβ m Z →
        criticalBias d ((d : ℝ) / 2) β m ρβ ≠ 0 →
        0 < smoothConstant P' k (windowPath m T 0 Z)
          (constPath m T (criticalBias d ((d : ℝ) / 2) β m ρβ))) := by
  have hm2 : (d : ℝ) < 2 * m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  -- uniform inputs
  obtain ⟨k₀, hk₀⟩ := HRS.ME.Unif.critical_marginal_expansion_unif_proof hd βm βp hβm hββ
  obtain ⟨c₀, Λ, hc₀, hΛ0, hth⟩ :=
    thermal_lower_cbNorm_unif hd hs0 hsd V hV βm βp hβm hββ k₀
  obtain ⟨C₁, hC₁⟩ := hk₀ c₀ Λ hc₀
  set Bc : ℝ := Real.sqrt 2 * Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m))) *
    |C₁| with hBc
  have hBc0 : 0 ≤ Bc := by positivity
  set Dd : ℝ := (Real.sqrt 2 * (βp ^ 2 * sphereArea d / d) * Λ *
    Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m)))) ^ 2 with hDd
  obtain ⟨Ccp, hCcp, hcp⟩ := HRS.ME.CritFinalUnif.critical_centered_path_proved hd hs0 hsd V hV
    βm βp hβm hββ m hm T hT
  obtain ⟨C, hC, hdiv⟩ := div_bound Ccp Bc Dd hCcp.le hBc0 (sq_nonneg _)
  -- the third clause needs no constants
  have h3 : ∀ k : ℕ, 2 ≤ k → ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
      IsThermalDensity (periodicRiesz d ((d : ℝ) / 2)) V β ρβ →
      ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
        (Z : ℝ → Ω' → NegSobolev d m),
        IsStationaryGaussianField P' ((d : ℝ) / 2) β hs0 hsd (hβm.trans_le hβ.1) V ρβ m Z →
        criticalBias d ((d : ℝ) / 2) β m ρβ ≠ 0 →
        0 < smoothConstant P' k (windowPath m T 0 Z)
          (constPath m T (criticalBias d ((d : ℝ) / 2) β m ρβ)) := by
    intro k hk β hβ ρβ hρβ Ω' _ P' _ Z hZ hb
    have hβ0 : 0 < β := hβm.trans_le hβ.1
    have hG : AEMeasurable (windowPath m T 0 Z) P' :=
      (HRS.MD.EQGaussWindow.eqgw_fidi hd hs0 hsd V hβ0 ρβ m T P' Z hZ 0 le_rfl).1
    refine smoothConstant_pos_of_aemeasurable P' _ hG k (by omega) _ ?_
    intro h0
    have := norm_constPath (m := m) hT.le (criticalBias d ((d : ℝ) / 2) β m ρβ)
    rw [h0, norm_zero] at this
    exact hb (norm_eq_zero.1 this.symm)
  have key : ∀ (β : ℝ) (hβ : β ∈ Set.Icc βm βp) (ρβ : Torus d → ℝ),
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
    intro β hβ ρβ hρβ u hu N hN Ω _ P _ X₀ W X hflow hfilt hinit Ω' _ P' _ Z hZ
    have hβ0 : 0 < β := hβm.trans_le hβ.1
    have hρm : SmoothPosDensity ρβ := smoothPos_of_thermal hd hs0 hsd hβ0 hV hρβ
    obtain ⟨hlow, hcb⟩ := hth β hβ ρβ hρβ
    have hbound : ∀ N : ℕ, 2 ≤ N →
        firstMarginal (modulatedGibbs (periodicRiesz d ((d : ℝ) / 2)) N β (withDensityReal ρβ)) ≪
            withDensityReal ρβ ∧
          eLpNorm (fun y =>
              ((firstMarginal (modulatedGibbs (periodicRiesz d ((d : ℝ) / 2)) N β
                  (withDensityReal ρβ))).rnDeriv (withDensityReal ρβ) y).toReal - 1 -
                Real.log N / N * (β ^ 2 * sphereArea d / d *
                  responseInverse (periodicRiesz d ((d : ℝ) / 2)) (withDensityReal ρβ) β ρβ y))
            2 (withDensityReal ρβ) ≤ ENNReal.ofReal (|C₁| * Real.sqrt (Real.log N) / N) := by
      intro N hN
      obtain ⟨h1, h2⟩ := hC₁ β hβ ρβ hρm (fun x => (hlow x).1) hcb N hN
      refine ⟨h1, h2.trans (ENNReal.ofReal_le_ofReal ?_)⟩
      have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _)) hN0.le
    have hsh := shift_norm_bound_of_L2 hd hβ0 hρm hm2 (abs_nonneg C₁) hbound
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
    -- uniform bound for the critical bias
    have hbn : ‖criticalBias d ((d : ℝ) / 2) β m ρβ‖ ^ 2 ≤ Dd := by
      have h1 := criticalBias_norm_le hd hm2 hβ0 hρm (fun x => (hlow x).2)
      have hS : 0 ≤ sphereArea d / d := by
        have := HRS.StaticLimitsAux.sphereArea_pos hd
        positivity
      have hβ2 : β ^ 2 ≤ βp ^ 2 := pow_le_pow_left₀ hβ0.le hβ.2 2
      have hfac : 0 ≤ Real.sqrt 2 * Λ *
          Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m))) := by positivity
      have h2 : Real.sqrt 2 * (β ^ 2 * sphereArea d / d) * Λ *
            Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m))) ≤
          Real.sqrt 2 * (βp ^ 2 * sphereArea d / d) * Λ *
            Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m))) := by
        have e1 : β ^ 2 * sphereArea d / d = β ^ 2 * (sphereArea d / d) := by ring
        have e2 : βp ^ 2 * sphereArea d / d = βp ^ 2 * (sphereArea d / d) := by ring
        rw [e1, e2]
        have : β ^ 2 * (sphereArea d / d) ≤ βp ^ 2 * (sphereArea d / d) :=
          mul_le_mul_of_nonneg_right hβ2 hS
        nlinarith [mul_le_mul_of_nonneg_right this hfac]
      rw [hDd]
      exact pow_le_pow_left₀ (norm_nonneg _) (h1.trans h2) 2
    exact instance_clauses hd hs0 hsd V hV hβ0 hρβ hm2 hT hu hN P hX P' Z hZ hCcp.le
      (fun p hp1 hp2 => hcp' p hp1 hp2) (fun k hk => hcpk k hk) hshift
      (p_biasuc_div_mono hN hbn (hdiv N hN))
  exact ⟨⟨C, hC, fun β hβ ρβ hρβ u hu N hN Ω _ P _ X₀ W X hflow hfilt hinit Ω' _ P' _ Z hZ p hp1 hp2 =>
      (key β hβ ρβ hρβ u hu N hN P X₀ W X hflow hfilt hinit P' Z hZ).1 p hp1 hp2⟩,
    fun k hk => ⟨C, hC, fun β hβ ρβ hρβ u hu N hN Ω _ P _ X₀ W X hflow hfilt hinit Ω' _ P' _ Z hZ =>
      (key β hβ ρβ hρβ u hu N hN P X₀ W X hflow hfilt hinit P' Z hZ).2 k hk⟩, h3⟩

end HRS.ME.Bias
