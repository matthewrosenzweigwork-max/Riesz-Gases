import HRS.MS.S21T2_I8
import HRS.MS.S21T2_A1
import HRS.MS.S21T2_A2

/-!
# S21T2 packet A3: the window bound of `S21PrepMetric` from INIT, the window master and the Gaussian identification

For one realization (a resulting solution, a thermal equilibrium, a window start `a₀ ≥ 0`), the window comparison
of `S21PrepMetric` follows from

* `S21InitWin` (INIT, through `s21i_init_law` of S21T2_I8): the Gaussian `γ0` is compared with the transported initial
  path `K`;
* the window master, taken here as the hypothesis `hM` with the exact shape of the conclusion of `s21m_master` (WMASTER,
  packet S21S2, not yet compiled): for every probability `γ0` with `smoothDist`/`W_1` of `law K` to `γ0` at most `εs`/`εw`,
  there is a Gaussian `Γ` with `law Ξ` compared to `γ0 * Γ`, with the bounds `Cs Wt + F + εs` and `Cw Wt^{1/2} + F + εw`;
* the S10.4 bounds `F ≤ K₁ √N δ_N`, `Wt ≤ K₂ w_N` (hypotheses `hF`, `hWt`);
* the identification `law Z = γ0 * Γ` (`s21p_Zwin_law`) and the rate algebra (S21T2_A1).

The initial path of WMASTER, `s56EvalPath (s105K0 ..)`, is identified with the S10.5 coupling path by S21T2_A2
(under the hypotheses of `s105_k0_eval`, which are assumed here, and `X 0 = X₀` almost surely).

Not proved here (remaining inputs of `S21PrepMetric`): `hM` (WMASTER), `hF`, `hWt` (S10.4 with the D2 repair), the
orbit class inputs `hC hF hK hcl` (S10.3 with the D2 repair), measurability of `X₀` (not assumed by `S21PrepMetric`).
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S21T2

open HRS.Whole HRS.MS.GenPath HRS.MS.R2GenInit
open HRS (Euc cbNorm MemCb smoothDist wassersteinE)

variable {d : ℕ}

theorem s21t2_iN_nonneg {s β₀ : ℝ} {N : ℕ} (hδ : 0 ≤ HRS.deltaN d s N) : 0 ≤ iN d s β₀ N := by
  unfold iN
  split_ifs
  · positivity
  · exact Real.sqrt_nonneg _

theorem s21t2_jN_nonneg {s β₀ : ℝ} {N : ℕ} (hδ : 0 ≤ HRS.deltaN d s N) : 0 ≤ jN d s β₀ N := by
  unfold jN
  split_ifs
  · positivity
  · exact Real.rpow_nonneg hδ _

theorem s21t2_localizationRate_nonneg {s C₀ : ℝ} {N : ℕ} : 0 ≤ localizationRate d s C₀ N := by
  unfold localizationRate
  positivity

/-- The window bound of `S21PrepMetric` for one realization, from INIT, the window master (as hypothesis `hM`)
and the Gaussian identification of the target window law. -/
theorem s21t2_window_of_master {s a β β₀ T εstar c₁ C₁ Corb Cinit C₀ : ℝ} {Cs Cw K1 K2 C : ℝ} {F Wt : ℝ≥0∞}
    (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hT : 0 < T) (ha : 0 < a) (hβ : 0 < β)
    (horb : HRS.MS.S21.S21iOrbClass d s a β T εstar c₁ C₁ Corb)
    (hW : HRS.MS.S21.S21InitWin d s a β β₀ T εstar c₁ C₁ Cinit)
    (hCs : 0 ≤ Cs) (hCw : 0 ≤ Cw) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hCi : 0 ≤ Cinit) (hC0 : 0 ≤ C)
    (hC1 : Cs * K2 + K1 + Cinit ≤ C) (hC2 : Cw * Real.sqrt K2 + K1 + Cinit ≤ C)
    {ρβ : Euc d → ℝ} (hρβ : IsThermalEquilibrium d s a β ρβ) {ε : ℝ} {ψ : Euc d → ℝ}
    (hψ : IsAdmissiblePerturbation ρβ εstar ε ψ) {ρ : ℝ → Euc d → ℝ}
    (hρ : IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ) {N : ℕ} (hN : 2 ≤ N) {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X₀ : Ω → EucConfig d N} (hX₀ : Measurable X₀)
    (hlaw : HRS.law P X₀ = HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β₀ (HRS.Whole.withDensityReal (ρ 0)))
    (X : ℝ≥0 → Ω → EucConfig d N) (hinit : ∀ᵐ ζ ∂P, X 0 ζ = X₀ ζ)
    (hδ : 0 ≤ HRS.deltaN d s N)
    -- orbit inputs of `s105_k0_eval` for the window `a₀`
    (hC : OscAdjointInput ((quadraticGradientDyn d s a β).coeff ρ) ((wholeSpaceIndex d : ℕ) : ℝ) (a₀ + T))
    (hF0 : S105Feat d ((wholeSpaceIndex d : ℕ) : ℝ) T (a₀ + T)
      (fun b r x => r2WindowFeature ((quadraticGradientDyn d s a β).coeff ρ) ((wholeSpaceIndex d : ℕ) : ℝ) T
        (gradComp b) a₀ r x))
    (hK : ∀ (b : Fin d) (z : Euc d), S105WinK ((quadraticGradientDyn d s a β).coeff ρ) ((wholeSpaceIndex d : ℕ) : ℝ) T
      a₀ b 0 z)
    (hcl : ∀ (α : MultiIndex d) (u : ℝ), u ∈ Set.Icc (0 : ℝ) T →
      IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff ρ) (a₀ + u) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)
        (fun r => propagatorW ((quadraticGradientDyn d s a β).coeff ρ) r (a₀ + u)
          (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) α)))
    (hρ2 : Integrable (fun x : Euc d => ‖x‖ ^ 2 * ρ 0 x))
    -- the window master (WMASTER, `s21m_master`), for the given `F`, `Wt`
    (hM : ∀ γ0 : Measure (OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T), IsProbabilityMeasure γ0 →
      ∀ (εs : ℝ) (εw : ℝ≥0∞),
      smoothDist 2 (HRS.law P (fun ζ => s56EvalPath hT.le (s105K0 ((quadraticGradientDyn d s a β).coeff ρ)
        ((wholeSpaceIndex d : ℕ) : ℝ) T a₀ (Real.sqrt N) (ρ 0) X ζ))) γ0 ≤ εs →
      wassersteinE 1 (HRS.law P (fun ζ => s56EvalPath hT.le (s105K0 ((quadraticGradientDyn d s a β).coeff ρ)
        ((wholeSpaceIndex d : ℕ) : ℝ) T a₀ (Real.sqrt N) (ρ 0) X ζ))) γ0 ≤ εw →
      ∃ Γ : Measure (OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T), IsProbabilityMeasure Γ ∧
        (∀ (p : ℕ) (ts : Fin p → ℝ) (hts : ∀ i, ts i ∈ Set.Icc (0 : ℝ) T) (αs : Fin p → MultiIndex d),
          (Matrix.of fun i j => noiseCovW ((quadraticGradientDyn d s a β).coeff ρ) β⁻¹ (a₀ + ts i) (a₀ + ts j)
            (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs i))
            (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs j))).PosSemidef ∧
          Γ.map (fun w : OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T => (WithLp.toLp 2 fun i => OscDual.coord
              (OscPath.at' w ⟨ts i, hts i⟩) (αs i) : EuclideanSpace ℝ (Fin p))) =
            multivariateGaussian 0 (Matrix.of fun i j => noiseCovW ((quadraticGradientDyn d s a β).coeff ρ) β⁻¹
              (a₀ + ts i) (a₀ + ts j) (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs i))
              (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs j)))) ∧
        ENNReal.ofReal (smoothDist 2 (HRS.law P (flucPathW ((wholeSpaceIndex d : ℕ) : ℝ) T a₀ (Real.sqrt N) X ρ))
            ((γ0.prod Γ).map (fun z : OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T × OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T =>
              z.1 + z.2))) ≤ ENNReal.ofReal Cs * Wt + F + ENNReal.ofReal εs ∧
        wassersteinE 1 (HRS.law P (flucPathW ((wholeSpaceIndex d : ℕ) : ℝ) T a₀ (Real.sqrt N) X ρ))
            ((γ0.prod Γ).map (fun z : OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T × OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T =>
              z.1 + z.2)) ≤ ENNReal.ofReal Cw * Wt ^ (1 / 2 : ℝ) + F + εw)
    (hF : F ≤ ENNReal.ofReal (K1 * (Real.sqrt N * HRS.deltaN d s N)))
    (hWt : Wt ≤ ENNReal.ofReal (K2 * localizationRate d s C₀ N))
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : ℝ → Ω' → OscDual d ((wholeSpaceIndex d : ℕ) : ℝ))
    (hZ : ∀ T' : ℝ, IsLinearGaussianEvolutionW P' ((quadraticGradientDyn d s a β).coeff ρ)
      ((wholeSpaceIndex d : ℕ) : ℝ) β⁻¹ T'
      (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal (ρ 0)) β₀) Z) :
    smoothDist 2 (HRS.law P (flucPathW ((wholeSpaceIndex d : ℕ) : ℝ) T a₀ (Real.sqrt N) X ρ))
        (HRS.law P' (processWindow ((wholeSpaceIndex d : ℕ) : ℝ) T a₀ Z)) ≤
      C * (Real.sqrt N * HRS.deltaN d s N + localizationRate d s C₀ N + iN d s β₀ N) ∧
    wassersteinE 1 (HRS.law P (flucPathW ((wholeSpaceIndex d : ℕ) : ℝ) T a₀ (Real.sqrt N) X ρ))
        (HRS.law P' (processWindow ((wholeSpaceIndex d : ℕ) : ℝ) T a₀ Z)) ≤
      ENNReal.ofReal (C * (Real.sqrt N * HRS.deltaN d s N + Real.sqrt (localizationRate d s C₀ N) +
        jN d s β₀ N)) := by
  have hρ0 : HRS.Whole.IsProbDensity (ρ 0) := (hρ.global 0).density 0 ⟨le_rfl, le_rfl⟩
  -- INIT: the Gaussian `γ0` and its comparison with the transported initial path
  obtain ⟨γ0, hγ0, hfdd, hsm, hw1⟩ :=
    HRS.MS.S21.s21i_init_law hd horb hT hW hρβ hψ hρ hN ha₀ P hX₀ hlaw
  -- the window initial path of WMASTER equals the S10.5 coupling path a.s.
  have hKae : (fun ζ => s56EvalPath hT.le (s105K0 ((quadraticGradientDyn d s a β).coeff ρ)
        ((wholeSpaceIndex d : ℕ) : ℝ) T a₀ (Real.sqrt N) (ρ 0) X ζ)) =ᵐ[P]
      (fun ζ => r2InitCouplingPath ((quadraticGradientDyn d s a β).coeff ρ) ((wholeSpaceIndex d : ℕ) : ℝ) T
        (HRS.Whole.withDensityReal (ρ 0)) a₀ X₀ (fun _ _ => 0) ζ) := by
    filter_upwards [hinit] with ζ hζ
    exact s21t2_K0_eq _ hT.le ha₀ hρ0 hρ2 (by omega) X X₀ hC hF0 hK hcl ζ hζ
  have hlawK : HRS.law P (fun ζ => s56EvalPath hT.le (s105K0 ((quadraticGradientDyn d s a β).coeff ρ)
        ((wholeSpaceIndex d : ℕ) : ℝ) T a₀ (Real.sqrt N) (ρ 0) X ζ)) =
      HRS.law P (fun ζ => r2InitCouplingPath ((quadraticGradientDyn d s a β).coeff ρ) ((wholeSpaceIndex d : ℕ) : ℝ) T
        (HRS.Whole.withDensityReal (ρ 0)) a₀ X₀ (fun _ _ => 0) ζ) :=
    Measure.map_congr hKae
  have hsm' : smoothDist 2 (HRS.law P (fun ζ => s56EvalPath hT.le (s105K0 ((quadraticGradientDyn d s a β).coeff ρ)
        ((wholeSpaceIndex d : ℕ) : ℝ) T a₀ (Real.sqrt N) (ρ 0) X ζ))) γ0 ≤
      Cinit * (Real.sqrt N * HRS.deltaN d s N + iN d s β₀ N) := by
    rw [hlawK]; exact hsm
  have hw' : wassersteinE 1 (HRS.law P (fun ζ => s56EvalPath hT.le (s105K0 ((quadraticGradientDyn d s a β).coeff ρ)
        ((wholeSpaceIndex d : ℕ) : ℝ) T a₀ (Real.sqrt N) (ρ 0) X ζ))) γ0 ≤
      ENNReal.ofReal (Cinit * (Real.sqrt N * HRS.deltaN d s N + jN d s β₀ N)) := by
    rw [hlawK]; exact hw1
  -- WMASTER with this `γ0`
  obtain ⟨Γ, hΓ0, hΓfdd, hS, hW1⟩ := hM γ0 hγ0 _ _ hsm' hw'
  -- the target window law is `γ0 * Γ`
  have hZl := HRS.Whole.s21p_Zwin_law (C₀ := HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal (ρ 0)) β₀)
    hT.le ha₀ P' (hZ (a₀ + T)) γ0 Γ hfdd hΓfdd
  have hu : 0 ≤ Real.sqrt N * HRS.deltaN d s N := mul_nonneg (Real.sqrt_nonneg _) hδ
  have hi : 0 ≤ iN d s β₀ N := s21t2_iN_nonneg hδ
  have hj : 0 ≤ jN d s β₀ N := s21t2_jN_nonneg hδ
  have hw : 0 ≤ localizationRate d s C₀ N := s21t2_localizationRate_nonneg
  exact s21t2_window_bounds hCs hCw hK1 hK2 hCi hu hi hw hj hC0 hC1 hC2 _ _ γ0 Γ hZl hS (le_refl _) hW1 hF hWt
    (le_refl _) (le_refl _)

end HRS.MS.S21T2
