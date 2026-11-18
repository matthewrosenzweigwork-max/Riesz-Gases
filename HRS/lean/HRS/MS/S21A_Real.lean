import HRS.MS.S21A_Orb
import HRS.MS.S21T2_A3
import HRS.MS.WsPrepQ6

/-!
# S21A packet 4: `S21PrepMetric` for one realization (window comparison, from INIT, the window master and S10.4)

`s21a_modif_ae`: two a.s. continuous processes that are modifications of each other have a.s. equal paths.
`s21a_window`: the two window bounds of `S21PrepMetric` for ONE realization `(P, X₀, W, X)` of the frozen statement S2.1 (ii) and one window start
`a₀ ≥ 0`, with the data

* `X'`, a modification of `X` which is an `IsR2Realization` (global strong solution with a filtration; `s21p_package_of_diss`);
* `hS : S21mData`, the moving window data along the resulting solution `ρ` (`s104b_data`);
* `hFb`, `hBt`: the S10.4 window errors for `X'` (`s21a_errors_up`);
* `hW : S21InitWin` (INIT, `s21i_init`) and `horb : S21iOrbClass`;
* `hCmp : S105WinCompareHyp` (`s105_win_compare`, unconditional).

It is `s21t2_window_of_master` (S21T2_A3) with the window master `hM` supplied by `s21m_master` (WMASTER) for the filtered modification `X'`, and the
transfer of the law of the particle window from `X'` to `X`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S21A

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.GenPath HRS.MS.S52 HRS.MP.RdRem HRS.MH.DualityRd HRS.MS.R2GenInit
  HRS.Uniform.Q54c HRS.GF

variable {d : ℕ}

/-- Modifications with a.s. continuous paths have a.s. equal paths. -/
theorem s21a_modif_ae {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X X' : ℝ≥0 → Ω → EucConfig d N} (hX : ∀ᵐ ζ ∂P, ∀ i, Continuous fun t => X t ζ i)
    (hX' : ∀ᵐ ζ ∂P, ∀ i, Continuous fun t => X' t ζ i) (hmod : ∀ t : ℝ≥0, X' t =ᵐ[P] X t) :
    ∀ᵐ ζ ∂P, ∀ t : ℝ, X' t.toNNReal ζ = X t.toNNReal ζ := by
  have hq : ∀ᵐ ζ ∂P, ∀ q : ℚ, X' (q : ℝ).toNNReal ζ = X (q : ℝ).toNNReal ζ :=
    ae_all_iff.2 fun q => hmod _
  filter_upwards [hX, hX', hq] with ζ h1 h2 h3 t
  funext i
  have key : (fun r : ℝ => X' r.toNNReal ζ i) = fun r => X r.toNNReal ζ i :=
    Rat.denseRange_cast.equalizer ((h2 i).comp continuous_real_toNNReal) ((h1 i).comp continuous_real_toNNReal)
      (funext fun q => by simp only [Function.comp_apply]; rw [h3 q])
  exact congr_fun key t

/-- The two window bounds of `S21PrepMetric` for one realization (see the module docstring). -/
theorem s21a_window {s a β β₀ T εstar c₁ C₁ Corb Cinit C₀ Cs Cw K1 K2 C : ℝ} {F Wt : ℝ≥0∞}
    (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (ha : 0 < a) (hβ : 0 < β) (hT : 0 < T)
    (horb : HRS.MS.S21.S21iOrbClass d s a β T εstar c₁ C₁ Corb)
    (hW : HRS.MS.S21.S21InitWin d s a β β₀ T εstar c₁ C₁ Cinit)
    (hCs : 0 ≤ Cs) (hCw : 0 ≤ Cw) (hK1 : 0 ≤ K1) (hK2 : 0 ≤ K2) (hCi : 0 ≤ Cinit) (hC0 : 0 ≤ C)
    (hC1 : Cs * K2 + K1 + Cinit ≤ C) (hC2 : Cw * Real.sqrt K2 + K1 + Cinit ≤ C)
    (hCmp : S105WinCompareHyp (d := d) ((wholeSpaceIndex d : ℕ) : ℝ) T Cs Cw)
    {ρβ : Euc d → ℝ} (hρβ : IsThermalEquilibrium d s a β ρβ) {ε : ℝ} {ψ : Euc d → ℝ}
    (hψ : IsAdmissiblePerturbation ρβ εstar ε ψ) {ρ : ℝ → Euc d → ℝ}
    (hρ : IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ) {N : ℕ} (hN : 2 ≤ N) {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hlaw : HRS.law P X₀ = HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β₀ (HRS.Whole.withDensityReal (ρ 0)))
    (hXcont : ∀ᵐ ζ ∂P, ∀ i, Continuous fun t => X t ζ i)
    (X' : ℝ≥0 → Ω → EucConfig d N) (hmod : ∀ t : ℝ≥0, X' t =ᵐ[P] X t)
    (hreal : IsR2Realization d s a β P X₀ W X')
    (hS : HRS.MS.S21m.S21mData d s a β T a₀ ρ)
    (hFb : ∫⁻ ζ, ⨆ u ∈ Set.Icc (0 : ℝ) T, l2NormE (fun α : MultiIndex d =>
        -(Real.sqrt N / 2) * ∫ r in Set.Icc (0 : ℝ) (a₀ + u), r2CommForcingMov
          ((quadraticGradientDyn d s a β).coeff ρ) s ((wholeSpaceIndex d : ℕ) : ℝ) ρ X' α
          (a₀ + u) r ζ) ∂P ≤ F)
    (hBt : ∃ Bt : ℝ → Ω → (KSpace d ((wholeSpaceIndex d : ℕ) : ℝ) T →L[ℝ]
        KSpace d ((wholeSpaceIndex d : ℕ) : ℝ) T →L[ℝ] ℝ),
      (∀ r ∈ Set.Icc (0 : ℝ) (a₀ + T), ∀ ζ u v, Bt r ζ u v =
        featureForm ((wholeSpaceIndex d : ℕ) : ℝ) T β⁻¹
          (fun (i : Fin d) (x : Euc d) => r2WindowFeature ((quadraticGradientDyn d s a β).coeff ρ)
            ((wholeSpaceIndex d : ℕ) : ℝ) T (gradComp i) a₀ r x) (HRS.Whole.empirical (X' r.toNNReal ζ)) u v -
        featureForm ((wholeSpaceIndex d : ℕ) : ℝ) T β⁻¹
          (fun (i : Fin d) (x : Euc d) => r2WindowFeature ((quadraticGradientDyn d s a β).coeff ρ)
            ((wholeSpaceIndex d : ℕ) : ℝ) T (gradComp i) a₀ r x) (HRS.Whole.withDensityReal (ρ r)) u v) ∧
      ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) (a₀ + T), ENNReal.ofReal (traceNormForm (Bt r ζ))) ∂P ≤ Wt)
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
  classical
  obtain ⟨ℱ, W', hfil⟩ := hreal.filtered
  have hX0m : Measurable (X' 0) := (hreal.solution 0).adapted 0
  have hlaw' : HRS.law P (X' 0) =
      HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel d s) N β₀ (HRS.Whole.withDensityReal (ρ 0)) := by
    rw [← hlaw]; exact Measure.map_congr (hreal.solution 0).init
  have hδ : 0 ≤ HRS.deltaN d s N := HRS.MS.S53.s53_deltaN_nonneg s (by omega)
  have hM : ∀ γ0 : Measure (OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T), IsProbabilityMeasure γ0 →
      ∀ (εs : ℝ) (εw : ℝ≥0∞),
      smoothDist 2 (HRS.law P (fun ζ => s56EvalPath hT.le (s105K0 ((quadraticGradientDyn d s a β).coeff ρ)
        ((wholeSpaceIndex d : ℕ) : ℝ) T a₀ (Real.sqrt N) (ρ 0) X' ζ))) γ0 ≤ εs →
      wassersteinE 1 (HRS.law P (fun ζ => s56EvalPath hT.le (s105K0 ((quadraticGradientDyn d s a β).coeff ρ)
        ((wholeSpaceIndex d : ℕ) : ℝ) T a₀ (Real.sqrt N) (ρ 0) X' ζ))) γ0 ≤ εw →
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
        ENNReal.ofReal (smoothDist 2 (HRS.law P (flucPathW ((wholeSpaceIndex d : ℕ) : ℝ) T a₀ (Real.sqrt N) X' ρ))
            ((γ0.prod Γ).map (fun z : OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T ×
              OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T => z.1 + z.2))) ≤ ENNReal.ofReal Cs * Wt + F +
              ENNReal.ofReal εs ∧
        wassersteinE 1 (HRS.law P (flucPathW ((wholeSpaceIndex d : ℕ) : ℝ) T a₀ (Real.sqrt N) X' ρ))
            ((γ0.prod Γ).map (fun z : OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T ×
              OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T => z.1 + z.2)) ≤
              ENNReal.ofReal Cw * Wt ^ (1 / 2 : ℝ) + F + εw := by
    intro γ0 hγ0 εs εw hsm hw
    haveI := hγ0
    exact HRS.MS.S21m.s21m_master hd hs0 hsd hβ ha₀ hT hS hN hCmp P X₀ W X' (hreal.solution (a₀ + T)) ℱ W' hfil
      F Wt hFb hBt γ0 hsm hw
  have key := HRS.MS.S21T2.s21t2_window_of_master (X := X') (X₀ := X' 0) (Corb := Corb) (Cinit := Cinit)
    (C₀ := C₀) (Cs := Cs) (Cw := Cw) (K1 := K1) (K2 := K2) (C := C) (F := F) (Wt := Wt)
    hd hs0 hT ha hβ horb hW hCs hCw hK1 hK2 hCi hC0 hC1 hC2 hρβ hψ hρ hN ha₀ P hX0m hlaw'
    (Filter.Eventually.of_forall fun _ => rfl) hδ hS.hC hS.hF
    (fun b z => hS.hK b 0 ⟨le_rfl, by linarith⟩ z)
    (fun α u hu => hS.hcl α (a₀ + u) (by linarith [hu.1])) hS.hρ2 hM hF hWt P' Z hZ
  have hae := s21a_modif_ae hXcont (hreal.solution 0).cont hmod
  have hlawfl : HRS.law P (flucPathW ((wholeSpaceIndex d : ℕ) : ℝ) T a₀ (Real.sqrt N) X' ρ) =
      HRS.law P (flucPathW ((wholeSpaceIndex d : ℕ) : ℝ) T a₀ (Real.sqrt N) X ρ) := by
    refine Measure.map_congr ?_
    filter_upwards [hae] with ζ h
    simp only [flucPathW, h]
  rw [← hlawfl]
  exact key

end HRS.MS.S21A
