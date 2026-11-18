import HRS.MS.WsPrepI7

/-!
# S21T packet 8: INIT in the realization form consumed by the window master

* `s21iK_eq_comp`: `r2InitCouplingPath C m T μ₀ bw X₀ 0 ζ = s21iK C m T μ₀ bw (X₀ ζ)` (the coupling path of S10.5 with `η₀ = 0`, as a function of the
  initial configuration);
* `s21iK_measurable`: `s21iK` is measurable under the orbit input (it is `Φ_σ ∘ featureVec`);
* `s21iK_law`: for a measurable initial configuration `X₀` on a probability space `P`,
  `Law_P(r2InitCouplingPath C m T μ₀ bw X₀ 0) = (Law_P X₀).map s21iK`;
* `s21i_init_law`: `S21InitWin` for a realization `P, X₀` with `Law_P X₀ = ℚ_{N,β₀}(ρ⁰)`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S21

open HRS.Whole HRS.MS.GenPath
open HRS (Euc cbNorm MemCb smoothDist)

variable {d : ℕ}

theorem s21iK_eq_comp {Ω : Type*} {N : ℕ} (C : WholeCoeff d) (m T : ℝ) (μ0 : Measure (Euc d)) (bw : ℝ)
    (X₀ : Ω → EucConfig d N) (ζ : Ω) :
    r2InitCouplingPath C m T μ0 bw X₀ (fun _ _ => 0) ζ = s21iK C m T μ0 bw (X₀ ζ) := rfl

theorem s21iK_measurable (hd1 : 1 ≤ d) {T : ℝ} (hT : 0 < T) {C : WholeCoeff d} {Corb : ℝ}
    (h : S21iOrb d T C Corb) {bw : ℝ} (hbw : 0 ≤ bw) (μ0 : Measure (Euc d)) [IsProbabilityMeasure μ0]
    {N : ℕ} (hN : 1 ≤ N) :
    Measurable (s21iK C ((wholeSpaceIndex d : ℕ) : ℝ) T μ0 bw :
      EucConfig d N → OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T) := by
  obtain ⟨σ⟩ := s11p_exists_equiv (d := d)
  obtain ⟨D, hD, hDw⟩ := s21i_orb_data hd1 h bw hbw
  have hU := s21i_series_of_orb hT h hbw D hD
  obtain ⟨hφ, -, -⟩ := s21i_family hd1 h hbw D hD hDw σ
  have hfm : Measurable (featureVec (fun j => D.f (σ j)) μ0 : EucConfig d N → SeqL2) :=
    S45.s45_feature_measurable hN hφ
  have e : (s21iK C ((wholeSpaceIndex d : ℕ) : ℝ) T μ0 bw :
      EucConfig d N → OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T) =
      fun x => s21gPhi σ hT ((wholeSpaceIndex d : ℕ) : ℝ) (featureVec (fun j => D.f (σ j)) μ0 x) :=
    funext fun x => s21i_path_eq hT bw D hU σ hφ μ0 hN x
  rw [e]
  exact (s21gPhi σ hT ((wholeSpaceIndex d : ℕ) : ℝ)).continuous.measurable.comp hfm

theorem s21iK_law {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {N : ℕ} {C : WholeCoeff d} {m T : ℝ}
    {μ0 : Measure (Euc d)} {bw : ℝ} {X₀ : Ω → EucConfig d N} (hX₀ : Measurable X₀)
    (hK : Measurable (s21iK C m T μ0 bw : EucConfig d N → OscPath d m T)) :
    P.map (fun ζ => r2InitCouplingPath C m T μ0 bw X₀ (fun _ _ => 0) ζ) =
      (P.map X₀).map (s21iK C m T μ0 bw) := by
  rw [Measure.map_map hK hX₀]
  rfl

/-- INIT for a realization: the law of the coupling path `K_bw` of S10.5 (with `η₀ = 0`) under `P`, when `Law_P X₀ = ℚ_{N,β₀}(ρ⁰)`. -/
theorem s21i_init_law {s a β β₀ T εstar c₁ C₁ Corb Cinit : ℝ} (hd : 2 ≤ d)
    (horb : S21iOrbClass d s a β T εstar c₁ C₁ Corb) (hT : 0 < T)
    (hW : S21InitWin d s a β β₀ T εstar c₁ C₁ Cinit)
    {ρβ : Euc d → ℝ} (hρβ : IsThermalEquilibrium d s a β ρβ) {ε : ℝ} {ψ : Euc d → ℝ}
    (hψ : IsAdmissiblePerturbation ρβ εstar ε ψ) {ρ : ℝ → Euc d → ℝ}
    (hρ : IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ) {N : ℕ} (hN : 2 ≤ N) {bw : ℝ} (hbw : 0 ≤ bw)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {X₀ : Ω → EucConfig d N}
    (hX₀ : Measurable X₀)
    (hlaw : HRS.law P X₀ = HRS.Whole.modulatedGibbs (rieszKernel d s) N β₀ (HRS.Whole.withDensityReal (ρ 0))) :
    ∃ γ0 : Measure (OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T), IsProbabilityMeasure γ0 ∧
      (∀ (p : ℕ) (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T) (αs : Fin p → MultiIndex d),
        (Matrix.of fun i j => HRS.Whole.susceptibilityCov (rieszKernel d s) (HRS.Whole.withDensityReal (ρ 0)) β₀
          (propagatorW ((quadraticGradientDyn d s a β).coeff ρ) 0 (bw + ts i)
            (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs i)))
          (propagatorW ((quadraticGradientDyn d s a β).coeff ρ) 0 (bw + ts j)
            (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs j)))).PosSemidef ∧
        γ0.map (fun w : OscPath d ((wholeSpaceIndex d : ℕ) : ℝ) T => (WithLp.toLp 2 fun i =>
            OscDual.coord (OscPath.at' w ⟨ts i, hts i⟩) (αs i) : EuclideanSpace ℝ (Fin p))) =
          multivariateGaussian 0 (Matrix.of fun i j => HRS.Whole.susceptibilityCov (rieszKernel d s)
            (HRS.Whole.withDensityReal (ρ 0)) β₀
            (propagatorW ((quadraticGradientDyn d s a β).coeff ρ) 0 (bw + ts i)
              (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs i)))
            (propagatorW ((quadraticGradientDyn d s a β).coeff ρ) 0 (bw + ts j)
              (oscTestFun ((wholeSpaceIndex d : ℕ) : ℝ) (αs j))))) ∧
      smoothDist 2 (P.map (fun ζ => r2InitCouplingPath ((quadraticGradientDyn d s a β).coeff ρ)
          ((wholeSpaceIndex d : ℕ) : ℝ) T (HRS.Whole.withDensityReal (ρ 0)) bw X₀ (fun _ _ => 0) ζ)) γ0 ≤
        Cinit * (Real.sqrt N * HRS.deltaN d s N + iN d s β₀ N) ∧
      wassersteinE 1 (P.map (fun ζ => r2InitCouplingPath ((quadraticGradientDyn d s a β).coeff ρ)
          ((wholeSpaceIndex d : ℕ) : ℝ) T (HRS.Whole.withDensityReal (ρ 0)) bw X₀ (fun _ _ => 0) ζ)) γ0 ≤
        ENNReal.ofReal (Cinit * (Real.sqrt N * HRS.deltaN d s N + jN d s β₀ N)) := by
  have hρ0 : HRS.Whole.IsProbDensity (ρ 0) := (hρ.global 0).density 0 ⟨le_rfl, le_rfl⟩
  haveI : IsProbabilityMeasure (HRS.Whole.withDensityReal (ρ 0)) := HRS.Whole.Q34.isProbabilityMeasure_nu hρ0
  have hK := s21iK_measurable (by omega) hT (horb ρβ hρβ ε ψ hψ ρ hρ) hbw (HRS.Whole.withDensityReal (ρ 0))
    (N := N) (by omega)
  obtain ⟨γ0, hγ0, hfdd, hsm, hw1⟩ := hW ρβ hρβ ε ψ hψ ρ hρ N hN bw hbw
  rw [s21iK_law P hX₀ hK]
  have : P.map X₀ = HRS.Whole.modulatedGibbs (rieszKernel d s) N β₀ (HRS.Whole.withDensityReal (ρ 0)) := hlaw
  rw [this]
  exact ⟨γ0, hγ0, hfdd, hsm, hw1⟩

end HRS.MS.S21
