import HRS.MS.WsStatAux32

/-!
# S21 packet K-2: the master comparison against a given Gaussian process `Z`

`s21_master_Z`: `s21_master` combined with `s21_Zlaw` (the law of `Z`, a continuous process whose finite-dimensional coordinate laws are
`multivariateGaussian 0 (Cc + noiseCovW)`, is `gamma0 * Gamma`).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MS.S21

open HRS.Whole HRS.MS.GenPath HRS.MP.RdRem HRS.GF HRS.Uniform HRS.Whole.AppendixA
open HRS (Euc)

variable {d : ℕ}

theorem s21_master_Z (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) {N : ℕ} (hN : 2 ≤ N)
    (hC : OscAdjointInput (S.coeff N) b.m b.T) {Ctr Cmax : ℝ}
    (hOM : OrbitMaximalConclusion b.m b.T
      (fun (a : Fin d) (r : ℝ) (x : Euc d) => gradFeature (S.coeff N) b.m b.T a r x) Ctr Cmax)
    {Cs Cw1 Cw2 : ℝ} (hCmp : S56CompareHyp (d := d) b.m b.T Cs Cw1 Cw2)
    {Ctr' : ℝ} (hCtr0 : 0 ≤ Ctr') (hTr : S56TraceHyp b Ctr') (M₂ : ℝ) (hM₂0 : 0 ≤ M₂)
    (hM1 : b.M = -1) {ρ : Euc d → ℝ} (hρ' : ∀ t, S.ρ N t = ρ)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hX : IsWholeStrongSolution P (S.dyn N) b.T X₀ W X) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsWholeFilteredSolution P ℱ W' W X)
    (hstat : ∀ t ∈ Set.Icc (0 : ℝ) b.T, P.map (X (Real.toNNReal t)) = P.map (X 0))
    (hν1 : Integrable (fun x : Euc d => ‖x‖) (HRS.Whole.meanEmpirical (P.map (X 0))))
    (hfub : ∀ α : MultiIndex d, ∀ t ∈ Set.Icc (0 : ℝ) b.T,
      IntegrableOn (fun r => ∫ ζ, commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρ) X α t r ζ ∂P)
          (Set.Icc 0 t) ∧
        ∫ ζ, (∫ r in Set.Icc (0 : ℝ) t,
            commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρ) X α t r ζ) ∂P =
          ∫ r in Set.Icc (0 : ℝ) t, ∫ ζ, commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρ) X α t r ζ ∂P ∧
        Integrable (fun ζ => ∫ r in Set.Icc (0 : ℝ) t,
          commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρ) X α t r ζ) P)
    (hint : ∀ᵐ ζ ∂P, ∀ α : MultiIndex d, ∀ t ∈ Set.Icc (0 : ℝ) b.T,
      IntegrableOn (fun r => commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρ) X α t r ζ)
        (Set.Icc 0 t))
    (hmom : ∀ t ∈ Set.Icc (0 : ℝ) b.T,
      ∫⁻ ζ, ENNReal.ofReal (HRS.Whole.pair (HRS.Whole.empirical (X (Real.toNNReal t) ζ))
        (fun x => ‖x‖ ^ 2)) ∂P ≤ ENNReal.ofReal M₂ ∧
      ENNReal.ofReal (HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N t)) (fun x => ‖x‖ ^ 2)) ≤
        ENNReal.ofReal M₂)
    (hE1 : S.energyMomentE N 1 P X ≠ ⊤) {ER : ℝ≥0∞}
    (hrem : (∫⁻ ζ, (⨆ t : Set.Icc (0 : ℝ) b.T, l2NormE (fun α : MultiIndex d =>
        s21Gfun b S ρ P X t α ζ)) ^ (2 : ℝ) ∂P) ^ (1 / 2 : ℝ) ≤ ER)
    (γ0 : Measure (OscPath d b.m b.T)) [IsProbabilityMeasure γ0] {εs : ℝ} {εw : ℝ≥0∞}
    (hsm0 : smoothDist 2 (law P (s21Path0 hbv.hT.le S X (HRS.Whole.meanEmpirical (P.map (X 0))))) γ0 ≤ εs)
    (hw0 : wassersteinE 1 (law P (s21Path0 hbv.hT.le S X (HRS.Whole.meanEmpirical (P.map (X 0))))) γ0 ≤ εw)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Zh : ℝ → Ω' → OscDual d b.m) (hZm : ∀ t, Measurable (Zh t))
    (hZc : ∀ᵐ ζ ∂P', ContinuousOn (fun t => Zh t ζ) (Set.Icc 0 b.T))
    (Cc : ℝ → ℝ → MultiIndex d → MultiIndex d → ℝ)
    (hZ : ∀ (p : ℕ) (ts : Fin p → ℝ) (_ : ∀ a, ts a ∈ Set.Icc (0 : ℝ) b.T) (αs : Fin p → MultiIndex d),
      P'.map (fun ζ => (WithLp.toLp 2 fun a => OscDual.coord (Zh (ts a) ζ) (αs a) :
          EuclideanSpace ℝ (Fin p))) =
        multivariateGaussian 0 (Matrix.of fun a c => Cc (ts a) (ts c) (αs a) (αs c) +
          noiseCovW (S.coeff N) (S.q N) (ts a) (ts c) (oscTestFun b.m (αs a)) (oscTestFun b.m (αs c))))
    (hγ : ∀ (p : ℕ) (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) b.T) (αs : Fin p → MultiIndex d),
      (Matrix.of fun a c => Cc (ts a) (ts c) (αs a) (αs c)).PosSemidef ∧
      γ0.map (fun w : OscPath d b.m b.T => (WithLp.toLp 2 fun a => OscDual.coord (OscPath.at' w ⟨ts a, hts a⟩)
          (αs a) : EuclideanSpace ℝ (Fin p))) =
        multivariateGaussian 0 (Matrix.of fun a c => Cc (ts a) (ts c) (αs a) (αs c))) :
    ENNReal.ofReal (smoothDist 2 (law P (s21XiPath S X (HRS.Whole.meanEmpirical (P.map (X 0)))))
          (law P' (processWindow b.m b.T 0 Zh))) ≤
        ENNReal.ofReal Cs * ENNReal.ofReal (Ctr' * S.q N *
          generalLocalizationRate d (S.energyMomentE N 1 P X).toReal M₂ N) + ER + ENNReal.ofReal εs ∧
      wassersteinE 1 (law P (s21XiPath S X (HRS.Whole.meanEmpirical (P.map (X 0)))))
          (law P' (processWindow b.m b.T 0 Zh)) ≤
        ENNReal.ofReal Cw1 * (ENNReal.ofReal (Ctr' * S.q N *
          generalLocalizationRate d (S.energyMomentE N 1 P X).toReal M₂ N)) ^ (1 / 2 : ℝ) + ER + εw := by
  obtain ⟨Γ, hΓp, hΓ, hsm, hw⟩ := s21_master b hbv S hN hC hOM hCmp hCtr0 hTr M₂ hM₂0 hM1 hρ' P hX ℱ W' hF hstat
    hν1 hfub hint hmom hE1 hrem γ0 hsm0 hw0
  have hlaw : law P' (processWindow b.m b.T 0 Zh) =
      (γ0.prod Γ).map (fun z : OscPath d b.m b.T × OscPath d b.m b.T => z.1 + z.2) :=
    s21_Zlaw b.m b.T hbv.hT.le P' Zh hZm hZc Cc
      (fun t t' α α' => noiseCovW (S.coeff N) (S.q N) t t' (oscTestFun b.m α) (oscTestFun b.m α')) γ0 Γ hZ hγ
      (fun p ts hts αs => ⟨s21_noiseCov_psd b hbv S N hC hOM (s56_hS b S N) (s56_q_nonneg b S N (by omega))
        ts hts αs, hΓ p ts hts αs⟩)
  rw [hlaw]
  exact ⟨hsm, hw⟩

end HRS.MS.S21
