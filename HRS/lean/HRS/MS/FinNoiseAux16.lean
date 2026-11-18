import HRS.MS.FinNoiseAux15

/-!
# S8.6 `finite_noise`: the relative-quadratic-form estimate of `chart_current_proof` (S86)

`s86_chart_relQuad`: for one chart (`ν = (μ|_U) ∘ ψ⁻¹ ≤ hi · Leb`), the expected reference-relative quadratic form of
the empirical chart covariance against the reference covariance, taken in the Fourier basis `hb d` with the weights
`chartWeight r`, is at most `(∑_k √d_k)² · 2 max(hi,0) (|Cin|/N + (Cin δ)²)`.  It is the internal step `hrq` of
`HRS.Uniform.ChartAux.chart_aux` (which exports only the Bures bound), re-stated with the density bound `hle`
instead of the density `h`; it controls the symmetric roots through `s8p_psd_root_relative`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.ChartAux

open HRS HRS.Uniform HRS.Uniform.RelCov

variable {d : ℕ}

theorem s86_chart_relQuad (r : ℕ) (hr : d < r)
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (U : Set X) (hU : MeasurableSet U) (ψ : X → Torus d) (hψ : Measurable ψ)
    (hi : ℝ) (hle : (μ.restrict U).map ψ ≤ ENNReal.ofReal hi • (volume : Measure (Torus d)))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N : ℕ) (hN : 1 ≤ N) (xs : Fin N → Ω → X) (hxs : ∀ i, Measurable (xs i)) (δ : ℝ)
    (g : X → ℝ) (hg : Measurable g)
    (hmarg : (N : ℝ≥0∞)⁻¹ • ∑ i, P.map (xs i) = μ.withDensity fun x => ENNReal.ofReal (g x))
    (Cin : ℝ)
    (hgL2 : ∫⁻ x, ‖g x - 1‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal ((Cin * δ) ^ 2))
    (hvar : ∀ f : X → ℝ, Measurable f → MemLp f 2 μ →
      evariance (fun ω => (N : ℝ)⁻¹ * ∑ i, f (xs i ω)) P ≤
        ENNReal.ofReal (Cin * (N : ℝ)⁻¹ * ∫ x, f x ^ 2 ∂μ)) :
    ∫⁻ ω, relQuad (hb d) (chartWeight r)
        (outerCov (chartFeature (d := d) r)
          (((((N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (xs i ω)).restrict U).map ψ)) -
          outerCov (chartFeature (d := d) r) ((μ.restrict U).map ψ)) ∂P ≤
      ENNReal.ofReal ((∑' k : Lattice d, Real.sqrt (chartWeight r k)) ^ 2) *
        ENNReal.ofReal (2 * max hi 0 * (|Cin| * (N : ℝ)⁻¹ + (Cin * δ) ^ 2)) := by
  classical
  letI : MeasurableSpace (FeatureSpace d) := borel _
  haveI : BorelSpace (FeatureSpace d) := ⟨rfl⟩
  haveI := secondCountable_featureSpace d
  set ν : Measure (Torus d) := (μ.restrict U).map ψ with hνdef
  set S1 : ℝ := ∑' k : Lattice d, Real.sqrt (chartWeight r k) with hS1
  set Bα : ℝ := 2 * max hi 0 * (|Cin| * (N : ℝ)⁻¹ + (Cin * δ) ^ 2) with hBα
  have hmeas : ∀ p : Lattice d × Lattice d, AEMeasurable (fun ω => ENNReal.ofReal
      (((outerCov (chartFeature (d := d) r)
        (((((N : ℝ≥0∞)⁻¹ • ∑ k, Measure.dirac (xs k ω)).restrict U).map ψ)) -
        outerCov (chartFeature (d := d) r) ν) (hb d p.1) (hb d p.2)) ^ 2 /
          (chartWeight r p.1 + chartWeight r p.2))) P := by
    intro p
    refine Measurable.aemeasurable ?_
    have hfm : Measurable fun u : Torus d => chartBasis p.1 u * chartBasis p.2 u :=
      ((continuous_chartBasis p.1).mul (continuous_chartBasis p.2)).measurable
    have hFm : Measurable (U.indicator ((fun u : Torus d => chartBasis p.1 u * chartBasis p.2 u) ∘ ψ)) :=
      (hfm.comp hψ).indicator hU
    have hfun : (fun ω => ENNReal.ofReal
      (((outerCov (chartFeature (d := d) r)
        (((((N : ℝ≥0∞)⁻¹ • ∑ k, Measure.dirac (xs k ω)).restrict U).map ψ)) -
        outerCov (chartFeature (d := d) r) ν) (hb d p.1) (hb d p.2)) ^ 2 /
          (chartWeight r p.1 + chartWeight r p.2))) = fun ω => ENNReal.ofReal
      (chartWeight r p.1 * chartWeight r p.2 / (chartWeight r p.1 + chartWeight r p.2) *
        ((N : ℝ)⁻¹ * ∑ k, U.indicator ((fun u : Torus d => chartBasis p.1 u * chartBasis p.2 u) ∘ ψ) (xs k ω) -
          ∫ x, U.indicator ((fun u : Torus d => chartBasis p.1 u * chartBasis p.2 u) ∘ ψ) x ∂μ) ^ 2) := by
      funext ω
      rw [hνdef, chart_entry_eq r hr μ U hU ψ hψ N hN (fun k => xs k ω) p.1 p.2]
    rw [hfun]
    exact Measurable.ennreal_ofReal (measurable_const.mul
      (((measurable_const.mul (Finset.measurable_sum _ fun k _ => hFm.comp (hxs k))).sub
        measurable_const).pow_const 2))
  have hrq : ∫⁻ ω, relQuad (hb d) (chartWeight r)
        (outerCov (chartFeature (d := d) r)
          (((((N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (xs i ω)).restrict U).map ψ)) -
          outerCov (chartFeature (d := d) r) ν) ∂P ≤
      ENNReal.ofReal (S1 ^ 2) * ENNReal.ofReal Bα := by
    have e1 : ∫⁻ ω, relQuad (hb d) (chartWeight r)
          (outerCov (chartFeature (d := d) r)
            (((((N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (xs i ω)).restrict U).map ψ)) -
            outerCov (chartFeature (d := d) r) ν) ∂P =
        ∑' p : Lattice d × Lattice d, ∫⁻ ω, ENNReal.ofReal
          (((outerCov (chartFeature (d := d) r)
            (((((N : ℝ≥0∞)⁻¹ • ∑ k, Measure.dirac (xs k ω)).restrict U).map ψ)) -
            outerCov (chartFeature (d := d) r) ν) (hb d p.1) (hb d p.2)) ^ 2 /
              (chartWeight r p.1 + chartWeight r p.2)) ∂P := by
      rw [← lintegral_tsum hmeas]; rfl
    have e2 : ∑' p : Lattice d × Lattice d, ∫⁻ ω, ENNReal.ofReal
          (((outerCov (chartFeature (d := d) r)
            (((((N : ℝ≥0∞)⁻¹ • ∑ k, Measure.dirac (xs k ω)).restrict U).map ψ)) -
            outerCov (chartFeature (d := d) r) ν) (hb d p.1) (hb d p.2)) ^ 2 /
              (chartWeight r p.1 + chartWeight r p.2)) ∂P ≤
        ∑' p : Lattice d × Lattice d, ENNReal.ofReal
          (chartWeight r p.1 * chartWeight r p.2 / (chartWeight r p.1 + chartWeight r p.2)) *
            ENNReal.ofReal Bα := by
      refine ENNReal.tsum_le_tsum fun p => ?_
      have hw0 : 0 ≤ chartWeight r p.1 * chartWeight r p.2 / (chartWeight r p.1 + chartWeight r p.2) := by
        have := chartWeight_pos r p.1; have := chartWeight_pos r p.2; positivity
      rw [← ENNReal.ofReal_mul hw0]
      exact pair_bound r hr μ U hU ψ hψ hi hle P N hN xs hxs g hg hmarg Cin δ hgL2 hvar p.1 p.2
    have e3 : ∑' p : Lattice d × Lattice d, ENNReal.ofReal
          (chartWeight r p.1 * chartWeight r p.2 / (chartWeight r p.1 + chartWeight r p.2)) *
            ENNReal.ofReal Bα =
        (∑' p : Lattice d × Lattice d, ENNReal.ofReal
          (chartWeight r p.1 * chartWeight r p.2 / (chartWeight r p.1 + chartWeight r p.2))) *
            ENNReal.ofReal Bα := ENNReal.tsum_mul_right
    refine e1.le.trans (e2.trans (e3.le.trans ?_))
    gcongr
    exact sum_w_le r hr
  exact hrq

end HRS.Uniform.ChartAux
