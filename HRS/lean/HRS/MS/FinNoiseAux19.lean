import HRS.MS.FinNoiseAux18

/-!
# S8.6 `finite_noise`: one chart, symmetric roots in the feature space (S86)

`s86_chart_root`: for a chart with reference density between `lo` and `hi` (relative to Lebesgue measure on the
torus) and the empirical chart covariance of `N` particles satisfying the linear input, any symmetric roots `S_ω` of
`κ·C_N(ω)` and `Sb` of `κ·D` satisfy
`E ‖S - Sb‖²_HS ≤ (4κ/lo) (∑_k √d_k)² · 2 max(hi,0) (|Cin|/N + (Cin δ)²)`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.ChartAux

open HRS HRS.Uniform HRS.MS.FinNoise

variable {d : ℕ}

theorem s86_chart_root (r : ℕ) (hr : d < r)
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (U : Set X) (hU : MeasurableSet U) (ψ : X → Torus d) (hψ : Measurable ψ)
    (lo hi : ℝ) (hlo0 : 0 < lo)
    (hlo : ENNReal.ofReal lo • (volume : Measure (Torus d)) ≤ (μ.restrict U).map ψ)
    (hle : (μ.restrict U).map ψ ≤ ENNReal.ofReal hi • (volume : Measure (Torus d)))
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (N : ℕ) (hN : 1 ≤ N) (xs : Fin N → Ω → X) (hxs : ∀ i, Measurable (xs i)) (δ : ℝ)
    (g : X → ℝ) (hg : Measurable g)
    (hmarg : (N : ℝ≥0∞)⁻¹ • ∑ i, P.map (xs i) = μ.withDensity fun x => ENNReal.ofReal (g x))
    (Cin : ℝ)
    (hgL2 : ∫⁻ x, ‖g x - 1‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal ((Cin * δ) ^ 2))
    (hvar : ∀ f : X → ℝ, Measurable f → MemLp f 2 μ →
      evariance (fun ω => (N : ℝ)⁻¹ * ∑ i, f (xs i ω)) P ≤
        ENNReal.ofReal (Cin * (N : ℝ)⁻¹ * ∫ x, f x ^ 2 ∂μ))
    (κ : ℝ) (hκ : 0 < κ)
    (S : Ω → FeatureSpace d →L[ℝ] FeatureSpace d)
    (hS : ∀ ω, IsSqrtOfForm (S ω) (κ • outerCov (chartFeature (d := d) r)
      (((((N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (xs i ω)).restrict U).map ψ))))
    (Sb : FeatureSpace d →L[ℝ] FeatureSpace d)
    (hSb : IsSqrtOfForm Sb (κ • outerCov (chartFeature (d := d) r) ((μ.restrict U).map ψ))) :
    ∫⁻ ω, ∑' j, ENNReal.ofReal (‖(S ω - Sb) (hb d j)‖ ^ 2) ∂P ≤
      ENNReal.ofReal (4 * κ / lo) *
        (ENNReal.ofReal ((∑' k : Lattice d, Real.sqrt (chartWeight r k)) ^ 2) *
          ENNReal.ofReal (2 * max hi 0 * (|Cin| * (N : ℝ)⁻¹ + (Cin * δ) ^ 2))) := by
  classical
  letI : MeasurableSpace (FeatureSpace d) := borel _
  haveI : BorelSpace (FeatureSpace d) := ⟨rfl⟩
  haveI := secondCountable_featureSpace d
  have hbc := continuous_chartFeature (d := d) r hr
  have hM : ∀ u, ‖chartFeature (d := d) r u‖ ^ 2 ≤ 2 * ∑' k : Lattice d, chartWeight r k :=
    fun u => norm_sq_chartFeature_le r hr u
  set ν : Measure (Torus d) := (μ.restrict U).map ψ with hνdef
  have hD : IsTraceClassCov (outerCov (chartFeature (d := d) r) ν) :=
    isTraceClassCov_outerCov hbc hM ν
  have hD₀e : ∀ i y, outerCov (chartFeature (d := d) r) (volume : Measure (Torus d)) (hb d i) y =
      chartWeight r i * inner ℝ (hb d i : FeatureSpace d) y := outerCov_vol_diag r hr
  have hcD0 := chart_hcD r hr ν lo hlo0.le hlo
  have hdd : ∀ i : Lattice d, 0 < chartWeight r i := chartWeight_pos r
  have hpt : ∀ ω, ∑' j, ENNReal.ofReal (‖(S ω - Sb) (hb d j)‖ ^ 2) ≤
      ENNReal.ofReal (4 * κ / lo) * relQuad (hb d) (chartWeight r)
        (outerCov (chartFeature (d := d) r)
          (((((N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (xs i ω)).restrict U).map ψ)) -
          outerCov (chartFeature (d := d) r) ν) := by
    intro ω
    haveI := isFiniteMeasure_empirical N hN (fun k => xs k ω)
    have hCN := isTraceClassCov_outerCov hbc hM
      (((((N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (xs i ω)).restrict U).map ψ))
    have K := s86_root_cmp (hb d) (chartWeight r) hdd hD₀e (c := lo * κ) (by positivity)
      (fun x => by
        simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
        have := mul_le_mul_of_nonneg_left (hcD0 x) hκ.le
        nlinarith)
      (isTraceClassCov_smul hCN hκ.le) (isTraceClassCov_smul hD hκ.le) (hS ω) hSb
    have esub : ∀ A B : FeatureSpace d →L[ℝ] FeatureSpace d →L[ℝ] ℝ, κ • A - κ • B = κ • (A - B) :=
      fun A B => (smul_sub κ A B).symm
    rw [esub, relQuad_smul _ _ κ hκ.le] at K
    have hconst : (4 : ℝ≥0∞) * ENNReal.ofReal (lo * κ)⁻¹ * ENNReal.ofReal (κ ^ 2) =
        ENNReal.ofReal (4 * κ / lo) := by
      rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    refine K.trans (le_of_eq ?_)
    rw [← mul_assoc, hconst]

  calc ∫⁻ ω, ∑' j, ENNReal.ofReal (‖(S ω - Sb) (hb d j)‖ ^ 2) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal (4 * κ / lo) * relQuad (hb d) (chartWeight r)
        (outerCov (chartFeature (d := d) r)
          (((((N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (xs i ω)).restrict U).map ψ)) -
          outerCov (chartFeature (d := d) r) ν) ∂P := lintegral_mono hpt
    _ = ENNReal.ofReal (4 * κ / lo) * ∫⁻ ω, relQuad (hb d) (chartWeight r)
        (outerCov (chartFeature (d := d) r)
          (((((N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (xs i ω)).restrict U).map ψ)) -
          outerCov (chartFeature (d := d) r) ν) ∂P := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
        gcongr
        exact s86_chart_relQuad r hr μ U hU ψ hψ hi hle P N hN xs hxs δ g hg hmarg Cin hgL2 hvar

end HRS.Uniform.ChartAux
