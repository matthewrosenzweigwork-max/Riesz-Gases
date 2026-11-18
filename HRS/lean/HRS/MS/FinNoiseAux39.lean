import HRS.MS.FinNoiseAux38
import HRS.MS.FinNoiseAux19

/-!
# S8.6 `finite_noise`: pointwise chart root bound and measurability of the relative form (S86b)

* `s86_outerCov_abs_le`: `|𝒞(z,w)| ≤ (2∑d_k) ν(ℝ^d) ‖z‖‖w‖` for the chart covariance `𝒞 = outerCov b ν`.
* `s86_chart_pt`: the pointwise form of `s86_chart_root` (no probability): for symmetric roots `S, Sb` of `κ𝒞_N, κ𝒞`,
  `∑_j ‖(S - Sb) b_j‖² ≤ (4κ/lo) 𝒬(𝒞_N - 𝒞)` when `𝒞 ≥ lo · 𝒞_{vol}`.
* `s86_relQuad_meas`: `ω ↦ 𝒬(𝒞_N(ω) - 𝒞)` is measurable (needed for Tonelli over the charts).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Uniform.ChartAux

open HRS HRS.Uniform HRS.MS.FinNoise

variable {d : ℕ}

theorem s86_outerCov_abs_le (r : ℕ) (hr : d < r) (μ : Measure (Torus d)) [IsFiniteMeasure μ]
    (z w : FeatureSpace d) :
    |outerCov (chartFeature (d := d) r) μ z w| ≤
      (2 * ∑' k : Lattice d, chartWeight r k) * (μ Set.univ).toReal * (‖z‖ * ‖w‖) := by
  have hbc := continuous_chartFeature (d := d) r hr
  have hM : ∀ u, ‖chartFeature (d := d) r u‖ ^ 2 ≤ 2 * ∑' k : Lattice d, chartWeight r k :=
    fun u => norm_sq_chartFeature_le r hr u
  rw [outerCov_chart_apply r hr]
  have hint : Integrable (fun u => ⟪chartFeature (d := d) r u, z⟫ * ⟪chartFeature (d := d) r u, w⟫) μ :=
    integrable_inner_mul hbc hM μ z w
  calc |∫ u, ⟪chartFeature (d := d) r u, z⟫ * ⟪chartFeature (d := d) r u, w⟫ ∂μ|
      = ‖∫ u, ⟪chartFeature (d := d) r u, z⟫ * ⟪chartFeature (d := d) r u, w⟫ ∂μ‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ∫ _u, (2 * ∑' k : Lattice d, chartWeight r k) * (‖z‖ * ‖w‖) ∂μ := by
        refine (norm_integral_le_integral_norm _).trans (integral_mono hint.norm (integrable_const _)
          fun u => ?_)
        rw [Real.norm_eq_abs, abs_mul]
        have h1 : |⟪chartFeature (d := d) r u, z⟫| ≤ ‖chartFeature (d := d) r u‖ * ‖z‖ :=
          abs_real_inner_le_norm _ _
        have h2 : |⟪chartFeature (d := d) r u, w⟫| ≤ ‖chartFeature (d := d) r u‖ * ‖w‖ :=
          abs_real_inner_le_norm _ _
        calc |⟪chartFeature (d := d) r u, z⟫| * |⟪chartFeature (d := d) r u, w⟫|
            ≤ (‖chartFeature (d := d) r u‖ * ‖z‖) * (‖chartFeature (d := d) r u‖ * ‖w‖) :=
              mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
          _ = ‖chartFeature (d := d) r u‖ ^ 2 * (‖z‖ * ‖w‖) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right (hM u) (by positivity)
    _ = _ := by
        rw [integral_const, smul_eq_mul, Measure.real]; ring

theorem s86_chart_pt (r : ℕ) (hr : d < r) (lo : ℝ) (hlo0 : 0 < lo)
    (ν0 νN : Measure (Torus d)) [IsFiniteMeasure ν0] [IsFiniteMeasure νN]
    (hlo : ENNReal.ofReal lo • (volume : Measure (Torus d)) ≤ ν0) (κ : ℝ) (hκ : 0 < κ)
    (S Sb : FeatureSpace d →L[ℝ] FeatureSpace d)
    (hS : IsSqrtOfForm S (κ • outerCov (chartFeature (d := d) r) νN))
    (hSb : IsSqrtOfForm Sb (κ • outerCov (chartFeature (d := d) r) ν0)) :
    ∑' j, ENNReal.ofReal (‖(S - Sb) (hb d j)‖ ^ 2) ≤ ENNReal.ofReal (4 * κ / lo) *
      relQuad (hb d) (chartWeight r) (outerCov (chartFeature (d := d) r) νN -
        outerCov (chartFeature (d := d) r) ν0) := by
  classical
  letI : MeasurableSpace (FeatureSpace d) := borel _
  haveI : BorelSpace (FeatureSpace d) := ⟨rfl⟩
  haveI := secondCountable_featureSpace d
  have hbc := continuous_chartFeature (d := d) r hr
  have hM : ∀ u, ‖chartFeature (d := d) r u‖ ^ 2 ≤ 2 * ∑' k : Lattice d, chartWeight r k :=
    fun u => norm_sq_chartFeature_le r hr u
  have hD : IsTraceClassCov (outerCov (chartFeature (d := d) r) ν0) :=
    isTraceClassCov_outerCov hbc hM ν0
  have hD₀e : ∀ i y, outerCov (chartFeature (d := d) r) (volume : Measure (Torus d)) (hb d i) y =
      chartWeight r i * inner ℝ (hb d i : FeatureSpace d) y := outerCov_vol_diag r hr
  have hcD0 := chart_hcD r hr ν0 lo hlo0.le hlo
  have hdd : ∀ i : Lattice d, 0 < chartWeight r i := chartWeight_pos r
  have hCN := isTraceClassCov_outerCov hbc hM νN
  have K := s86_root_cmp (hb d) (chartWeight r) hdd hD₀e (c := lo * κ) (by positivity)
    (fun x => by
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
      have := mul_le_mul_of_nonneg_left (hcD0 x) hκ.le
      nlinarith)
    (isTraceClassCov_smul hCN hκ.le) (isTraceClassCov_smul hD hκ.le) hS hSb
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

theorem s86_relQuad_meas (r : ℕ) (hr : d < r) {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsFiniteMeasure μ] (U : Set X) (hU : MeasurableSet U) (ψ : X → Torus d) (hψ : Measurable ψ)
    {Ω : Type*} [MeasurableSpace Ω] (N : ℕ) (hN : 1 ≤ N) (xs : Fin N → Ω → X)
    (hxs : ∀ i, Measurable (xs i)) :
    Measurable fun ω => relQuad (hb d) (chartWeight r)
      (outerCov (chartFeature (d := d) r)
        (((((N : ℝ≥0∞)⁻¹ • ∑ i, Measure.dirac (xs i ω)).restrict U).map ψ)) -
        outerCov (chartFeature (d := d) r) ((μ.restrict U).map ψ)) := by
  classical
  unfold relQuad
  refine Measurable.ennreal_tsum fun p => ?_
  have hfm : Measurable fun u : Torus d => chartBasis p.1 u * chartBasis p.2 u :=
    ((continuous_chartBasis p.1).mul (continuous_chartBasis p.2)).measurable
  have hFm : Measurable (U.indicator ((fun u : Torus d => chartBasis p.1 u * chartBasis p.2 u) ∘ ψ)) :=
    (hfm.comp hψ).indicator hU
  have hfun : (fun ω => ENNReal.ofReal
    (((outerCov (chartFeature (d := d) r)
      (((((N : ℝ≥0∞)⁻¹ • ∑ k, Measure.dirac (xs k ω)).restrict U).map ψ)) -
      outerCov (chartFeature (d := d) r) ((μ.restrict U).map ψ)) (hb d p.1) (hb d p.2)) ^ 2 /
        (chartWeight r p.1 + chartWeight r p.2))) = fun ω => ENNReal.ofReal
    (chartWeight r p.1 * chartWeight r p.2 / (chartWeight r p.1 + chartWeight r p.2) *
      ((N : ℝ)⁻¹ * ∑ k, U.indicator ((fun u : Torus d => chartBasis p.1 u * chartBasis p.2 u) ∘ ψ) (xs k ω) -
        ∫ x, U.indicator ((fun u : Torus d => chartBasis p.1 u * chartBasis p.2 u) ∘ ψ) x ∂μ) ^ 2) := by
    funext ω
    rw [chart_entry_eq r hr μ U hU ψ hψ N hN (fun k => xs k ω) p.1 p.2]
  show Measurable fun ω => ENNReal.ofReal
    (((outerCov (chartFeature (d := d) r)
      (((((N : ℝ≥0∞)⁻¹ • ∑ k, Measure.dirac (xs k ω)).restrict U).map ψ)) -
      outerCov (chartFeature (d := d) r) ((μ.restrict U).map ψ)) (hb d p.1) (hb d p.2)) ^ 2 /
        (chartWeight r p.1 + chartWeight r p.2))
  rw [hfun]
  exact Measurable.ennreal_ofReal (measurable_const.mul
    (((measurable_const.mul (Finset.measurable_sum _ fun k _ => hFm.comp (hxs k))).sub
      measurable_const).pow_const 2))

end HRS.Uniform.ChartAux
