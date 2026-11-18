import HRS.MS.FinNoiseAux36
import HRS.Uniform.RelativeCov

/-!
# S8.6 `finite_noise`: the feature covariance as a sum over charts (Pro FR07) (S86b)

`s86_form_chart`: if the localised features are reconstructed on every chart, `χ_j(x) Γ(x) = 1_{U_j}(x) R_j b(ψ_j x)`
with `∑_j χ_j² = 1`, then for every finite measure `ν`,
`∫ ⟨Γ,u⟩⟨Γ,v⟩ dν = ∑_j 𝒞_j(R_j^* u, R_j^* v)`, with `𝒞_j = outerCov b ((ν|_{U_j}) ∘ ψ_j⁻¹)` the chart covariance of `ν`.
`s86_trace_outerCov`: the chart covariances are trace class with trace at most `2 ∑ d_k · ν(ℝ^d)` along `hb d`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.FinNoise

open HRS HRS.Uniform HRS.Uniform.ChartAux

variable {d : ℕ}

theorem s86_form_chart {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    [MeasurableSpace K] [BorelSpace K] {J : Type*} [Countable J] (r : ℕ) (hr : d < r)
    (ν : Measure (Euc d)) [IsFiniteMeasure ν]
    (U : J → Set (Euc d)) (hU : ∀ j, MeasurableSet (U j)) (ψ : J → Euc d → Torus d)
    (hψ : ∀ j, Measurable (ψ j)) (χ : J → Euc d → ℝ) (hχm : ∀ j, Measurable (χ j))
    (hχ1 : ∀ x, HasSum (fun j => χ j x ^ 2) 1)
    (Γ : Euc d → K) (hΓm : Measurable Γ) (B : ℝ) (hΓb : ∀ x, ‖Γ x‖ ≤ B)
    (R : J → FeatureSpace d →L[ℝ] K)
    (hR : ∀ j x, χ j x • Γ x = (U j).indicator (fun x => R j (chartFeature (d := d) r (ψ j x))) x)
    (u v : K) :
    ∫ x, ⟪Γ x, u⟫ * ⟪Γ x, v⟫ ∂ν = ∑' j, outerCov (chartFeature (d := d) r)
      ((ν.restrict (U j)).map (ψ j))
      (ContinuousLinearMap.adjoint (R j) u) (ContinuousLinearMap.adjoint (R j) v) := by
  classical
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hΓb 0)
  have hinm : ∀ w : K, Measurable fun x => ⟪Γ x, w⟫ := fun w => by
    have : (fun x => ⟪Γ x, w⟫) = (innerSL ℝ w) ∘ Γ := by
      funext x; simp [real_inner_comm]
    rw [this]
    exact (innerSL ℝ w).continuous.measurable.comp hΓm
  set f : J → Euc d → ℝ := fun j x => ⟪χ j x • Γ x, u⟫ * ⟪χ j x • Γ x, v⟫ with hf
  have hfe : ∀ j x, f j x = χ j x ^ 2 * (⟪Γ x, u⟫ * ⟪Γ x, v⟫) := by
    intro j x; simp only [hf, inner_smul_left, conj_trivial]; ring
  have hfm : ∀ j, Measurable (f j) := fun j => by
    have : f j = fun x => χ j x ^ 2 * (⟪Γ x, u⟫ * ⟪Γ x, v⟫) := funext (hfe j)
    rw [this]
    exact ((hχm j).pow_const 2).mul ((hinm u).mul (hinm v))
  have hsum : ∀ x, ∑' j, f j x = ⟪Γ x, u⟫ * ⟪Γ x, v⟫ := by
    intro x
    simp_rw [hfe]
    rw [tsum_mul_right, (hχ1 x).tsum_eq, one_mul]
  -- the lintegral bound
  have hbound : ∀ j x, ‖f j x‖ₑ ≤ ENNReal.ofReal (χ j x ^ 2) * ENNReal.ofReal (B ^ 2 * ‖u‖ * ‖v‖) := by
    intro j x
    rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hfe, norm_mul, norm_mul, Real.norm_of_nonneg (sq_nonneg _)]
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    have h1 : ‖⟪Γ x, u⟫‖ ≤ B * ‖u‖ := (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hΓb x) (norm_nonneg _))
    have h2 : ‖⟪Γ x, v⟫‖ ≤ B * ‖v‖ := (norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hΓb x) (norm_nonneg _))
    calc ‖⟪Γ x, u⟫‖ * ‖⟪Γ x, v⟫‖ ≤ (B * ‖u‖) * (B * ‖v‖) :=
          mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
      _ = B ^ 2 * ‖u‖ * ‖v‖ := by ring
  have hfin : ∑' j, ∫⁻ x, ‖f j x‖ₑ ∂ν ≠ ∞ := by
    have h1 : ∑' j, ∫⁻ x, ‖f j x‖ₑ ∂ν ≤
        ∑' j, ∫⁻ x, ENNReal.ofReal (χ j x ^ 2) * ENNReal.ofReal (B ^ 2 * ‖u‖ * ‖v‖) ∂ν :=
      ENNReal.tsum_le_tsum fun j => lintegral_mono fun x => hbound j x
    refine ne_top_of_le_ne_top ?_ h1
    have h2 : ∑' j, ∫⁻ x, ENNReal.ofReal (χ j x ^ 2) * ENNReal.ofReal (B ^ 2 * ‖u‖ * ‖v‖) ∂ν =
        ENNReal.ofReal (B ^ 2 * ‖u‖ * ‖v‖) * ν Set.univ := by
      simp_rw [lintegral_mul_const _ (((hχm _).pow_const 2).ennreal_ofReal)]
      rw [ENNReal.tsum_mul_right, ← lintegral_tsum fun j =>
        (((hχm j).pow_const 2).ennreal_ofReal).aemeasurable]
      have : ∀ x, ∑' j, ENNReal.ofReal (χ j x ^ 2) = 1 := fun x => by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => sq_nonneg _) (hχ1 x).summable, (hχ1 x).tsum_eq]
        simp
      simp_rw [this]
      simp [mul_comm]
    rw [h2]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have hswap := integral_tsum (fun j => (hfm j).aestronglyMeasurable) hfin
  -- integrals of the pieces
  have hpiece : ∀ j, ∫ x, f j x ∂ν = outerCov (chartFeature (d := d) r)
      ((ν.restrict (U j)).map (ψ j))
      (ContinuousLinearMap.adjoint (R j) u) (ContinuousLinearMap.adjoint (R j) v) := by
    intro j
    rw [outerCov_chart_apply r hr]
    set g : Torus d → ℝ := fun w => ⟪chartFeature (d := d) r w, ContinuousLinearMap.adjoint (R j) u⟫ *
      ⟪chartFeature (d := d) r w, ContinuousLinearMap.adjoint (R j) v⟫ with hg
    have hgc : Continuous g := by
      have hc := continuous_chartFeature (d := d) r hr
      exact (hc.inner continuous_const).mul (hc.inner continuous_const)
    have hfj : f j = (U j).indicator (fun x => g (ψ j x)) := by
      funext x
      by_cases hx : x ∈ U j
      · simp only [hf, hR j x, Set.indicator_of_mem hx, hg, ContinuousLinearMap.adjoint_inner_right]
      · simp [hf, hR j x, Set.indicator_of_notMem hx]
    rw [hfj, integral_indicator (hU j)]
    rw [integral_map (hψ j).aemeasurable hgc.aestronglyMeasurable]
  simp_rw [← hpiece]
  rw [← hswap]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => (hsum x).symm)

theorem s86_trace_outerCov (r : ℕ) (hr : d < r) (μ : Measure (Torus d)) [IsFiniteMeasure μ] :
    Summable (fun i : Lattice d => outerCov (chartFeature (d := d) r) μ (hb d i) (hb d i)) ∧
    ∑' i : Lattice d, outerCov (chartFeature (d := d) r) μ (hb d i) (hb d i) ≤
      (2 * ∑' k : Lattice d, chartWeight r k) * (μ Set.univ).toReal := by
  classical
  have hbc := continuous_chartFeature (d := d) r hr
  have hM : ∀ u, ‖chartFeature (d := d) r u‖ ^ 2 ≤ 2 * ∑' k : Lattice d, chartWeight r k :=
    fun u => norm_sq_chartFeature_le r hr u
  have hterm : ∀ i, outerCov (chartFeature (d := d) r) μ (hb d i) (hb d i) =
      ∫ u, ⟪chartFeature (d := d) r u, (hb d i : FeatureSpace d)⟫ ^ 2 ∂μ := by
    intro i
    rw [outerCov_chart_apply r hr]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => by ring)
  have hint : ∀ i, Integrable (fun u => ⟪chartFeature (d := d) r u, (hb d i : FeatureSpace d)⟫ ^ 2) μ :=
    fun i => ((hbc.inner continuous_const).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hnn : ∀ i, 0 ≤ outerCov (chartFeature (d := d) r) μ (hb d i) (hb d i) := fun i => by
    rw [hterm]; exact integral_nonneg fun u => sq_nonneg _
  have hF : ∀ F : Finset (Lattice d), ∑ i ∈ F, outerCov (chartFeature (d := d) r) μ (hb d i) (hb d i) ≤
      (2 * ∑' k : Lattice d, chartWeight r k) * (μ Set.univ).toReal := by
    intro F
    simp_rw [hterm]
    rw [← integral_finsetSum _ fun i _ => hint i]
    calc ∫ u, ∑ i ∈ F, ⟪chartFeature (d := d) r u, (hb d i : FeatureSpace d)⟫ ^ 2 ∂μ
        ≤ ∫ _u, 2 * ∑' k : Lattice d, chartWeight r k ∂μ := by
          refine integral_mono (integrable_finsetSum _ fun i _ => hint i) (integrable_const _)
            fun u => ?_
          have := (hb d).orthonormal.sum_inner_products_le (chartFeature (d := d) r u) (s := F)
          simp only [Real.norm_eq_abs, sq_abs] at this
          calc ∑ i ∈ F, ⟪chartFeature (d := d) r u, (hb d i : FeatureSpace d)⟫ ^ 2
              = ∑ i ∈ F, ⟪(hb d i : FeatureSpace d), chartFeature (d := d) r u⟫ ^ 2 := by
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [real_inner_comm]
            _ ≤ ‖chartFeature (d := d) r u‖ ^ 2 := this
            _ ≤ _ := hM u
      _ = (2 * ∑' k : Lattice d, chartWeight r k) * (μ Set.univ).toReal := by
          rw [integral_const, smul_eq_mul, Measure.real, mul_comm]
  exact ⟨summable_of_sum_le hnn hF, (summable_of_sum_le hnn hF).tsum_le_of_sum_le hF⟩

theorem s86_sqrt_sq_diag {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {S : H →L[ℝ] H} {C : H →L[ℝ] H →L[ℝ] ℝ} (hS : HRS.IsSqrtOfForm S C) (x : H) :
    ‖S x‖ ^ 2 = C x x := by
  rw [← real_inner_self_eq_norm_sq]
  exact hS.sq x x

end HRS.MS.FinNoise
