import HRS.MS.S21F_S19a

/-!
# S21F, packet R26-T3.S19: Gaussian spatial cutoff boundary estimate

Fixed `N`: `g_k = (1+∑‖X_i‖)^k ∈ L²(μ₀^{⊗N})` (Gaussian tail of the actual reference), the density `dQ/dμ₀^{⊗N} ∈ L²` (S05, `r = 2`), hence
`g_k ∈ L¹(Q_{N,γ})` (Cauchy-Schwarz and `integrable_rnDeriv_smul_iff`), and the tails `∫_{∑‖X_i‖ ≥ L} g_k dQ → 0` by dominated convergence.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole

namespace HRS.MS.R26T3

theorem r26t3_infinity_boundary {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (hγ : 0 < p.γ) (N : ℕ) (hN : 2 ≤ N) (k : ℕ) :
    Integrable (fun X : EucConfig p.d N => (1 + ∑ i, ‖X i‖) ^ k) (r26t3_Q R N) ∧
    Tendsto (fun L : ℝ => ∫ X in {X : EucConfig p.d N | L ≤ ∑ i, ‖X i‖},
      (1 + ∑ i, ‖X i‖) ^ k ∂(r26t3_Q R N)) atTop (𝓝 0) := by
  obtain ⟨-, -, -, href⟩ := r26t3_reference_data p δ hδ hδh R
  obtain ⟨M₀, c, S, hc, hTc⟩ := href 0
  have hP : IsProbabilityMeasure (HRS.Whole.withDensityReal (R.ρ 0)) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hTc.prob
  obtain ⟨hQprob, hLr⟩ := r26t3_static_pressure hδ hδh R hγ
  obtain ⟨C2, hC2⟩ := hLr 2 (by norm_num)
  set ν : Measure (EucConfig p.d N) := Measure.pi fun _ : Fin N => r26t3_mu R 0 with hν
  haveI : IsProbabilityMeasure (r26t3_mu R 0) := hP
  haveI := hQprob N hN
  set Q := r26t3_Q R N with hQ
  have hac : Q ≪ ν := by
    show HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel p.d p.s) N p.γ (r26t3_mu R 0) ≪ ν
    unfold HRS.Whole.modulatedGibbs
    exact Measure.AbsolutelyContinuous.smul_left (withDensity_absolutelyContinuous _ _) _
  have hρmeas : Measurable fun X : EucConfig p.d N => (Q.rnDeriv ν X).toReal :=
    (Measure.measurable_rnDeriv Q ν).ennreal_toReal
  have hρL2 : MemLp (fun X : EucConfig p.d N => (Q.rnDeriv ν X).toReal) 2 ν := by
    have := hC2 N hN
    simp only [ENNReal.ofReal_ofNat] at this
    exact lt_of_le_of_lt this ENNReal.ofReal_lt_top
  have hgm : ∀ k : ℕ, Measurable fun X : EucConfig p.d N => (1 + ∑ i, ‖X i‖) ^ k := fun k =>
    (measurable_const.add (Finset.measurable_sum _ fun i _ =>
      (measurable_norm.comp (measurable_pi_apply i)))).pow_const k
  have hgL2 : MemLp (fun X : EucConfig p.d N => (1 + ∑ i, ‖X i‖) ^ k) 2 ν := by
    rw [memLp_two_iff_integrable_sq (hgm k).aestronglyMeasurable]
    exact s21f_config_sq (fun m => s21f_moment_mu hTc hc m) k
  have hint : Integrable (fun X : EucConfig p.d N => (1 + ∑ i, ‖X i‖) ^ k) Q := by
    rw [← integrable_rnDeriv_smul_iff hac]
    have := hρL2.integrable_mul hgL2
    refine this.congr (Eventually.of_forall fun X => ?_)
    simp [mul_comm]
  refine ⟨hint, ?_⟩
  have hset : ∀ L : ℝ, MeasurableSet {X : EucConfig p.d N | L ≤ ∑ i, ‖X i‖} := fun L =>
    measurableSet_le measurable_const (Finset.measurable_sum _ fun i _ =>
      (measurable_norm.comp (measurable_pi_apply i)))
  have hDCT := tendsto_integral_filter_of_dominated_convergence
    (μ := Q) (l := (atTop : Filter ℝ))
    (F := fun (L : ℝ) (X : EucConfig p.d N) =>
      ({X : EucConfig p.d N | L ≤ ∑ i, ‖X i‖}).indicator (fun X => (1 + ∑ i, ‖X i‖) ^ k) X)
    (f := fun _ => (0 : ℝ)) (fun X => (1 + ∑ i, ‖X i‖) ^ k)
    (Eventually.of_forall fun L => ((hgm k).indicator (hset L)).aestronglyMeasurable)
    ?_ hint ?_
  · simpa [integral_indicator (hset _)] using hDCT
  · refine Eventually.of_forall fun L => Eventually.of_forall fun X => ?_
    have h0 : 0 ≤ (1 + ∑ i, ‖X i‖) ^ k := by positivity
    by_cases hX : X ∈ {X : EucConfig p.d N | L ≤ ∑ i, ‖X i‖}
    · simp only [indicator_of_mem hX, Real.norm_of_nonneg h0]; exact le_rfl
    · simp only [indicator_of_notMem hX, norm_zero]; exact h0
  · refine Eventually.of_forall fun X => ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop (∑ i, ‖X i‖)] with L hL
    have hX : X ∉ {X : EucConfig p.d N | L ≤ ∑ i, ‖X i‖} := by
      simp only [Set.mem_setOf_eq, not_le]; exact hL
    simp [indicator_of_notMem hX]

end HRS.MS.R26T3
