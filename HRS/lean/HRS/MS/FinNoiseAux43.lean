import HRS.MS.FinNoiseAux42
import HRS.MS.ShiftFldAux5

/-!
# S8.6 `finite_noise`: the canonical realization supplies the chart-level moment hypotheses (Pro FR09) (S86b)

For a canonical realization (`law (X t) = ℙ_{N,β}`, exchangeable) with the linear input `LinearInputBounds` at time `t`:
the particle positions `xs i = X_t(i)` are measurable, their mean law is the first marginal of the Gibbs law, which has a
density `g` with `‖g - 1‖_{L²(μ)}² ≤ (Cin δ)²`, and the variance of the linear statistic is the bound of `s86_chart_relQuad`.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.FinNoise

open HRS HRS.Whole

variable {d : ℕ}

theorem s86_linStat_eq (f : Euc d → ℝ) (hf : Measurable f) {N : ℕ} (hN : 1 ≤ N) (Y : EucConfig d N) :
    linStat f Y = (N : ℝ)⁻¹ * ∑ i, f (Y i) := by
  unfold linStat HRS.Whole.pair HRS.Whole.empirical
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp only [integral_dirac' _ _ hf.stronglyMeasurable, smul_eq_mul]
    rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
  · intro i _
    exact integrable_dirac enorm_lt_top

theorem s86_particle_data (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hreal : IsCanonicalRealization d ((d : ℝ) / 2) a β N P X₀ W X)
    (ℱ : Filtration ℝ mΩ) (hprog : ∀ i : Fin N, IsProgressive ℱ (fun r z => X (Real.toNNReal r) z i))
    (ρ : Euc d → ℝ) (Cin : ℝ) (t : ℝ) (ht : 0 ≤ t)
    (hlin : LinearInputBounds d ((d : ℝ) / 2) N (HRS.Whole.withDensityReal ρ) Cin P
      (X (Real.toNNReal t))) :
    (∀ i : Fin N, Measurable fun z => X (Real.toNNReal t) z i) ∧
    ∃ g : Euc d → ℝ, Measurable g ∧
      (N : ℝ≥0∞)⁻¹ • ∑ i : Fin N, P.map (fun z => X (Real.toNNReal t) z i) =
        (HRS.Whole.withDensityReal ρ).withDensity (fun x => ENNReal.ofReal (g x)) ∧
      ∫⁻ x, ‖g x - 1‖ₑ ^ 2 ∂(HRS.Whole.withDensityReal ρ) ≤
        ENNReal.ofReal ((Cin * deltaN d ((d : ℝ) / 2) N) ^ 2) ∧
      ∀ f : Euc d → ℝ, Measurable f → MemLp f 2 (HRS.Whole.withDensityReal ρ) →
        evariance (fun ω => (N : ℝ)⁻¹ * ∑ i : Fin N, f (X (Real.toNNReal t) ω i)) P ≤
          ENNReal.ofReal (Cin * (N : ℝ)⁻¹ * ∫ x, f x ^ 2 ∂(HRS.Whole.withDensityReal ρ)) := by
  classical
  have hN1 : 1 ≤ N := by omega
  set Y : Ω → EucConfig d N := X (Real.toNNReal t) with hY
  -- measurability of the coordinates
  have hmeas : ∀ i : Fin N, Measurable fun z => Y z i := by
    intro i
    have h1 := hprog i t
    have h3 : Measurable[ℱ t] (fun z : Ω => Y z i) := by
      letI : MeasurableSpace Ω := ℱ t
      exact h1.comp ((measurable_const (a := (⟨t, Set.mem_Iic.2 le_rfl⟩ : Set.Iic t))).prodMk measurable_id)
    exact h3.mono (ℱ.le t) le_rfl
  have hYm : Measurable Y := measurable_pi_iff.2 hmeas
  refine ⟨hmeas, ?_⟩
  obtain ⟨hmb, hvar⟩ := hlin
  obtain ⟨g, hgm, hfm, hgb, hgL, hgn⟩ := hmb
  refine ⟨g, hgm, ?_, ?_, ?_⟩
  · -- the mean law
    have hs0 : (0 : ℝ) < (d : ℝ) / 2 := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    have hsd : (d : ℝ) / 2 < d := by
      have : (2 : ℝ) ≤ d := by exact_mod_cast hd
      linarith
    obtain ⟨Cs, -, hS⟩ := S45.s45_static_all hd hs0.le hsd ha hβ
    have hSN := hS N hN
    have hlaw : law P Y = HRS.Whole.canonicalGibbs (HRS.Whole.rieszKernel d ((d : ℝ) / 2)) (HRS.Whole.confinement a) N β :=
      HRS.Whole.S79.s79_law_X_eq hreal (Real.toNNReal t)
    haveI := hSN.prob
    haveI : IsProbabilityMeasure (law P Y) := by rw [hlaw]; exact hSN.prob
    have hexch : HRS.Whole.IsExchangeable (law P Y) := by rw [hlaw]; exact hSN.exch
    have hmean : HRS.Whole.meanEmpirical (law P Y) = HRS.Whole.firstMarginal (law P Y) :=
      HRS.Whole.meanEmpirical_eq_firstMarginal _ hexch hN1
    rw [← hfm, ← hmean]
    ext A hA
    rw [HRS.Whole.meanEmpirical_apply _ hA, Measure.smul_apply, Measure.coe_finset_sum, Finset.sum_apply,
      smul_eq_mul]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Measure.map_apply (hmeas i) hA]
    show P ((fun z => Y z i) ⁻¹' A) = (P.map Y) {X : EucConfig d N | X i ∈ A}
    rw [Measure.map_apply hYm (show MeasurableSet {X : EucConfig d N | X i ∈ A} from
      measurable_pi_apply i hA)]
    rfl
  · -- the L² bound
    have hgL' : MemLp (fun x => g x - 1) 2 (HRS.Whole.withDensityReal ρ) := hgL
    have hint : Integrable (fun x => (g x - 1) ^ 2) (HRS.Whole.withDensityReal ρ) := hgL'.integrable_sq
    have h1 : ∫⁻ x, ‖g x - 1‖ₑ ^ 2 ∂(HRS.Whole.withDensityReal ρ) =
        ENNReal.ofReal (∫ x, (g x - 1) ^ 2 ∂(HRS.Whole.withDensityReal ρ)) := by
      rw [ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => sq_nonneg _)]
      refine lintegral_congr fun x => ?_
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]
    rw [h1]
    refine ENNReal.ofReal_le_ofReal ?_
    have h2 : HRS.Whole.l2Norm (HRS.Whole.withDensityReal ρ) (fun x => g x - 1) =
        Real.sqrt (∫ x, (g x - 1) ^ 2 ∂(HRS.Whole.withDensityReal ρ)) := rfl
    have h3 : 0 ≤ ∫ x, (g x - 1) ^ 2 ∂(HRS.Whole.withDensityReal ρ) :=
      integral_nonneg fun x => sq_nonneg _
    have h4 := hgn
    rw [h2] at h4
    calc ∫ x, (g x - 1) ^ 2 ∂(HRS.Whole.withDensityReal ρ)
        = Real.sqrt (∫ x, (g x - 1) ^ 2 ∂(HRS.Whole.withDensityReal ρ)) ^ 2 := (Real.sq_sqrt h3).symm
      _ ≤ (Cin * deltaN d ((d : ℝ) / 2) N) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h4 2
  · intro f hfm' hf2
    have := hvar f hf2
    have hlin' : (fun ω => linStat f (Y ω)) = fun ω => (N : ℝ)⁻¹ * ∑ i : Fin N, f (Y ω i) :=
      funext fun ω => s86_linStat_eq f hfm' hN1 (Y ω)
    rw [hlin'] at this
    refine this.trans (le_of_eq ?_)
    congr 2

end HRS.MS.FinNoise
