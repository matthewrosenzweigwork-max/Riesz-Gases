import HRS.Sections.QuenchAux5

/-!
# Packet QUENCH (Q27), part 6: abstract Brownian lemma

`gauss_limit`: an a.s. limit of centred Gaussians with convergent variances is Gaussian.
Riemann sums of continuous functions.  Then (next parts) the process
`B_t = (G_t + λ∫_0^t G)/σ` of an OU-type Gaussian process `G` is a Brownian motion.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Qch

/-- An a.s. limit of centred Gaussians with convergent variances is Gaussian. -/
theorem gauss_limit {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {V : ℕ → Ω → ℝ} {W : Ω → ℝ} {v : ℕ → ℝ≥0} {v₀ : ℝ≥0}
    (hV : ∀ n, P.map (V n) = gaussianReal 0 (v n)) (hv : Tendsto v atTop (𝓝 v₀))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun n => V n ω) atTop (𝓝 (W ω)))
    (hW : AEMeasurable W P) (hVm : ∀ n, AEMeasurable (V n) P) :
    P.map W = gaussianReal 0 v₀ := by
  haveI : IsProbabilityMeasure (P.map W) := ⟨by simp [Measure.map_apply_of_aemeasurable hW MeasurableSet.univ]⟩
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [charFun_apply_real, charFun_gaussianReal, integral_map hW (by fun_prop)]
  have h1 : Tendsto (fun n => ∫ ω, Complex.exp (t * V n ω * Complex.I) ∂P) atTop
      (𝓝 (∫ ω, Complex.exp (t * W ω * Complex.I) ∂P)) := by
    refine tendsto_integral_of_dominated_convergence (fun _ => 1) (fun n => ?_) (integrable_const _)
      (fun n => ?_) ?_
    · exact ((Complex.continuous_exp.comp (by fun_prop : Continuous fun x : ℝ => (t : ℂ) * x * Complex.I)).measurable.comp_aemeasurable
        (hVm n)).aestronglyMeasurable
    · refine Eventually.of_forall fun ω => ?_
      have : (t : ℂ) * (V n ω) * Complex.I = ((t * V n ω : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    · filter_upwards [hlim] with ω hω
      exact (Complex.continuous_exp.tendsto _).comp
        (((Complex.continuous_ofReal.tendsto _).comp hω).const_mul (t : ℂ) |>.mul_const Complex.I)
  have h2 : ∀ n, ∫ ω, Complex.exp (t * V n ω * Complex.I) ∂P =
      Complex.exp (-(v n : ℝ) * t ^ 2 / 2) := by
    intro n
    have := charFun_gaussianReal (μ := 0) (v := v n) t
    rw [← hV n, charFun_apply_real, integral_map (hVm n) (by fun_prop)] at this
    rw [this]
    congr 1
    simp
    ring
  simp_rw [h2] at h1
  have h3 : Tendsto (fun n => Complex.exp (-(v n : ℝ) * t ^ 2 / 2)) atTop
      (𝓝 (Complex.exp (-(v₀ : ℝ) * t ^ 2 / 2))) := by
    refine (Complex.continuous_exp.tendsto _).comp ?_
    have : Tendsto (fun n => ((v n : ℝ) : ℂ)) atTop (𝓝 ((v₀ : ℝ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp (NNReal.tendsto_coe.2 hv)
    have h4 := (this.neg.mul_const ((t : ℂ) ^ 2)).div_const 2
    simpa using h4
  have := tendsto_nhds_unique h1 h3
  rw [this]
  congr 1
  simp
  ring

/-- Riemann sums of a continuous function converge: `h ∑_{k<⌊t/h⌋} g(kh) → ∫_0^t g`, `h = 1/(n+1)`. -/
theorem riemann_sum {g : ℝ → ℝ} (hg : Continuous g) {t : ℝ} (ht : 0 ≤ t) :
    Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1)) *
      ∑ k ∈ Finset.range ⌊t * ((n : ℝ) + 1)⌋₊, g ((k : ℝ) / ((n : ℝ) + 1))) atTop
      (𝓝 (∫ u in Set.Icc (0 : ℝ) t, g u)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ u ∈ Set.Icc (0 : ℝ) (t + 1), |g u| ≤ M := by
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t + 1)).exists_bound_of_continuousOn hg.continuousOn
    exact ⟨M, fun u hu => by simpa using hM u hu⟩
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM 0 ⟨le_rfl, by linarith⟩)
  have huc : UniformContinuousOn g (Set.Icc (0 : ℝ) (t + 1)) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hg.continuousOn
  have hε' : 0 < ε / (2 * (t + 1)) := by positivity
  obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuousOn_iff.1 huc (ε / (2 * (t + 1))) hε'
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (max (1 / δ) (2 * (M + 1) / ε))
  refine ⟨n₀, fun n hn => ?_⟩
  set h : ℝ := 1 / ((n : ℝ) + 1) with hh
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hhpos : 0 < h := by positivity
  have hhn : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hhδ : h < δ := by
    have : 1 / δ < (n : ℝ) + 1 := by
      have := (le_max_left (1 / δ) (2 * (M + 1) / ε)).trans_lt hn₀
      linarith
    rw [hh, div_lt_iff₀ hn1]
    rw [div_lt_iff₀ hδ] at this
    linarith
  have hhM : h * (2 * (M + 1)) < ε := by
    have : 2 * (M + 1) / ε < (n : ℝ) + 1 := by
      have := (le_max_right (1 / δ) (2 * (M + 1) / ε)).trans_lt hn₀
      linarith
    rw [div_lt_iff₀ hε] at this
    rw [hh, one_div, inv_mul_lt_iff₀ hn1]
    linarith
  set N : ℕ := ⌊t * ((n : ℝ) + 1)⌋₊ with hN
  have hNle : (N : ℝ) * h ≤ t := by
    have h1 : (N : ℝ) ≤ t * ((n : ℝ) + 1) := Nat.floor_le (by positivity)
    rw [hh, ← div_eq_mul_one_div, div_le_iff₀ hn1]
    linarith
  have hNlt : t < ((N : ℝ) + 1) * h := by
    have h1 : t * ((n : ℝ) + 1) < (N : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [hh, ← div_eq_mul_one_div, lt_div_iff₀ hn1]
    linarith
  have hNh0 : 0 ≤ (N : ℝ) * h := by positivity
  have hkh : ∀ k : ℕ, k ≤ N → (k : ℝ) * h ≤ t := fun k hk =>
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hk) hhpos.le).trans hNle
  -- the integral over `[0, Nh]`
  have hint : ∀ a b : ℝ, IntervalIntegrable g volume a b := fun a b => hg.intervalIntegrable a b
  have hsplit : ∫ u in (0 : ℝ)..(N : ℝ) * h, g u =
      ∑ k ∈ Finset.range N, ∫ u in ((k : ℝ) * h)..(((k + 1 : ℕ) : ℝ) * h), g u := by
    have := intervalIntegral.sum_integral_adjacent_intervals (f := g) (μ := volume)
      (a := fun k : ℕ => (k : ℝ) * h) (n := N) (fun k _ => hint _ _)
    simpa using this.symm
  have hterm : ∀ k ∈ Finset.range N, |h * g ((k : ℝ) * h) - ∫ u in ((k : ℝ) * h)..(((k + 1 : ℕ) : ℝ) * h), g u| ≤
      h * (ε / (2 * (t + 1))) := by
    intro k hk
    have hk' : k < N := Finset.mem_range.1 hk
    have hk1 : ((k + 1 : ℕ) : ℝ) * h ≤ t := hkh (k + 1) hk'
    have hconst : ∫ u in ((k : ℝ) * h)..(((k + 1 : ℕ) : ℝ) * h), g ((k : ℝ) * h) = h * g ((k : ℝ) * h) := by
      rw [intervalIntegral.integral_const]
      simp only [smul_eq_mul]
      push_cast
      ring
    have hdiff : h * g ((k : ℝ) * h) - ∫ u in ((k : ℝ) * h)..(((k + 1 : ℕ) : ℝ) * h), g u =
        ∫ u in ((k : ℝ) * h)..(((k + 1 : ℕ) : ℝ) * h), (g ((k : ℝ) * h) - g u) := by
      rw [intervalIntegral.integral_sub intervalIntegrable_const (hint _ _), hconst]
    rw [hdiff]
    have hle : ((k : ℝ) * h) ≤ (((k + 1 : ℕ) : ℝ) * h) := by
      push_cast; nlinarith
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (k : ℝ) * h)
      (b := ((k + 1 : ℕ) : ℝ) * h) (C := ε / (2 * (t + 1))) (f := fun u => g ((k : ℝ) * h) - g u) (by
        intro u hu
        rw [Set.uIoc_of_le hle] at hu
        have hu0 : 0 ≤ (k : ℝ) * h := by positivity
        have hk0 : (k : ℝ) * h ∈ Set.Icc (0 : ℝ) (t + 1) := ⟨hu0, by linarith [hkh k hk'.le]⟩
        have hu1 : u ∈ Set.Icc (0 : ℝ) (t + 1) := ⟨hu0.trans hu.1.le, by linarith [hu.2]⟩
        have := hδg _ hk0 _ hu1 (by
          rw [Real.dist_eq, abs_lt]
          push_cast at hu
          constructor <;> nlinarith [hu.1, hu.2])
        rw [Real.dist_eq] at this
        simpa [Real.norm_eq_abs] using this.le)
    refine this.trans ?_
    rw [abs_of_nonneg (by linarith : 0 ≤ ((k + 1 : ℕ) : ℝ) * h - (k : ℝ) * h)]
    push_cast
    nlinarith
  -- the Riemann sum versus the integral to `Nh`
  have hRS : |h * ∑ k ∈ Finset.range N, g ((k : ℝ) / ((n : ℝ) + 1)) - ∫ u in (0 : ℝ)..(N : ℝ) * h, g u| ≤
      (N : ℝ) * h * (ε / (2 * (t + 1))) := by
    rw [hsplit, Finset.mul_sum, ← Finset.sum_sub_distrib]
    have e : ∀ k : ℕ, g ((k : ℝ) / ((n : ℝ) + 1)) = g ((k : ℝ) * h) := fun k => by
      rw [hh, div_eq_mul_one_div]
    simp_rw [e]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum hterm).trans ?_
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    nlinarith [hhpos]
  -- the tail integral
  have htail : |∫ u in (N : ℝ) * h..t, g u| ≤ M * h := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (N : ℝ) * h) (b := t) (C := M)
      (f := g) (by
        intro u hu
        rw [Set.uIoc_of_le hNle] at hu
        exact by simpa [Real.norm_eq_abs] using hM u ⟨hNh0.trans hu.1.le, by linarith [hu.2]⟩)
    rw [Real.norm_eq_abs] at this
    refine this.trans ?_
    rw [abs_of_nonneg (by linarith)]
    nlinarith [hNlt]
  have hIcc : ∫ u in Set.Icc (0 : ℝ) t, g u = ∫ u in (0 : ℝ)..t, g u := by
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht]
  have hsplit2 : ∫ u in (0 : ℝ)..t, g u = (∫ u in (0 : ℝ)..(N : ℝ) * h, g u) + ∫ u in (N : ℝ) * h..t, g u :=
    (intervalIntegral.integral_add_adjacent_intervals (hint 0 ((N : ℝ) * h)) (hint ((N : ℝ) * h) t)).symm
  rw [Real.dist_eq, hIcc, hsplit2]
  have key : h * ∑ k ∈ Finset.range N, g ((k : ℝ) / ((n : ℝ) + 1)) -
      ((∫ u in (0 : ℝ)..(N : ℝ) * h, g u) + ∫ u in (N : ℝ) * h..t, g u) =
      (h * ∑ k ∈ Finset.range N, g ((k : ℝ) / ((n : ℝ) + 1)) - ∫ u in (0 : ℝ)..(N : ℝ) * h, g u) -
        ∫ u in (N : ℝ) * h..t, g u := by ring
  rw [key]
  refine (abs_sub _ _).trans_lt ?_
  have h1 : (N : ℝ) * h * (ε / (2 * (t + 1))) ≤ ε / 2 := by
    have : (N : ℝ) * h ≤ t + 1 := by linarith
    calc (N : ℝ) * h * (ε / (2 * (t + 1))) ≤ (t + 1) * (ε / (2 * (t + 1))) := by
          apply mul_le_mul_of_nonneg_right this hε'.le
      _ = ε / 2 := by field_simp
  have h2 : M * h < ε / 2 := by
    nlinarith [hhM, hM0, hhpos]
  have e1 : h * ∑ k ∈ Finset.range ⌊t * ((n : ℝ) + 1)⌋₊, g ((k : ℝ) / ((n : ℝ) + 1)) =
      h * ∑ k ∈ Finset.range N, g ((k : ℝ) / ((n : ℝ) + 1)) := rfl
  linarith [hRS, htail]

end Qch

end HRS
