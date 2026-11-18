import HRS.Commutator.Whole.PRODAux2

/-!
# CMX-PROD helper file 3: the `L^p` approximate identity for the mollifier
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff Convolution

noncomputable section

namespace HRS.Commutator.Whole.PROD

open HRS HRS.Whole HRS.Commutator.Whole

variable {d : ℕ}

/-- Dominated convergence for `L^p` norms, with a bound supported in a ball. -/
lemma prod_tendsto_eLpNorm_of_dominated {p : ℝ} (hp : 0 < p) {F : ℕ → Euc d → ℂ}
    (hF : ∀ n, AEStronglyMeasurable (F n) volume) (R c : ℝ)
    (hb : ∀ n y, ‖F n y‖ ≤ if ‖y‖ ≤ R then c else 0)
    (hlim : ∀ y, Tendsto (fun n => F n y) atTop (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
  have hpne : ENNReal.ofReal p ≠ 0 := by simpa using hp
  have hpt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal hp.le
  have key : Tendsto (fun n => ∫⁻ y, ‖F n y‖ₑ ^ p) atTop (𝓝 0) := by
    have hbd : ∫⁻ y, (closedBall (0 : Euc d) R).indicator (fun _ => ENNReal.ofReal c ^ p) y ≠ ⊤ := by
      rw [lintegral_indicator_const measurableSet_closedBall]
      exact ENNReal.mul_ne_top (ENNReal.rpow_lt_top_of_nonneg hp.le ENNReal.ofReal_ne_top).ne
        measure_closedBall_lt_top.ne
    have := tendsto_lintegral_of_dominated_convergence'
      (μ := volume) (F := fun n y => ‖F n y‖ₑ ^ p) (f := fun _ => (0 : ℝ≥0∞))
      (fun y => (closedBall (0 : Euc d) R).indicator (fun _ => ENNReal.ofReal c ^ p) y)
      (fun n => ((hF n).enorm).pow_const p)
      (fun n => Filter.Eventually.of_forall fun y => ?_) hbd
      (Filter.Eventually.of_forall fun y => ?_)
    · simpa using this
    · dsimp only
      by_cases hy : ‖y‖ ≤ R
      · have h1 : ‖F n y‖ ≤ c := by simpa [hy] using hb n y
        rw [Set.indicator_of_mem (mem_closedBall_zero_iff.2 hy)]
        refine ENNReal.rpow_le_rpow ?_ hp.le
        rw [← ofReal_norm_eq_enorm]
        exact ENNReal.ofReal_le_ofReal h1
      · have h1 : ‖F n y‖ ≤ 0 := by simpa [hy] using hb n y
        have h2 : F n y = 0 := norm_le_zero_iff.1 h1
        rw [h2]
        simp [ENNReal.zero_rpow_of_pos hp]
    · have h1 : Tendsto (fun n => ‖F n y‖ₑ) atTop (𝓝 ‖(0 : ℂ)‖ₑ) := (hlim y).enorm
      simp only [enorm_zero] at h1
      have h2 := ((ENNReal.continuous_rpow_const (y := p)).tendsto 0).comp h1
      rw [ENNReal.zero_rpow_of_pos hp] at h2
      exact h2
  have h3 : Tendsto (fun n => (∫⁻ y, ‖F n y‖ₑ ^ p) ^ (1 / p)) atTop (𝓝 0) := by
    have h2 := ((ENNReal.continuous_rpow_const (y := 1 / p)).tendsto 0).comp key
    rw [ENNReal.zero_rpow_of_pos (one_div_pos.2 hp)] at h2
    exact h2
  refine h3.congr (fun n => ?_)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpne hpt (hF n), hpr]

/-- The approximate identity for continuous compactly supported functions. -/
lemma prod_ker_conv_Lp_cc {p : ℝ} (hp : 0 < p) {g : Euc d → ℂ} (hg : Continuous g)
    (hgc : HasCompactSupport g) :
    Tendsto (fun n => eLpNorm (fun y => prod_conv (prod_ker d n) g y - g y) (ENNReal.ofReal p) volume)
      atTop (𝓝 0) := by
  obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall (0 : Euc d)
  obtain ⟨M, hM⟩ := hg.bounded_above_of_compact_support hgc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  have hconv_zero : ∀ n (y : Euc d), R + 1 < ‖y‖ → prod_conv (prod_ker d n) g y = 0 := by
    intro n y hy
    unfold prod_conv
    refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only [Pi.zero_apply]
    by_cases ht : 1 / ((n : ℝ) + 1) ≤ ‖t‖
    · rw [prod_ker_apply, prod_kerR_zero ht]; simp
    · push Not at ht
      have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one (by positivity)]; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
      have h2 : R < ‖y - t‖ := by
        have := norm_sub_norm_le y t
        linarith
      have h3 : g (y - t) = 0 := by
        by_contra hne
        have : y - t ∈ tsupport g := subset_tsupport _ hne
        have := mem_closedBall_zero_iff.1 (hR this)
        linarith
      rw [h3, mul_zero]
  have hconv_bd : ∀ n (y : Euc d), ‖prod_conv (prod_ker d n) g y‖ ≤ M := by
    intro n y
    unfold prod_conv
    have hint : Integrable (fun t => ‖prod_ker d n t‖ * M) := (prod_ker d n).integrable.norm.mul_const M
    refine (norm_integral_le_of_norm_le hint (Filter.Eventually.of_forall fun t => ?_)).trans ?_
    · rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hM _) (norm_nonneg _)
    · rw [integral_mul_const, prod_ker_norm_integral, one_mul]
  refine prod_tendsto_eLpNorm_of_dominated hp (F := fun n y => prod_conv (prod_ker d n) g y - g y)
    (fun n => (prod_aesm_conv (prod_ker d n).continuous.aestronglyMeasurable
      hg.aestronglyMeasurable).sub hg.aestronglyMeasurable) (R + 1) (2 * M) ?_ ?_
  · intro n y
    by_cases hy : ‖y‖ ≤ R + 1
    · rw [if_pos hy]
      calc ‖prod_conv (prod_ker d n) g y - g y‖ ≤ ‖prod_conv (prod_ker d n) g y‖ + ‖g y‖ :=
            norm_sub_le _ _
        _ ≤ M + M := add_le_add (hconv_bd n y) (hM y)
        _ = 2 * M := by ring
    · rw [if_neg hy]
      push Not at hy
      have h1 := hconv_zero n y hy
      have h2 : g y = 0 := by
        by_contra hne
        have := mem_closedBall_zero_iff.1 (hR (subset_tsupport _ hne))
        linarith
      simp [h1, h2]
  · intro y
    have := (prod_conv_ker_tendsto hg y).sub_const (g y)
    simpa using this

/-- The approximate identity in `L^p`, `1 < p < ∞`. -/
theorem prod_ker_conv_Lp {p : ℝ} (hp : 1 < p) {h : Euc d → ℂ}
    (hh : MemLp h (ENNReal.ofReal p) volume) :
    Tendsto (fun n => eLpNorm (fun y => prod_conv (prod_ker d n) h y - h y) (ENNReal.ofReal p) volume)
      atTop (𝓝 0) := by
  have hp0 : 0 < p := by linarith
  have hP1 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp.le
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  by_cases hεt : ε = ⊤
  · exact ⟨0, fun n _ => by simp [hεt]⟩
  have hδ : ε / 3 ≠ 0 := by
    intro h0
    rw [ENNReal.div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · exact hε.ne' h0
    · simp at h0
  obtain ⟨g, hgc, hgd, hgcont, hgm⟩ := hh.exists_hasCompactSupport_eLpNorm_sub_le
    (μ := (volume : Measure (Euc d))) ENNReal.ofReal_ne_top hδ
  obtain ⟨N, hN⟩ := (ENNReal.tendsto_atTop_zero.1 (prod_ker_conv_Lp_cc hp0 hgcont hgc)) (ε / 3)
    (pos_iff_ne_zero.2 hδ)
  refine ⟨N, fun n hn => ?_⟩
  have hKm : AEStronglyMeasurable (prod_ker d n : Euc d → ℂ) volume :=
    (prod_ker d n).continuous.aestronglyMeasurable
  have hsub := prod_conv_sub (prod_ker d n) hp hh hgm
  have e : (fun y => prod_conv (prod_ker d n) h y - h y) =
      (fun y => (prod_conv (prod_ker d n) h y - prod_conv (prod_ker d n) g y) +
        (prod_conv (prod_ker d n) g y - g y)) + (fun y => g y - h y) := by
    funext y; simp
  have hA : AEStronglyMeasurable (fun y => prod_conv (prod_ker d n) h y -
      prod_conv (prod_ker d n) g y) volume :=
    (prod_aesm_conv hKm hh.aestronglyMeasurable).sub (prod_aesm_conv hKm hgm.aestronglyMeasurable)
  have hB : AEStronglyMeasurable (fun y => prod_conv (prod_ker d n) g y - g y) volume :=
    (prod_aesm_conv hKm hgm.aestronglyMeasurable).sub hgm.aestronglyMeasurable
  have hC : AEStronglyMeasurable (fun y => g y - h y) volume :=
    hgm.aestronglyMeasurable.sub hh.aestronglyMeasurable
  have h1 : eLpNorm (fun y => prod_conv (prod_ker d n) h y - prod_conv (prod_ker d n) g y)
      (ENNReal.ofReal p) volume ≤ ε / 3 := by
    have e1 : (fun y => prod_conv (prod_ker d n) h y - prod_conv (prod_ker d n) g y) =
        prod_conv (prod_ker d n) (h - g) := (prod_conv_sub (prod_ker d n) hp hh hgm).symm
    rw [e1]
    refine (prod_eLpNorm_conv_le hp (prod_ker d n).integrable
      (hh.aestronglyMeasurable.sub hgm.aestronglyMeasurable)).trans ?_
    rw [prod_ker_norm_integral, ENNReal.ofReal_one, one_mul]
    exact hgd
  have h3 : eLpNorm (fun y => g y - h y) (ENNReal.ofReal p) volume ≤ ε / 3 := by
    have : (fun y => g y - h y) = -(h - g) := by funext y; simp
    rw [this, eLpNorm_neg]
    exact hgd
  rw [e]
  calc eLpNorm ((fun y => (prod_conv (prod_ker d n) h y - prod_conv (prod_ker d n) g y) +
        (prod_conv (prod_ker d n) g y - g y)) + (fun y => g y - h y)) (ENNReal.ofReal p) volume
      ≤ eLpNorm (fun y => (prod_conv (prod_ker d n) h y - prod_conv (prod_ker d n) g y) +
        (prod_conv (prod_ker d n) g y - g y)) (ENNReal.ofReal p) volume +
        eLpNorm (fun y => g y - h y) (ENNReal.ofReal p) volume :=
        eLpNorm_add_le hP1
    _ ≤ (eLpNorm (fun y => prod_conv (prod_ker d n) h y - prod_conv (prod_ker d n) g y)
          (ENNReal.ofReal p) volume + eLpNorm (fun y => prod_conv (prod_ker d n) g y - g y)
          (ENNReal.ofReal p) volume) + eLpNorm (fun y => g y - h y) (ENNReal.ofReal p) volume := by
        gcongr
        exact eLpNorm_add_le hP1
    _ ≤ (ε / 3 + ε / 3) + ε / 3 := by
        gcongr
        exact hN n hn
    _ = ε := ENNReal.add_thirds ε

end HRS.Commutator.Whole.PROD
