import HRS.MS.SpecAux69

/-!
# S8L: integration of the Herbst inequality and the `L¹ → L²` bound (S8.7, block L)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_herbst`: a positive `C¹` subsolution `s` (`S8pSubsol`) with `∫ s = 1`
of a probability measure `μ` with log-Sobolev constant `C` has `s ∈ L²(μ)` and
`∫ s² ≤ exp ((2C/3)(a + b (3 H4/2 + 9/4)))`.
-/

noncomputable section

open MeasureTheory Set Real Filter Topology

namespace HRS.MS.Spec

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} {s h : E → ℝ} {s0 a b H4 C : ℝ}

/-- Bound at fixed truncation `ε`: `Φ_ε(2) ≤ exp K`. -/
theorem s8p_herbst_eps [IsProbabilityMeasure μ] (hyp : S8pSubsol μ s h s0 a b H4)
    (hLSI : s8p_LSI μ C) (hC : 0 ≤ C) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∫ x, s8p_U2 2 ε (s x) ∂μ ≤ Real.exp ((2 * C / 3) * (a + b * (3 * H4 / 2 + 9 / 4))) := by
  set K := (2 * C / 3) * (a + b * (3 * H4 / 2 + 9 / 4)) with hK
  have hs0 := hyp.s0_pos
  have hsm : Measurable s := hyp.cont.continuous.measurable
  set Φ : ℝ → ℝ := fun q => ∫ x, s8p_U2 q ε (s x) ∂μ with hΦ
  set Dq : ℝ → ℝ := fun q => ∫ x, s8p_U2 q ε (s x) * Real.log (s8p_hm ε (s x)) ∂μ with hDq
  have hderiv : ∀ q, HasDerivAt Φ (Dq q) q := fun q =>
    s8p_Phi_hasDerivAt hε hs0 hsm hyp.int hyp.ge q
  have hge : ∀ q ∈ Icc (1 : ℝ) 2, 1 / 6 ≤ Φ q := fun q hq =>
    s8p_Phi_ge hyp hε hε1 hq.1 hq.2
  have hpos : ∀ q ∈ Icc (1 : ℝ) 2, 0 < Φ q := fun q hq => lt_of_lt_of_le (by norm_num) (hge q hq)
  have hdi : ∀ q ∈ Icc (1 : ℝ) 2, q * Dq q ≤ Φ q * (Real.log (Φ q) + K) := fun q hq =>
    s8p_diff_ineq hyp hLSI hC hε hε1 hq.1 hq.2
  have hΦ1 : Φ 1 = 1 := by
    simp only [hΦ]
    have : ∀ x, s8p_U2 1 ε (s x) = s x := fun x => by
      simp [s8p_U2, s8p_G]
    simp [this, hyp.one]
  -- χ(q) = (log Φ(q) + K)/q is antitone on [1,2]
  set χ : ℝ → ℝ := fun q => (Real.log (Φ q) + K) / q with hχ
  have hχd : ∀ q ∈ Icc (1 : ℝ) 2,
      HasDerivAt χ ((Dq q / Φ q * q - (Real.log (Φ q) + K)) / q ^ 2) q := by
    intro q hq
    have hq0 : q ≠ 0 := by have := hq.1; positivity
    have h1 := ((hderiv q).log (hpos q hq).ne').add_const K
    have h2 := h1.div (hasDerivAt_id q) hq0
    have e : χ = (fun x => Real.log (Φ x) + K) / id := by funext x; simp [hχ]
    rw [e]
    convert h2 using 1
    simp
  have hanti : AntitoneOn χ (Icc 1 2) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 1 2) ?_ ?_ ?_
    · exact fun q hq => (hχd q hq).continuousAt.continuousWithinAt
    · intro q hq
      rw [interior_Icc] at hq
      exact (hχd q ⟨hq.1.le, hq.2.le⟩).differentiableAt.differentiableWithinAt
    · intro q hq
      rw [interior_Icc] at hq
      have hq' : q ∈ Icc (1 : ℝ) 2 := ⟨hq.1.le, hq.2.le⟩
      rw [(hχd q hq').deriv]
      have hqpos : 0 < q := by linarith [hq.1]
      have hP := hpos q hq'
      have h2 := hdi q hq'
      apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      have : Dq q / Φ q * q ≤ Real.log (Φ q) + K := by
        rw [div_mul_eq_mul_div, div_le_iff₀ hP]
        nlinarith
      linarith
  have h12 := hanti ⟨le_rfl, by norm_num⟩ ⟨by norm_num, le_rfl⟩ (by norm_num : (1 : ℝ) ≤ 2)
  simp only [hχ, hΦ1, Real.log_one] at h12
  have h2 : Real.log (Φ 2) ≤ K := by
    have : (Real.log (Φ 2) + K) / 2 ≤ K := by simpa using h12
    linarith
  calc Φ 2 = Real.exp (Real.log (Φ 2)) := (Real.exp_log (hpos 2 ⟨by norm_num, le_rfl⟩)).symm
    _ ≤ Real.exp K := Real.exp_le_exp.2 h2


theorem s8p_U2_two (ε t : ℝ) : s8p_U2 2 ε t = t * s8p_hm ε t := by
  unfold s8p_U2 s8p_G
  norm_num

/-- **Herbst bound**: `∫ s² ≤ exp K` for a positive subsolution with `∫ s = 1`. -/
theorem s8p_herbst [IsProbabilityMeasure μ] (hyp : S8pSubsol μ s h s0 a b H4)
    (hLSI : s8p_LSI μ C) (hC : 0 ≤ C) :
    Integrable (fun x => s x ^ 2) μ ∧
      ∫ x, s x ^ 2 ∂μ ≤ Real.exp ((2 * C / 3) * (a + b * (3 * H4 / 2 + 9 / 4))) := by
  set K := (2 * C / 3) * (a + b * (3 * H4 / 2 + 9 / 4)) with hK
  have hs0 := hyp.s0_pos
  have hsm : Measurable s := hyp.cont.continuous.measurable
  have hpos : ∀ x, 0 < s x := fun x => lt_of_lt_of_le hs0 (hyp.ge x)
  set εn : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hεn
  have hεn0 : ∀ n, 0 < εn n := fun n => by simp only [hεn]; positivity
  have hεn1 : ∀ n, εn n ≤ 1 := fun n => by
    simp only [hεn]; rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  set F : ℕ → E → ENNReal := fun n x => ENNReal.ofReal (s8p_U2 2 (εn n) (s x)) with hF
  have hFm : ∀ n, Measurable (F n) := fun n => by
    simp only [hF, s8p_U2_two, s8p_hm]
    fun_prop
  have hFint : ∀ n, ∫⁻ x, F n x ∂μ ≤ ENNReal.ofReal (Real.exp K) := fun n => by
    simp only [hF]
    rw [← ofReal_integral_eq_lintegral_ofReal (s8p_U2_integrable 2 (hεn0 n) hs0 hsm hyp.int hyp.ge)
      (Filter.Eventually.of_forall fun x => (s8p_U2_pos (hεn0 n).le (hpos x)).le)]
    exact ENNReal.ofReal_le_ofReal (s8p_herbst_eps hyp hLSI hC (hεn0 n) (hεn1 n))
  have hmono : ∀ x, Monotone fun n => F n x := fun x n m hnm => by
    simp only [hF, s8p_U2_two]
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (hpos x).le
    unfold s8p_hm
    have h1 : εn m ≤ εn n := by
      simp only [hεn]
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast (by linarith [(Nat.cast_le (α := ℝ)).2 hnm]))
    rw [div_le_div_iff₀ (by have := hεn0 n; have := hpos x; positivity)
      (by have := hεn0 m; have := hpos x; positivity)]
    nlinarith [mul_pos (hpos x) (hpos x), mul_nonneg (sub_nonneg.2 h1) (mul_pos (hpos x) (hpos x)).le]
  have hlim : ∀ x, Tendsto (fun n => F n x) atTop (nhds (ENNReal.ofReal (s x ^ 2))) := fun x => by
    simp only [hF, s8p_U2_two, s8p_hm]
    apply ENNReal.tendsto_ofReal
    have h1 : Tendsto (fun n : ℕ => εn n) atTop (nhds 0) := by
      simp only [hεn]; exact tendsto_one_div_add_atTop_nhds_zero_nat
    have h2 : Tendsto (fun n : ℕ => s x * (s x / (1 + εn n * s x))) atTop
        (nhds (s x * (s x / (1 + 0 * s x)))) := by
      apply Tendsto.const_mul
      apply Tendsto.div tendsto_const_nhds (tendsto_const_nhds.add (h1.mul_const _))
      simp
    simpa [sq] using h2
  have hL := lintegral_tendsto_of_tendsto_of_monotone (μ := μ) (fun n => (hFm n).aemeasurable)
    (Filter.Eventually.of_forall hmono) (Filter.Eventually.of_forall hlim)
  have hle : ∫⁻ x, ENNReal.ofReal (s x ^ 2) ∂μ ≤ ENNReal.ofReal (Real.exp K) :=
    le_of_tendsto' hL hFint
  have hsq : Measurable fun x => s x ^ 2 := hsm.pow_const 2
  have hint : Integrable (fun x => s x ^ 2) μ := by
    refine ⟨hsq.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => sq_nonneg (s x))]
    exact lt_of_le_of_lt hle ENNReal.ofReal_lt_top
  refine ⟨hint, ?_⟩
  rw [← ENNReal.ofReal_le_ofReal_iff (Real.exp_pos K).le,
    ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall fun x => sq_nonneg (s x))]
  exact hle

end HRS.MS.Spec
