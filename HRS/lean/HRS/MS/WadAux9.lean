import HRS.MS.WadAux4

/-!
# S8.3, packet D3 (part 1): the far-field norm of the Mehler semigroup

`s83_tail_ratio`: for `0 < c ≤ 1`, `|σ| ≤ σ₀`, `M ≥ 0`: `⟨x⟩^{-M} ∫ ⟨cx+σz⟩^M dγ(z) → c^M` as `x → ∞`.
`s83_tail_bound`: consequently, for every `ε > 0` there is `R` such that for `‖x‖ ≥ R` and every continuous `f`
with `‖f‖_M ≤ C`: `‖G_{c,σ} f (x)‖ ≤ C (c^M + ε) ⟨x⟩^M`; i.e. `‖(1-χ_R) P_t‖_{C_M → C_M} ≤ e^{-aMt} + ε`
(`s83_P_tail_bound`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

/-- `⟨·⟩` is `1`-Lipschitz. -/
theorem s83_jb_lipschitz (y y' : Euc d) : |jbracket y - jbracket y'| ≤ ‖y - y'‖ := by
  have key : ∀ u v : Euc d, jbracket u ≤ jbracket v + ‖u - v‖ := by
    intro u v
    have h1 : ‖u‖ ≤ ‖v‖ + ‖u - v‖ := by
      have := norm_le_norm_add_norm_sub' u v
      linarith
    refine s83_le_of_sq_le (by have := s83_jb_pos v; positivity) ?_
    rw [s83_jb_sq u]
    have h2 := s83_jb_sq v
    have hjv := s83_jb_pos v
    have hn := norm_nonneg (u - v)
    have hnv := norm_nonneg v
    have : ‖u‖ ^ 2 ≤ (‖v‖ + ‖u - v‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [s83_norm_le_jb v, mul_nonneg hn hjv.le]
  rw [abs_le]
  constructor
  · have := key y' y
    rw [norm_sub_rev] at this
    linarith
  · have := key y y'
    linarith

theorem s83_jb_smul_ratio {c : ℝ} (hc0 : 0 < c) (hc : c ≤ 1) (x : Euc d) :
    |jbracket (c • x) - c * jbracket x| ≤ 1 := by
  have h1 : (jbracket (c • x)) ^ 2 = 1 + c ^ 2 * ‖x‖ ^ 2 := by
    rw [s83_jb_sq, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  have h2 : (c * jbracket x) ^ 2 = c ^ 2 + c ^ 2 * ‖x‖ ^ 2 := by
    rw [mul_pow, s83_jb_sq]; ring
  have hA := s83_jb_pos (c • x)
  have hB : 0 < c * jbracket x := mul_pos hc0 (s83_jb_pos x)
  have hc2 : c ^ 2 ≤ 1 := by nlinarith
  rw [abs_le]
  constructor
  · -- `c jb(x) ≤ jb(cx) + 1`
    have : (c * jbracket x) ^ 2 ≤ (jbracket (c • x) + 1) ^ 2 := by
      nlinarith
    have := s83_le_of_sq_le (by linarith) this
    linarith
  · -- `jb(cx) ≤ c jb(x) + 1`
    have : (jbracket (c • x)) ^ 2 ≤ (c * jbracket x + 1) ^ 2 := by
      nlinarith
    have := s83_le_of_sq_le (by linarith) this
    linarith

theorem s83_jb_tendsto_atTop : Tendsto (fun x : Euc d => jbracket x) (cocompact (Euc d)) atTop :=
  tendsto_atTop_mono (fun x => s83_norm_le_jb x) tendsto_norm_cocompact_atTop

/-- `⟨cx + σz⟩ / ⟨x⟩ → c` as `x → ∞`. -/
theorem s83_ratio_tendsto {c : ℝ} (hc0 : 0 < c) (hc : c ≤ 1) (σ : ℝ) (z : Euc d) :
    Tendsto (fun x : Euc d => jbracket (c • x + σ • z) / jbracket x) (cocompact (Euc d)) (𝓝 c) := by
  have hKz : ∀ x : Euc d, |jbracket (c • x + σ • z) - c * jbracket x| ≤ |σ| * ‖z‖ + 1 := by
    intro x
    have h1 := s83_jb_lipschitz (c • x + σ • z) (c • x)
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs] at h1
    have h2 := s83_jb_smul_ratio hc0 hc x
    calc |jbracket (c • x + σ • z) - c * jbracket x|
        = |(jbracket (c • x + σ • z) - jbracket (c • x)) + (jbracket (c • x) - c * jbracket x)| := by
          ring_nf
      _ ≤ |jbracket (c • x + σ • z) - jbracket (c • x)| + |jbracket (c • x) - c * jbracket x| :=
          abs_add_le _ _
      _ ≤ |σ| * ‖z‖ + 1 := add_le_add h1 h2
  have hbd : Tendsto (fun x : Euc d => (|σ| * ‖z‖ + 1) / jbracket x) (cocompact (Euc d)) (𝓝 0) :=
    tendsto_const_nhds.div_atTop s83_jb_tendsto_atTop
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun x => dist_nonneg) (fun x => ?_) hbd
  rw [Real.dist_eq]
  have hp := s83_jb_pos x
  have : jbracket (c • x + σ • z) / jbracket x - c =
      (jbracket (c • x + σ • z) - c * jbracket x) / jbracket x := by
    field_simp
  rw [this, abs_div, abs_of_pos hp]
  exact div_le_div_of_nonneg_right (hKz x) hp.le

/-- **Far-field ratio.** -/
theorem s83_tail_ratio {M : ℝ} (hM : 0 ≤ M) {c σ σ₀ : ℝ} (hc0 : 0 < c) (hc : c ≤ 1)
    (hσ : |σ| ≤ σ₀) :
    Tendsto (fun x : Euc d => (∫ z, jbracket (c • x + σ • z) ^ M ∂(stdGaussian (Euc d))) /
      jbracket x ^ M) (cocompact (Euc d)) (𝓝 (c ^ M)) := by
  haveI := s83_cocompact_cg d
  have hmain : Tendsto (fun x : Euc d => ∫ z, jbracket (c • x + σ • z) ^ M / jbracket x ^ M
      ∂(stdGaussian (Euc d))) (cocompact (Euc d)) (𝓝 (∫ _ : Euc d, c ^ M ∂(stdGaussian (Euc d)))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (bound := fun z : Euc d => 2 ^ M * jbracket (σ • z) ^ M) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun x => ?_
      have : Continuous fun z : Euc d => jbracket (c • x + σ • z) ^ M / jbracket x ^ M := by
        refine Continuous.div_const ?_ _
        unfold jbracket
        exact Continuous.rpow_const (by fun_prop) fun z => Or.inl (by
          have := (s83_jb_pos (c • x + σ • z)).ne'; unfold jbracket at this; exact this)
      exact this.aestronglyMeasurable
    · refine Eventually.of_forall fun x => Eventually.of_forall fun z => ?_
      have hp : 0 < jbracket x ^ M := Real.rpow_pos_of_pos (s83_jb_pos x) _
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _) hp.le), div_le_iff₀ hp]
      have h1 := s83_jb_add_rpow hM (c • x) (σ • z)
      have h2 : jbracket (c • x) ^ M ≤ jbracket x ^ M :=
        s83_jb_smul_le_rpow hM (by rw [abs_of_pos hc0]; exact hc) x
      have h3 : 0 ≤ jbracket (σ • z) ^ M := Real.rpow_nonneg (s83_jb_pos _).le _
      calc jbracket (c • x + σ • z) ^ M ≤ 2 ^ M * (jbracket (c • x) ^ M * jbracket (σ • z) ^ M) := h1
        _ ≤ 2 ^ M * (jbracket x ^ M * jbracket (σ • z) ^ M) := by
            gcongr
        _ = 2 ^ M * jbracket (σ • z) ^ M * jbracket x ^ M := by ring
    · exact (s83_int_jb_smul (M := M) hM hσ).const_mul _
    · refine Eventually.of_forall fun z => ?_
      have := (s83_ratio_tendsto hc0 hc σ z).rpow_const (p := M) (Or.inr hM)
      refine this.congr fun x => ?_
      rw [Real.div_rpow (s83_jb_pos _).le (s83_jb_pos x).le]
  rw [integral_const] at hmain
  simp only [probReal_univ, one_smul] at hmain
  refine hmain.congr fun x => ?_
  have hp : 0 < jbracket x ^ M := Real.rpow_pos_of_pos (s83_jb_pos x) _
  rw [integral_div]

/-- **Far-field bound** for the Gaussian average: for `ε > 0` there is `R` with
`‖G_{c,σ} f (x)‖ ≤ C (c^M + ε) ⟨x⟩^M` for `‖x‖ ≥ R` and all continuous `f` with `‖f‖ ≤ C ⟨·⟩^M`. -/
theorem s83_tail_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {M : ℝ} (hM : 0 ≤ M) {c σ σ₀ : ℝ} (hc0 : 0 < c) (hc : c ≤ 1) (hσ : |σ| ≤ σ₀) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ R : ℝ, ∀ x : Euc d, R ≤ ‖x‖ → ∀ (f : Euc d → E) (C : ℝ), Continuous f → Wt M C f →
      ‖s83_G c σ f x‖ ≤ C * (c ^ M + ε) * jbracket x ^ M := by
  have h := s83_tail_ratio (d := d) hM hc0 hc hσ
  have hev : {x : Euc d | (∫ z, jbracket (c • x + σ • z) ^ M ∂(stdGaussian (Euc d))) /
      jbracket x ^ M < c ^ M + ε} ∈ cocompact (Euc d) :=
    h.eventually (gt_mem_nhds (by linarith))
  obtain ⟨r, hr⟩ := Metric.closedBall_compl_subset_of_mem_cocompact hev 0
  refine ⟨r + 1, fun x hx f C hf hw => ?_⟩
  have hxP := hr (show x ∈ (Metric.closedBall (0 : Euc d) r)ᶜ by
    simp only [Set.mem_compl_iff, mem_closedBall_zero_iff, not_le]; linarith)
  have hxP' : (∫ z, jbracket (c • x + σ • z) ^ M ∂(stdGaussian (Euc d))) /
      jbracket x ^ M < c ^ M + ε := hxP
  have hp : 0 < jbracket x ^ M := Real.rpow_pos_of_pos (s83_jb_pos x) _
  rw [div_lt_iff₀ hp] at hxP'
  have hC := hw.nonneg
  have hint : Integrable (fun z : Euc d => jbracket (c • x + σ • z) ^ M) (stdGaussian (Euc d)) := by
    have hw1 : Wt M 1 (fun y : Euc d => jbracket y ^ M) := fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (s83_jb_pos y).le _), one_mul]
    have hc1 : Continuous fun y : Euc d => jbracket y ^ M := by
      unfold jbracket
      exact Continuous.rpow_const (by fun_prop) fun z => Or.inl (by
        have := (s83_jb_pos z).ne'; unfold jbracket at this; exact this)
    exact s83_int_shift hc1 hM hw1 hσ x
  have hintf := (s83_int_shift hf hM hw hσ (c := c) x).norm
  calc ‖s83_G c σ f x‖ ≤ ∫ z, ‖f (c • x + σ • z)‖ ∂(stdGaussian (Euc d)) :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ z, C * jbracket (c • x + σ • z) ^ M ∂(stdGaussian (Euc d)) :=
        integral_mono hintf (hint.const_mul C) fun z => hw _
    _ = C * ∫ z, jbracket (c • x + σ • z) ^ M ∂(stdGaussian (Euc d)) := integral_const_mul _ _
    _ ≤ C * ((c ^ M + ε) * jbracket x ^ M) := mul_le_mul_of_nonneg_left hxP'.le hC
    _ = C * (c ^ M + ε) * jbracket x ^ M := by ring

/-- `‖(1-χ_R) P_t‖_{C_M→C_M} ≤ e^{-aMt} + ε` for `R` large (uniformly in nothing but `t`, `ε`). -/
theorem s83_P_tail_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {M : ℝ} (hM : 0 ≤ M) {a ν t : ℝ} (ha : 0 < a) (hν : 0 ≤ ν) (ht : 0 ≤ t) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ x : Euc d, R ≤ ‖x‖ → ∀ (f : Euc d → E) (C : ℝ), Continuous f → Wt M C f →
      ‖s83_P a ν t f x‖ ≤ C * (Real.exp (-a * M * t) + ε) * jbracket x ^ M := by
  obtain ⟨R, hR⟩ := s83_tail_bound (d := d) (E := E) hM (s83_mc_pos a t) (s83_mc_le_one ha.le ht)
    (s83_abs_ms_le ha hν ht) hε
  refine ⟨R, fun x hx f C hf hw => ?_⟩
  have := hR x hx f C hf hw
  have e : s83_mc a t ^ M = Real.exp (-a * M * t) := by
    unfold s83_mc
    rw [← Real.exp_mul]; congr 1; ring
  rw [e] at this
  exact this

end HRS.MS.Wad
