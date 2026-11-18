import HRS.MS.S104eC1G

/-!
# S104E route C, packet C1 (part H): small-parameter closeness and decay for Gaussian averages of `C_0` functions

`s104c1_close`: for `φ` continuous, bounded, vanishing at infinity: `G_{c,s} φ → φ` uniformly as `(c,s) → (1,0)`.
`s104c1_van`: for fixed `c > 0`, `s ≥ 0`, `G_{c,s} φ` vanishes at infinity.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ContDiff

namespace HRS.MS.S104e.C
open HRS HRS.Whole
variable {d : ℕ}

theorem s104c1_cocompact_small {F : Type*} [NormedAddCommGroup F] {φ : Euc d → F}
    (hv : Tendsto (fun y => ‖φ y‖) (cocompact (Euc d)) (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ y, R < ‖y‖ → ‖φ y‖ ≤ ε := by
  have h1 := hv.eventually (gt_mem_nhds hε)
  obtain ⟨t, ht, hts⟩ := Filter.mem_cocompact.1 h1
  obtain ⟨R, hR⟩ := ht.isBounded.subset_closedBall (0 : Euc d)
  refine ⟨max R 0, le_max_right _ _, fun y hy => ?_⟩
  have : y ∉ t := fun hyt => by
    have := hR hyt
    simp only [Metric.mem_closedBall, dist_zero_right] at this
    linarith [le_max_left R 0]
  exact (hts this).le

theorem s104c1_int_norm : Integrable (fun z : Euc d => ‖z‖) (stdGaussian (Euc d)) :=
  (IsGaussian.integrable_id (μ := stdGaussian (Euc d))).norm

theorem s104c1_close {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {φ : Euc d → F} (hφ : Continuous φ) {M : ℝ} (hM : ∀ y, ‖φ y‖ ≤ M)
    (hv : Tendsto (fun y => ‖φ y‖) (cocompact (Euc d)) (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c s : ℝ, |c - 1| < δ → 0 ≤ s → s < δ → ∀ x : Euc d,
      ‖(∫ z, φ (c • x + s • z) ∂(stdGaussian (Euc d))) - φ x‖ ≤ ε := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set ε₁ : ℝ := ε / 4 with hε₁
  have hε₁0 : 0 < ε₁ := by positivity
  obtain ⟨R, hR0, hR⟩ := s104c1_cocompact_small hv hε₁0
  have hU : UniformContinuous φ :=
    hφ.uniformContinuous_of_tendsto_cocompact (tendsto_zero_iff_norm_tendsto_zero.2 hv)
  obtain ⟨η, hη0, hη⟩ := Metric.uniformContinuous_iff.1 hU ε₁ hε₁0
  set η' : ℝ := min η 1 with hη'
  have hη'0 : 0 < η' := lt_min hη0 one_pos
  have hη'η : η' ≤ η := min_le_left _ _
  have hη'1 : η' ≤ 1 := min_le_right _ _
  set m1 : ℝ := ∫ z : Euc d, ‖z‖ ∂(stdGaussian (Euc d)) with hm1
  have hm10 : 0 ≤ m1 := integral_nonneg fun _ => norm_nonneg _
  set R₂ : ℝ := 2 * R + 2 with hR₂
  have hR₂0 : 0 < R₂ := by positivity
  set δ : ℝ := min (min (1 / 2) (η' / (2 * R₂ + 1))) (ε * η' / (16 * (M + 1) * (m1 + 1))) with hδ
  have hδ0 : 0 < δ := lt_min (lt_min (by norm_num) (by positivity)) (by positivity)
  refine ⟨δ, hδ0, fun c s hc hs0 hsδ x => ?_⟩
  have hδ1 : δ ≤ 1 / 2 := (min_le_left _ _).trans (min_le_left _ _)
  have hδ2 : δ ≤ η' / (2 * R₂ + 1) := (min_le_left _ _).trans (min_le_right _ _)
  have hδ3 : δ ≤ ε * η' / (16 * (M + 1) * (m1 + 1)) := min_le_right _ _
  have hc2 : 1 / 2 < c := by have := (abs_lt.1 hc).1; linarith
  have hcδ : |c - 1| ≤ η' / (2 * R₂ + 1) := (hc.le).trans hδ2
  -- pointwise bound
  have hpt : ∀ z : Euc d, ‖φ (c • x + s • z) - φ x‖ ≤ 2 * ε₁ + (4 * M / η') * (s * ‖z‖) := by
    intro z
    have hsz0 : 0 ≤ s * ‖z‖ := by positivity
    have hlin : 0 ≤ (4 * M / η') * (s * ‖z‖) := by positivity
    by_cases hz : s * ‖z‖ < η' / 2
    · by_cases hx : ‖x‖ ≤ R₂
      · have hd : dist (c • x + s • z) x < η := by
          rw [dist_eq_norm]
          have e : c • x + s • z - x = (c - 1) • x + s • z := by
            rw [sub_smul, one_smul]; abel
          rw [e]
          refine (norm_add_le _ _).trans_lt ?_
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hs0]
          have h1 : |c - 1| * ‖x‖ ≤ η' / 2 := by
            calc |c - 1| * ‖x‖ ≤ (η' / (2 * R₂ + 1)) * R₂ :=
                  mul_le_mul hcδ hx (norm_nonneg _) (by positivity)
              _ ≤ η' / 2 := by
                  rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
                  nlinarith
          linarith
        have := hη hd
        rw [dist_eq_norm] at this
        linarith
      · push Not at hx
        have hx1 : ‖φ x‖ ≤ ε₁ := hR x (by linarith)
        have hcx : R < ‖c • x + s • z‖ := by
          have h1 : ‖c • x‖ ≤ ‖c • x + s • z‖ + ‖s • z‖ := by
            calc ‖c • x‖ = ‖(c • x + s • z) - s • z‖ := by rw [add_sub_cancel_right]
              _ ≤ _ := norm_sub_le _ _
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by linarith : 0 < c)] at h1
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs0] at h1
          nlinarith
        have := hR _ hcx
        calc ‖φ (c • x + s • z) - φ x‖ ≤ ‖φ (c • x + s • z)‖ + ‖φ x‖ := norm_sub_le _ _
          _ ≤ ε₁ + ε₁ := add_le_add this hx1
          _ ≤ _ := by linarith
    · push Not at hz
      have h1 : ‖φ (c • x + s • z) - φ x‖ ≤ 2 * M :=
        (norm_sub_le _ _).trans (by linarith [hM (c • x + s • z), hM x])
      have h2 : 2 * M ≤ (4 * M / η') * (s * ‖z‖) := by
        calc 2 * M = (4 * M / η') * (η' / 2) := by field_simp; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left hz (by positivity)
      linarith
  -- integrate
  have hintφ : Integrable (fun z : Euc d => φ (c • x + s • z)) (stdGaussian (Euc d)) :=
    Integrable.of_bound (C := M) (hφ.comp (by fun_prop)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hM _)
  have hconst : (∫ z : Euc d, φ x ∂(stdGaussian (Euc d))) = φ x := by simp
  have e : (∫ z, φ (c • x + s • z) ∂(stdGaussian (Euc d))) - φ x =
      ∫ z, (φ (c • x + s • z) - φ x) ∂(stdGaussian (Euc d)) := by
    rw [integral_sub hintφ (integrable_const _), hconst]
  rw [e]
  refine (norm_integral_le_integral_norm _).trans ?_
  have hrhs : Integrable (fun z : Euc d => 2 * ε₁ + (4 * M / η') * (s * ‖z‖)) (stdGaussian (Euc d)) :=
    (integrable_const _).add ((s104c1_int_norm.const_mul s).const_mul _)
  have hlhs : Integrable (fun z : Euc d => ‖φ (c • x + s • z) - φ x‖) (stdGaussian (Euc d)) :=
    (hintφ.sub (integrable_const _)).norm
  refine (integral_mono hlhs hrhs hpt).trans ?_
  rw [integral_add (integrable_const _) ((s104c1_int_norm.const_mul s).const_mul _), integral_const,
    integral_const_mul, integral_const_mul]
  have hu1 : (stdGaussian (Euc d)).real univ = 1 := by simp [Measure.real]
  rw [hu1, one_smul]
  rw [← hm1]
  have key : (4 * M / η') * (s * m1) ≤ ε / 4 := by
    have hs' : s ≤ ε * η' / (16 * (M + 1) * (m1 + 1)) := hsδ.le.trans hδ3
    calc (4 * M / η') * (s * m1) ≤ (4 * M / η') * ((ε * η' / (16 * (M + 1) * (m1 + 1))) * m1) := by
          gcongr
      _ = (ε / 4) * ((M / (M + 1)) * (m1 / (m1 + 1))) := by field_simp; ring
      _ ≤ (ε / 4) * 1 := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          have a1 : M / (M + 1) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
          have a2 : m1 / (m1 + 1) ≤ 1 := (div_le_one (by linarith)).2 (by linarith)
          calc M / (M + 1) * (m1 / (m1 + 1)) ≤ 1 * 1 :=
                mul_le_mul a1 a2 (by positivity) zero_le_one
            _ = 1 := one_mul 1
      _ = ε / 4 := mul_one _
  linarith

/-- vanishing at infinity of weighted Gaussian averages (dominated convergence along `cocompact`) -/
theorem s104c1_van_w {F : Type*} [NormedAddCommGroup F] {φ : Euc d → F} {M : ℝ} (hφ : Continuous φ)
    (hM : ∀ y, ‖φ y‖ ≤ M) (hv : Tendsto (fun y => ‖φ y‖) (cocompact (Euc d)) (𝓝 0)) {c s : ℝ}
    (hc : c ≠ 0) {w : Euc d → ℝ} (hw : Integrable w (stdGaussian (Euc d))) (hw0 : ∀ z, 0 ≤ w z) :
    Tendsto (fun x : Euc d => ∫ z, ‖φ (c • x + s • z)‖ * w z ∂(stdGaussian (Euc d))) (cocompact (Euc d))
      (𝓝 0) := by
  haveI : (cocompact (Euc d)).IsCountablyGenerated := HRS.MS.Wad.s83_cocompact_cg d
  have hlim : ∀ z : Euc d, Tendsto (fun x : Euc d => ‖φ (c • x + s • z)‖ * w z) (cocompact (Euc d)) (𝓝 0) := by
    intro z
    have hemb : Topology.IsClosedEmbedding (fun x : Euc d => c • x + s • z) :=
      ((Homeomorph.smulOfNeZero c hc).trans (Homeomorph.addRight (s • z))).isClosedEmbedding
    have h1 := hv.comp hemb.tendsto_cocompact
    simpa using h1.mul_const (w z)
  have := tendsto_integral_filter_of_dominated_convergence (μ := stdGaussian (Euc d))
    (F := fun x z => ‖φ (c • x + s • z)‖ * w z) (bound := fun z => M * w z)
    (Filter.Eventually.of_forall fun x =>
      (((hφ.comp (by fun_prop)).norm.aestronglyMeasurable).mul hw.1))
    (Filter.Eventually.of_forall fun x => Filter.Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (hw0 z))]
      exact mul_le_mul_of_nonneg_right (hM _) (hw0 z))
    (hw.const_mul M) (Filter.Eventually.of_forall hlim)
  simpa using this

theorem s104c1_van {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {φ : Euc d → F} {M : ℝ} (hφ : Continuous φ) (hM : ∀ y, ‖φ y‖ ≤ M)
    (hv : Tendsto (fun y => ‖φ y‖) (cocompact (Euc d)) (𝓝 0)) {c s : ℝ} (hc : c ≠ 0) :
    Tendsto (fun x : Euc d => ‖∫ z, φ (c • x + s • z) ∂(stdGaussian (Euc d))‖) (cocompact (Euc d))
      (𝓝 0) := by
  have h := s104c1_van_w (s := s) hφ hM hv hc (w := fun _ => (1 : ℝ)) (integrable_const _) (fun _ => zero_le_one)
  refine squeeze_zero (fun x => norm_nonneg _) (fun x => ?_) h
  have hint : Integrable (fun z : Euc d => φ (c • x + s • z)) (stdGaussian (Euc d)) :=
    Integrable.of_bound (C := M) (hφ.comp (by fun_prop)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hM _)
  simpa using norm_integral_le_integral_norm (μ := stdGaussian (Euc d)) (fun z => φ (c • x + s • z))

end HRS.MS.S104e.C
