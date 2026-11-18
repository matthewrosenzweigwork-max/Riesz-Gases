import HRS.MP.SelfSimP4MolB3

/-!
# MPP4MOL stage 5a (9): continuity of parameter integrals against a narrowly continuous family of laws
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MP.SelfSimP4Mol

variable {d N : ℕ}

/-- Continuity of `(r, x) ↦ ∫ h r x y dμ_r(y)` for `h` continuous with `y`-support in a ball. -/
theorem p4m_cont_param_supp {μ : ℝ → Measure (EucConfig d N)} [∀ r, IsProbabilityMeasure (μ r)]
    (hnar : ∀ g : EucConfig d N → ℝ, Continuous g → (∃ C : ℝ, ∀ y, |g y| ≤ C) →
      Continuous fun r => ∫ y, g y ∂(μ r))
    {h : ℝ → EucConfig d N → EucConfig d N → ℝ}
    (hc : Continuous (fun p : ℝ × EucConfig d N × EucConfig d N => h p.1 p.2.1 p.2.2))
    {R : ℝ} (hsupp : ∀ r x y, R < ‖y‖ → h r x y = 0) :
    Continuous (fun p : ℝ × EucConfig d N => ∫ y, h p.1 p.2 y ∂(μ p.1)) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨r₀, x₀⟩
  rw [Metric.continuousAt_iff]
  intro ε hε
  -- the frozen integrand
  have hg₀c : Continuous (h r₀ x₀) :=
    hc.comp (Continuous.prodMk continuous_const (Continuous.prodMk continuous_const continuous_id))
  have hg₀b : ∃ C : ℝ, ∀ y, |h r₀ x₀ y| ≤ C := by
    have hcs : HasCompactSupport (h r₀ x₀) := by
      refine HasCompactSupport.intro (isCompact_closedBall (0 : EucConfig d N) R) fun y hy => ?_
      exact hsupp _ _ _ (by simpa [Metric.mem_closedBall, dist_zero_right] using hy)
    obtain ⟨C, hC⟩ := hg₀c.bounded_above_of_compact_support hcs
    exact ⟨C, fun y => by simpa using hC y⟩
  have hnarr := (hnar _ hg₀c hg₀b).continuousAt (x := r₀)
  rw [Metric.continuousAt_iff] at hnarr
  obtain ⟨δ₁, hδ₁, h1⟩ := hnarr (ε / 2) (by positivity)
  -- uniform continuity
  set K : Set (ℝ × EucConfig d N × EucConfig d N) :=
    Metric.closedBall r₀ 1 ×ˢ Metric.closedBall x₀ 1 ×ˢ Metric.closedBall (0 : EucConfig d N) R with hK
  have hKc : IsCompact K :=
    (isCompact_closedBall r₀ 1).prod ((isCompact_closedBall x₀ 1).prod (isCompact_closedBall 0 R))
  have huc := Metric.uniformContinuousOn_iff.1 (hKc.uniformContinuousOn_of_continuous hc.continuousOn)
  obtain ⟨δ₂, hδ₂, h2⟩ := huc (ε / 2) (by positivity)
  refine ⟨min (min δ₁ δ₂) 1, by positivity, fun p hp => ?_⟩
  obtain ⟨r, x⟩ := p
  rw [Prod.dist_eq, max_lt_iff] at hp
  simp only at hp
  have hr1 : dist r r₀ < δ₁ := lt_of_lt_of_le hp.1 (by simp)
  have hr2 : dist r r₀ < δ₂ := lt_of_lt_of_le hp.1 (by simp)
  have hr3 : dist r r₀ < 1 := lt_of_lt_of_le hp.1 (by simp)
  have hx2 : dist x x₀ < δ₂ := lt_of_lt_of_le hp.2 (by simp)
  have hx3 : dist x x₀ < 1 := lt_of_lt_of_le hp.2 (by simp)
  -- pointwise closeness
  have hpt : ∀ y, |h r x y - h r₀ x₀ y| ≤ ε / 2 := by
    intro y
    by_cases hy : R < ‖y‖
    · rw [hsupp _ _ _ hy, hsupp _ _ _ hy]; simp; positivity
    · push_neg at hy
      have hA : (r, x, y) ∈ K := ⟨by simpa [Metric.mem_closedBall] using hr3.le,
        by simpa [Metric.mem_closedBall] using hx3.le, by simpa [Metric.mem_closedBall] using hy⟩
      have hB : (r₀, x₀, y) ∈ K := ⟨by simp [Metric.mem_closedBall], by simp [Metric.mem_closedBall],
        by simpa [Metric.mem_closedBall] using hy⟩
      have := h2 _ hA _ hB (by
        rw [Prod.dist_eq, Prod.dist_eq]
        simp only [dist_self]
        refine lt_of_le_of_lt ?_ (max_lt hr2 hx2)
        simp)
      simpa [Real.dist_eq] using this.le
  -- the integrals
  have hint : ∀ r' x' : _, Integrable (h r' x') (μ r) := by
    intro r' x'
    have hcc : Continuous (h r' x') :=
      hc.comp (Continuous.prodMk continuous_const (Continuous.prodMk continuous_const continuous_id))
    have hcs : HasCompactSupport (h r' x') := by
      refine HasCompactSupport.intro (isCompact_closedBall (0 : EucConfig d N) R) fun y hy => ?_
      exact hsupp _ _ _ (by simpa [Metric.mem_closedBall, dist_zero_right] using hy)
    obtain ⟨C, hC⟩ := hcc.bounded_above_of_compact_support hcs
    exact Integrable.of_bound hcc.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  have hi1 := hint r x
  have hi2 := hint r₀ x₀
  have hd : |∫ y, h r x y ∂(μ r) - ∫ y, h r₀ x₀ y ∂(μ r)| ≤ ε / 2 := by
    rw [← integral_sub hi1 hi2]
    have := norm_integral_le_of_norm_le_const (μ := μ r) (f := fun y => h r x y - h r₀ x₀ y) (C := ε / 2)
      (Filter.Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using hpt y)
    simpa [Real.norm_eq_abs] using this
  have hn := h1 hr1
  rw [Real.dist_eq] at hn ⊢
  calc |∫ y, h r x y ∂(μ r) - ∫ y, h r₀ x₀ y ∂(μ r₀)|
      = |(∫ y, h r x y ∂(μ r) - ∫ y, h r₀ x₀ y ∂(μ r)) + (∫ y, h r₀ x₀ y ∂(μ r) - ∫ y, h r₀ x₀ y ∂(μ r₀))| := by
        congr 1; ring
    _ ≤ |∫ y, h r x y ∂(μ r) - ∫ y, h r₀ x₀ y ∂(μ r)| + |∫ y, h r₀ x₀ y ∂(μ r) - ∫ y, h r₀ x₀ y ∂(μ r₀)| :=
        abs_add_le _ _
    _ < ε := by linarith


/-- The cut-off `ζ_R(y) = max 0 (min 1 (R + 1 - ‖y‖))`. -/
def p4m_zeta (R : ℝ) (y : EucConfig d N) : ℝ := max 0 (min 1 (R + 1 - ‖y‖))

theorem p4m_zeta_cont (R : ℝ) : Continuous (p4m_zeta R : EucConfig d N → ℝ) :=
  continuous_const.max (continuous_const.min (continuous_const.sub continuous_norm))

theorem p4m_zeta_nonneg (R : ℝ) (y : EucConfig d N) : 0 ≤ p4m_zeta R y := le_max_left _ _

theorem p4m_zeta_le_one (R : ℝ) (y : EucConfig d N) : p4m_zeta R y ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem p4m_zeta_eq_one {R : ℝ} {y : EucConfig d N} (hy : ‖y‖ ≤ R) : p4m_zeta R y = 1 := by
  unfold p4m_zeta
  rw [min_eq_left (by linarith), max_eq_right zero_le_one]

theorem p4m_zeta_eq_zero {R : ℝ} {y : EucConfig d N} (hy : R + 1 ≤ ‖y‖) : p4m_zeta R y = 0 := by
  unfold p4m_zeta
  exact max_eq_left ((min_le_right _ _).trans (by linarith))

theorem p4m_norm_le_q_add (y : EucConfig d N) : ‖y‖ ≤ 1 + p4m_q y := by
  have := p4m_norm_sq_le_q y
  nlinarith [norm_nonneg y, sq_nonneg (‖y‖ - 1)]

/-- Continuity of parameter integrals with at most linear growth in `y`. -/
theorem p4m_cont_param {μ : ℝ → Measure (EucConfig d N)} [∀ r, IsProbabilityMeasure (μ r)]
    (hm : ∀ r, Integrable p4m_q (μ r)) {M : ℝ} (hM : ∀ r, ∫ y, p4m_q y ∂(μ r) ≤ M)
    (hnar : ∀ g : EucConfig d N → ℝ, Continuous g → (∃ C : ℝ, ∀ y, |g y| ≤ C) →
      Continuous fun r => ∫ y, g y ∂(μ r))
    {h : ℝ → EucConfig d N → EucConfig d N → ℝ}
    (hc : Continuous (fun p : ℝ × EucConfig d N × EucConfig d N => h p.1 p.2.1 p.2.2))
    (hb : ∀ x₀ : EucConfig d N, ∃ C : ℝ, 0 ≤ C ∧ ∀ r x, dist x x₀ ≤ 1 → ∀ y, |h r x y| ≤ C * (1 + ‖y‖)) :
    Continuous (fun p : ℝ × EucConfig d N => ∫ y, h p.1 p.2 y ∂(μ p.1)) := by
  have hcy : ∀ r x, Continuous (h r x) := fun r x =>
    hc.comp (Continuous.prodMk continuous_const (Continuous.prodMk continuous_const continuous_id))
  -- cut-off versions
  have hcut : ∀ R : ℝ, Continuous (fun p : ℝ × EucConfig d N =>
      ∫ y, h p.1 p.2 y * p4m_zeta R y ∂(μ p.1)) := by
    intro R
    refine p4m_cont_param_supp hnar (R := R + 1) (h := fun r x y => h r x y * p4m_zeta R y) ?_ ?_
    · exact hc.mul ((p4m_zeta_cont R).comp (continuous_snd.comp continuous_snd))
    · intro r x y hy
      rw [p4m_zeta_eq_zero (by linarith), mul_zero]
  rw [continuous_iff_continuousAt]
  rintro ⟨r₀, x₀⟩
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨C, hC0, hC⟩ := hb x₀
  set R : ℝ := max 1 (6 * C * (|M| + 1) / ε) with hRdef
  have hR1 : 1 ≤ R := le_max_left _ _
  have hR0 : 0 < R := by linarith
  have hRε : 6 * C * (|M| + 1) / ε ≤ R := le_max_right _ _
  -- tail bound
  have htail : ∀ r x, dist x x₀ ≤ 1 →
      |∫ y, h r x y ∂(μ r) - ∫ y, h r x y * p4m_zeta R y ∂(μ r)| ≤ 2 * C * (|M| + 1) / R := by
    intro r x hx
    have hint : Integrable (h r x) (μ r) := by
      have : Integrable (fun y => C * (2 + p4m_q y)) (μ r) :=
        ((integrable_const 2).add (hm r)).const_mul C
      refine this.mono' (hcy r x).aestronglyMeasurable (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs]
      refine (hC r x hx y).trans ?_
      have := p4m_norm_le_q_add y
      nlinarith
    have hint2 : Integrable (fun y => h r x y * p4m_zeta R y) (μ r) := by
      refine hint.mono ((hcy r x).mul (p4m_zeta_cont R)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg (p4m_zeta_nonneg R y)]
      exact mul_le_of_le_one_right (abs_nonneg _) (p4m_zeta_le_one R y)
    rw [← integral_sub hint hint2]
    have hbound : ∀ y, ‖h r x y - h r x y * p4m_zeta R y‖ ≤ (2 * C / R) * p4m_q y := by
      intro y
      rw [Real.norm_eq_abs, ← mul_one_sub, abs_mul]
      by_cases hy : ‖y‖ ≤ R
      · rw [p4m_zeta_eq_one hy]
        have := p4m_q_nonneg y
        simp only [sub_self, abs_zero, mul_zero]
        positivity
      · push_neg at hy
        have h1 : |1 - p4m_zeta R y| ≤ 1 := by
          rw [abs_of_nonneg (by linarith [p4m_zeta_le_one R y])]
          linarith [p4m_zeta_nonneg R y]
        have h2 : |h r x y| ≤ 2 * C * ‖y‖ := by
          refine (hC r x hx y).trans ?_
          nlinarith
        have h3 : ‖y‖ ≤ p4m_q y / R := by
          rw [le_div_iff₀ hR0]
          have := p4m_norm_sq_le_q y
          nlinarith [norm_nonneg y]
        calc |h r x y| * |1 - p4m_zeta R y| ≤ |h r x y| * 1 :=
              mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
          _ ≤ 2 * C * ‖y‖ := by linarith
          _ ≤ 2 * C * (p4m_q y / R) := by gcongr
          _ = (2 * C / R) * p4m_q y := by ring
    have := norm_integral_le_of_norm_le ((hm r).const_mul (2 * C / R))
      (Filter.Eventually.of_forall hbound)
    rw [integral_const_mul] at this
    rw [Real.norm_eq_abs] at this
    refine this.trans ?_
    calc 2 * C / R * ∫ y, p4m_q y ∂(μ r) ≤ 2 * C / R * (|M| + 1) :=
          mul_le_mul_of_nonneg_left ((hM r).trans (by linarith [le_abs_self M])) (by positivity)
      _ = _ := by ring
  have hεR : 2 * C * (|M| + 1) / R ≤ ε / 3 := by
    have hpos : 0 ≤ C * (|M| + 1) := by positivity
    rw [div_le_iff₀ hR0]
    have : 6 * C * (|M| + 1) ≤ ε * R := by
      have := (div_le_iff₀ hε).1 hRε
      linarith
    nlinarith
  have hcR := (hcut R).continuousAt (x := (r₀, x₀))
  rw [Metric.continuousAt_iff] at hcR
  obtain ⟨δ, hδ, hδ'⟩ := hcR (ε / 3) (by positivity)
  refine ⟨min δ 1, by positivity, fun p hp => ?_⟩
  obtain ⟨r, x⟩ := p
  have hpδ : dist (r, x) (r₀, x₀) < δ := lt_of_lt_of_le hp (min_le_left _ _)
  have hx1 : dist x x₀ ≤ 1 := by
    have := lt_of_lt_of_le hp (min_le_right _ _)
    rw [Prod.dist_eq, max_lt_iff] at this
    exact this.2.le
  have e1 := htail r x hx1
  have e2 := htail r₀ x₀ (by simp)
  have e3 := hδ' hpδ
  rw [Real.dist_eq] at e3 ⊢
  simp only at e3 ⊢
  calc |∫ y, h r x y ∂(μ r) - ∫ y, h r₀ x₀ y ∂(μ r₀)|
      = |(∫ y, h r x y ∂(μ r) - ∫ y, h r x y * p4m_zeta R y ∂(μ r)) +
        (∫ y, h r x y * p4m_zeta R y ∂(μ r) - ∫ y, h r₀ x₀ y * p4m_zeta R y ∂(μ r₀)) -
        (∫ y, h r₀ x₀ y ∂(μ r₀) - ∫ y, h r₀ x₀ y * p4m_zeta R y ∂(μ r₀))| := by
        congr 1; ring
    _ ≤ |∫ y, h r x y ∂(μ r) - ∫ y, h r x y * p4m_zeta R y ∂(μ r)| +
        |∫ y, h r x y * p4m_zeta R y ∂(μ r) - ∫ y, h r₀ x₀ y * p4m_zeta R y ∂(μ r₀)| +
        |∫ y, h r₀ x₀ y ∂(μ r₀) - ∫ y, h r₀ x₀ y * p4m_zeta R y ∂(μ r₀)| := by
        refine (abs_sub _ _).trans ?_
        gcongr
        exact abs_add_le _ _
    _ < ε := by linarith

end HRS.MP.SelfSimP4Mol
