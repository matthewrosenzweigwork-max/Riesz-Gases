import HRS.MS.R2ChaosAux62

/-!
# HRS.MS.R2ChaosAux63 -- S9.6: a function that is uniformly continuous on a dense countable set and has the integral structure is continuous

Packet S94 (S9.6), namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

`s94_cont_of_rat_uc`: `g` with (H1) continuity on `[0,u]` for `u ∈ D`, (H2) `g = 0` off `D`, `D` an initial segment, and uniformly
continuous on `Qc = (ℚ ∩ [0,T]) ∪ {T}` is continuous on `[0,T]`.  (Used for `u ↦ ∫_0^u f`, whose junk values off the integrability
set make `Continuous` a nontrivial event: its measurability is the point.)
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

/-- The countable dense set `ℚ ∩ [0,T] ∪ {T}`. -/
def s94Qc (T : ℝ) : Set ℝ := {q | (∃ r : ℚ, (r : ℝ) = q) ∧ 0 ≤ q ∧ q ≤ T} ∪ {T}

theorem s94Qc_countable (T : ℝ) : (s94Qc T).Countable := by
  refine Set.Countable.union ?_ (Set.countable_singleton T)
  refine (Set.countable_range ((↑) : ℚ → ℝ)).mono ?_
  rintro q ⟨⟨r, hr⟩, -, -⟩
  exact ⟨r, hr⟩

theorem s94Qc_approx_below {T : ℝ} (hT : 0 ≤ T) {u : ℝ} (hu0 : 0 ≤ u) (huT : u ≤ T) {η : ℝ} (hη : 0 < η) :
    ∃ q ∈ s94Qc T, q ≤ u ∧ |q - u| < η := by
  rcases hu0.eq_or_lt with h0 | hpos
  · refine ⟨0, Or.inl ⟨⟨0, by simp⟩, le_rfl, hT⟩, by linarith, by simp [← h0, hη]⟩
  · obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show max 0 (u - η) < u from max_lt hpos (by linarith))
    have h1 : max 0 (u - η) < (r : ℝ) := hr1
    refine ⟨r, Or.inl ⟨⟨r, rfl⟩, ?_, ?_⟩, hr2.le, ?_⟩
    · exact (le_max_left _ _).trans h1.le
    · linarith
    · rw [abs_of_neg (by linarith)]
      have := (le_max_right 0 (u - η)).trans_lt h1
      linarith

theorem s94Qc_approx_above {T : ℝ} (hT : 0 ≤ T) {u : ℝ} (hu0 : 0 ≤ u) (huT : u ≤ T) {η : ℝ} (hη : 0 < η) :
    ∃ q ∈ s94Qc T, u ≤ q ∧ |q - u| < η := by
  rcases huT.eq_or_lt with h | hlt
  · exact ⟨T, Or.inr rfl, h.le, by simp [h, hη]⟩
  · obtain ⟨r, hr1, hr2⟩ := exists_rat_btwn (show u < min (u + η) T from lt_min (by linarith) hlt)
    refine ⟨r, Or.inl ⟨⟨r, rfl⟩, ?_, ?_⟩, hr1.le, ?_⟩
    · linarith
    · exact hr2.le.trans (min_le_right _ _)
    · rw [abs_of_pos (by linarith)]
      have := hr2.trans_le (min_le_left (u + η) T)
      linarith

theorem s94_cont_of_rat_uc {T : ℝ} (hT : 0 ≤ T) {g : ℝ → ℝ} {D : Set ℝ}
    (hDmono : ∀ u v, u ∈ D → 0 ≤ v → v ≤ u → v ∈ D)
    (hH1 : ∀ u ∈ D, 0 ≤ u → u ≤ T → ContinuousOn g (Set.Icc 0 u))
    (hH2 : ∀ u ∉ D, 0 ≤ u → u ≤ T → g u = 0)
    (hUC : ∀ ε > 0, ∃ δ > 0, ∀ q ∈ s94Qc T, ∀ q' ∈ s94Qc T, |q - q'| < δ → |g q - g q'| ≤ ε) :
    ContinuousOn g (Set.Icc 0 T) := by
  -- key: `g u` is approximated by `g q`, `q ∈ Qc` arbitrarily close to `u`
  have K : ∀ u, 0 ≤ u → u ≤ T → ∀ ε > 0, ∀ η > 0, ∃ q ∈ s94Qc T, |q - u| < η ∧ |g q - g u| ≤ ε := by
    intro u hu0 huT ε hε η hη
    by_cases hu : u ∈ D
    · have hc := hH1 u hu hu0 huT u ⟨hu0, le_rfl⟩
      obtain ⟨δ', hδ', hδ'1⟩ := Metric.continuousWithinAt_iff.1 hc ε hε
      obtain ⟨q, hq, hqu, hqd⟩ := s94Qc_approx_below hT hu0 huT (lt_min hη hδ')
      refine ⟨q, hq, lt_of_lt_of_le hqd (min_le_left _ _), ?_⟩
      have hq0 : 0 ≤ q := by
        rcases hq with ⟨-, h0, -⟩ | h
        · exact h0
        · rw [Set.mem_singleton_iff] at h; rw [h]; exact hT
      have := hδ'1 (x := q) ⟨hq0, hqu⟩ (by rw [Real.dist_eq]; exact lt_of_lt_of_le hqd (min_le_right _ _))
      rw [Real.dist_eq] at this
      exact this.le
    · obtain ⟨q, hq, huq, hqd⟩ := s94Qc_approx_above hT hu0 huT hη
      refine ⟨q, hq, hqd, ?_⟩
      have hqT : q ≤ T := by
        rcases hq with ⟨-, -, h⟩ | h
        · exact h
        · rw [Set.mem_singleton_iff] at h; rw [h]
      have hq : q ∉ D := fun hqD => hu (hDmono q u hqD hu0 huq)
      rw [hH2 u hu hu0 huT, hH2 q hq (hu0.trans huq) hqT]
      simp [hε.le]
  intro u0 hu0
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hUCδ⟩ := hUC (ε / 4) (by positivity)
  refine ⟨δ / 3, by positivity, fun u hu hud => ?_⟩
  obtain ⟨q, hq, hqd, hqg⟩ := K u hu.1 hu.2 (ε / 4) (by positivity) (δ / 3) (by positivity)
  obtain ⟨q0, hq0, hq0d, hq0g⟩ := K u0 hu0.1 hu0.2 (ε / 4) (by positivity) (δ / 3) (by positivity)
  have hqq : |q - q0| < δ := by
    rw [Real.dist_eq] at hud
    calc |q - q0| = |(q - u) + (u - u0) + (u0 - q0)| := by ring_nf
      _ ≤ |q - u| + |u - u0| + |u0 - q0| := abs_add_three _ _ _
      _ < δ / 3 + δ / 3 + δ / 3 := by
          have : |u0 - q0| = |q0 - u0| := abs_sub_comm _ _
          linarith
      _ = δ := by ring
  have h3 := hUCδ q hq q0 hq0 hqq
  rw [Real.dist_eq]
  calc |g u - g u0| = |(g u - g q) + (g q - g q0) + (g q0 - g u0)| := by ring_nf
    _ ≤ |g u - g q| + |g q - g q0| + |g q0 - g u0| := abs_add_three _ _ _
    _ < ε := by
        have : |g u - g q| = |g q - g u| := abs_sub_comm _ _
        linarith

end HRS.MS.R2Chaos
