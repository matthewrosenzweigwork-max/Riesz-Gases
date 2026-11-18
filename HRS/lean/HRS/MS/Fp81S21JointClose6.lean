import HRS.MS.Fp81S21JointN5

/-! Explicit chart-uniform radius condition for the physical bundle and errors. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

private theorem fp81s21_jointClose_bundle_radius_exists (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
    ∃ εN εG εB : ℕ → ℝ,
      (∀ m, 0 ≤ εN m) ∧ Tendsto εN atTop (𝓝 0) ∧
      (∀ m, 0 ≤ εG m) ∧ Tendsto εG atTop (𝓝 0) ∧
      (∀ m, 0 ≤ εB m) ∧ Tendsto εB atTop (𝓝 0) ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        Nonempty (fp81s21_Physical31 p R Es E εN εG εB) := by
  obtain ⟨εN, εG, εB, hn, hnl, hg, hgl, hb, hbl, δ0, hδ, hh, hs⟩ :=
    fp81s21_physical31_exists p Es E
  exact ⟨δ0, hδ, hh, εN, εG, εB, hn, hnl, hg, hgl, hb, hbl, hs⟩

/-- A radius selected from the existing chart-dependent physical bundle producer. -/
def fp81s21_jointClose_bundleRadius (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)) : ℝ :=
  Classical.choose (fp81s21_jointClose_bundle_radius_exists p Es E)

/-- A radius selected from the existing chart-dependent shared-error producer. -/
def fp81s21_jointClose_errorRadius (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)) : ℝ :=
  Classical.choose (fp81s21_jointN_sqerr_physical p Es E)

/-- A common positive lower bound on the two selected chart radii moves the
radius before the charts, while leaving the profile and physical selection
for each chart before the trajectory and horizon. -/
theorem fp81s21_jointClose_chart_uniform (p : Parameters)
    (hUniform : ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
        (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)),
        δ0 ≤ fp81s21_jointClose_bundleRadius p Es E ∧
        δ0 ≤ fp81s21_jointClose_errorRadius p Es E) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
    ∀ (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
      (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)),
      δ0 ≤ fp81s21_jointClose_errorRadius p Es E ∧
      ∃ εN εG εB : ℕ → ℝ,
        (∀ m, 0 ≤ εN m) ∧ Tendsto εN atTop (𝓝 0) ∧
        (∀ m, 0 ≤ εG m) ∧ Tendsto εG atTop (𝓝 0) ∧
        (∀ m, 0 ≤ εB m) ∧ Tendsto εB atTop (𝓝 0) ∧
        ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
          Nonempty (fp81s21_Physical31 p R Es E εN εG εB) := by
  obtain ⟨δ0, hδ0, hh, hu⟩ := hUniform
  refine ⟨δ0, hδ0, hh, ?_⟩
  intro Es E
  obtain ⟨hbundle, herror⟩ := hu Es E
  obtain ⟨_, _, εN, εG, εB, hn, hnl, hg, hgl, hb, hbl, hs⟩ :=
    Classical.choose_spec (fp81s21_jointClose_bundle_radius_exists p Es E)
  refine ⟨herror, εN, εG, εB, hn, hnl, hg, hgl, hb, hbl, ?_⟩
  intro δ hδ hδle R
  apply hs δ hδ ?_ R
  exact hδle.trans hbundle

#print axioms fp81s21_jointClose_bundleRadius
#print axioms fp81s21_jointClose_errorRadius
#print axioms fp81s21_jointClose_chart_uniform
end HRS.Fp81.S21
end
