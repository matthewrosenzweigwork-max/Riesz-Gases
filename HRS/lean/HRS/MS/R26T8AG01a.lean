import HRS.MS.R26T8AG00

/-!
# S8.2 observed-time layer, packet T8A.G01 (helper a): the one-dimensional cutoff

`ψ t = smoothTransition ((t - 1) / 3)` is `0` for `t ≤ 1`, `1` for `t ≥ 4`, smooth, with values in `[0, 1]`;
its first and second derivatives vanish outside `[1, 4]` and are bounded.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A

/-- the one-dimensional cutoff: `0` on `(-∞,1]`, `1` on `[4,∞)` -/
def r26t8a_g01a_psi (t : ℝ) : ℝ := Real.smoothTransition ((t - 1) / 3)

theorem r26t8a_g01a_contDiff : ContDiff ℝ ∞ r26t8a_g01a_psi := by
  unfold r26t8a_g01a_psi
  exact Real.smoothTransition.contDiff.comp
    ((contDiff_id.sub contDiff_const).div_const 3)

theorem r26t8a_g01a_nonneg (t : ℝ) : 0 ≤ r26t8a_g01a_psi t :=
  Real.smoothTransition.nonneg _

theorem r26t8a_g01a_le_one (t : ℝ) : r26t8a_g01a_psi t ≤ 1 :=
  Real.smoothTransition.le_one _

theorem r26t8a_g01a_eq_zero {t : ℝ} (h : t ≤ 1) : r26t8a_g01a_psi t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem r26t8a_g01a_eq_one {t : ℝ} (h : 4 ≤ t) : r26t8a_g01a_psi t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

/-- the first and second derivatives vanish off `[1, 4]` -/
theorem r26t8a_g01a_deriv_zero {t : ℝ} (h : t < 1 ∨ 4 < t) :
    deriv r26t8a_g01a_psi t = 0 ∧ deriv (deriv r26t8a_g01a_psi) t = 0 := by
  have hloc : r26t8a_g01a_psi =ᶠ[𝓝 t] fun _ => r26t8a_g01a_psi t := by
    rcases h with h | h
    · filter_upwards [Iio_mem_nhds h] with x hx
      rw [r26t8a_g01a_eq_zero (le_of_lt hx), r26t8a_g01a_eq_zero (le_of_lt h)]
    · filter_upwards [Ioi_mem_nhds h] with x hx
      rw [r26t8a_g01a_eq_one (le_of_lt hx), r26t8a_g01a_eq_one (le_of_lt h)]
  have h1 : deriv r26t8a_g01a_psi =ᶠ[𝓝 t] deriv (fun _ : ℝ => r26t8a_g01a_psi t) :=
    hloc.deriv
  have h2 : deriv (deriv r26t8a_g01a_psi) =ᶠ[𝓝 t] deriv (deriv (fun _ : ℝ => r26t8a_g01a_psi t)) :=
    h1.deriv
  refine ⟨?_, ?_⟩
  · rw [h1.eq_of_nhds]
    simp
  · rw [h2.eq_of_nhds]
    simp

/-- the derivatives are bounded (they are continuous with support in `[1, 4]`) -/
theorem r26t8a_g01a_deriv_bdd : ∃ K1 K2 : ℝ, 0 ≤ K1 ∧ 0 ≤ K2 ∧
    ∀ t : ℝ, |deriv r26t8a_g01a_psi t| ≤ K1 ∧ |deriv (deriv r26t8a_g01a_psi) t| ≤ K2 := by
  have hC1 : ContDiff ℝ ∞ (deriv r26t8a_g01a_psi) :=
    (contDiff_infty_iff_deriv.1 r26t8a_g01a_contDiff).2
  have hC2 : ContDiff ℝ ∞ (deriv (deriv r26t8a_g01a_psi)) :=
    (contDiff_infty_iff_deriv.1 hC1).2
  have hs1 : tsupport (deriv r26t8a_g01a_psi) ⊆ Icc 1 4 := by
    refine closure_minimal (fun t ht => ?_) isClosed_Icc
    by_contra h
    simp only [mem_Icc, not_and_or, not_le] at h
    exact ht (r26t8a_g01a_deriv_zero (by rcases h with h | h <;> [left; right] <;> linarith)).1
  have hs2 : tsupport (deriv (deriv r26t8a_g01a_psi)) ⊆ Icc 1 4 := by
    refine closure_minimal (fun t ht => ?_) isClosed_Icc
    by_contra h
    simp only [mem_Icc, not_and_or, not_le] at h
    exact ht (r26t8a_g01a_deriv_zero (by rcases h with h | h <;> [left; right] <;> linarith)).2
  have hcs1 : HasCompactSupport (deriv r26t8a_g01a_psi) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hs1
  have hcs2 : HasCompactSupport (deriv (deriv r26t8a_g01a_psi)) :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) hs2
  obtain ⟨K1, hK1⟩ := hC1.continuous.bounded_above_of_compact_support hcs1
  obtain ⟨K2, hK2⟩ := hC2.continuous.bounded_above_of_compact_support hcs2
  refine ⟨max K1 0, max K2 0, le_max_right _ _, le_max_right _ _, fun t => ⟨?_, ?_⟩⟩
  · rw [← Real.norm_eq_abs]
    exact (hK1 t).trans (le_max_left _ _)
  · rw [← Real.norm_eq_abs]
    exact (hK2 t).trans (le_max_left _ _)

end HRS.MS.R26T8A

end
