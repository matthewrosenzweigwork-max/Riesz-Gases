import HRS.MS.R2SeAux18

/-!
# S9.9 `r2_static_edgeworth`, packet 19: finite-rank kernels, the cutoff, `C_c^∞ ⊂ C_b^k`

Worker S99, namespace `S99`.

* `s99_cb_of_cinf`: `C_c^∞ ⊂ C_b^k` for every `k`;
* `s99_cutoff`: a smooth compactly supported `ϑ_R` with `ϑ_R(y) = y` and `ϑ_R' = 1` on `|y| < R`;
* `s99_pe_finrank`: for the finite-rank kernel `h_n = ∑ c_{ab} u_a ⊗ u_b` (`c` symmetric),
  `N F^{h_n}_N = ½ ∑ c_{ab} Z_a Z_b - ½ μ_N(∑ c_{ab} u_a u_b)`, `Z_a = √N(μ_N(u_a) - μ(u_a))`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

theorem s99_cb_of_cinf {u : Euc d → ℝ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) (k : ℕ) :
    MemCb k u := by
  refine ⟨hu.of_le (by exact_mod_cast le_top), fun j hj => ?_⟩
  have hcont : Continuous fun x => ‖iteratedFDeriv ℝ j u x‖ :=
    (hu.continuous_iteratedFDeriv (m := j) (by exact_mod_cast le_top)).norm
  have hsupp : HasCompactSupport fun x => ‖iteratedFDeriv ℝ j u x‖ := (hc.iteratedFDeriv j).norm
  obtain ⟨B, hB⟩ := hcont.bounded_above_of_compact_support hsupp
  exact ⟨B, by rintro _ ⟨x, rfl⟩; simpa using hB x⟩

theorem s99_cutoff (R : ℝ) (hR : 0 < R) :
    ∃ ϑ : ℝ → ℝ, ContDiff ℝ ∞ ϑ ∧ (∀ y, |y| < R → ϑ y = y) ∧ (∀ y, |y| < R → deriv ϑ y = 1) ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ y, |ϑ y| ≤ M ∧ |deriv ϑ y| ≤ M := by
  set g : ℝ → ℝ := fun y => Real.smoothTransition (2 - y ^ 2 / R ^ 2) with hg
  set ϑ : ℝ → ℝ := fun y => y * g y with hϑ
  have hgc : ContDiff ℝ ∞ g :=
    Real.smoothTransition.contDiff.comp (contDiff_const.sub (((contDiff_id.pow 2)).div_const _))
  have hϑc : ContDiff ℝ ∞ ϑ := contDiff_id.mul hgc
  have hg1 : ∀ y, |y| < R → g y = 1 := by
    intro y hy
    apply Real.smoothTransition.one_of_one_le
    have : y ^ 2 < R ^ 2 := by nlinarith [abs_nonneg y, sq_abs y]
    have : y ^ 2 / R ^ 2 < 1 := by rw [div_lt_one (by positivity)]; exact this
    linarith
  have hsupp : HasCompactSupport ϑ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) (2 * R)) fun y hy => ?_
    have hy' : 2 * R < |y| := by simpa [Real.dist_eq] using hy
    have : g y = 0 := by
      apply Real.smoothTransition.zero_of_nonpos
      have : (2 * R) ^ 2 < y ^ 2 := by nlinarith [abs_nonneg y, sq_abs y]
      have : 4 < y ^ 2 / R ^ 2 := by
        rw [lt_div_iff₀ (by positivity)]; nlinarith
      linarith
    simp [hϑ, this]
  have hderc : Continuous (deriv ϑ) := hϑc.continuous_deriv (by exact_mod_cast le_top)
  have hdersupp : HasCompactSupport (deriv ϑ) := hsupp.deriv
  obtain ⟨M1, hM1⟩ := hϑc.continuous.bounded_above_of_compact_support hsupp
  obtain ⟨M2, hM2⟩ := hderc.bounded_above_of_compact_support hdersupp
  refine ⟨ϑ, hϑc, fun y hy => by simp [hϑ, hg1 y hy], fun y hy => ?_,
    max M1 M2 ⊔ 0, le_max_right _ _, fun y => ⟨?_, ?_⟩⟩
  · have : ϑ =ᶠ[𝓝 y] fun y => y := by
      have hopen : IsOpen {z : ℝ | |z| < R} := isOpen_lt continuous_abs continuous_const
      filter_upwards [hopen.mem_nhds hy] with z hz
      simp [hϑ, hg1 z hz]
    rw [this.deriv_eq]; simp
  · have := hM1 y
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_trans (le_max_left _ _) (le_max_left _ _))
  · have := hM2 y
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_trans (le_max_right _ _) (le_max_left _ _))

end S99

end
