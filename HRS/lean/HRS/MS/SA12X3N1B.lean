import HRS.MS.SA12X3N1A
import HRS.MS.SA12BuildC19
import HRS.MS.Ker1Aux6

/-!
# S.A.12 N1/N2 (SA12X3), part B: far regime of the periodic kernel (mean value theorem off the lattice)
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

variable {d : ℕ}

theorem sa12x3n_reduce {L : ℝ} (hL : 0 < L) (w : Euc d) :
    ∃ k : Fin d → ℤ, ∀ i, |(w - L • latticePt k) i| ≤ L / 2 := by
  refine ⟨fun i => round (w i / L), fun i => ?_⟩
  have h := abs_sub_round (w i / L)
  have e : (w - L • latticePt (fun i => round (w i / L))) i = L * (w i / L - round (w i / L)) := by
    simp [latticePt]; field_simp
  rw [e, abs_mul, abs_of_pos hL]
  nlinarith

theorem sa12x3n_reduce_norm {R L : ℝ} (hR : 1 ≤ R) (hL : 4 * R ≤ L) {x u : Euc d} {k : Fin d → ℤ}
    (hx : ∀ i, |x i| ≤ L / 2) (hxn : 2 * R ≤ ‖x‖) (hu : ‖u‖ ≤ R)
    (hw' : ∀ i, |(x - u - L • latticePt k) i| ≤ L / 2) : R ≤ ‖x - u - L • latticePt k‖ := by
  by_cases hk : k = 0
  · subst hk
    have h0 : latticePt (0 : Fin d → ℤ) = (0 : Euc d) := by ext i; simp [latticePt]
    have : x - u - L • latticePt (0 : Fin d → ℤ) = x - u := by rw [h0]; simp
    rw [this]
    have h1 : ‖x‖ ≤ ‖x - u‖ + ‖u‖ := by
      calc ‖x‖ = ‖(x - u) + u‖ := by simp
        _ ≤ _ := norm_add_le _ _
    linarith
  · obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
      by_contra h
      push Not at h
      exact hk (funext h)
    have h1 : (1 : ℝ) ≤ |(k i : ℝ)| := by
      have : (1 : ℤ) ≤ |k i| := Int.one_le_abs hi
      exact_mod_cast this
    have h2 : |u i| ≤ R := by
      have := PiLp.norm_apply_le u i
      rw [Real.norm_eq_abs] at this
      linarith
    have e : (x - u - L • latticePt k) i = x i - u i - L * k i := by simp [latticePt]
    have hL0 : 0 < L := by linarith
    have h3 : L * |(k i : ℝ)| ≤ |x i - u i - L * k i| + |x i - u i| := by
      have : L * (k i : ℝ) = (x i - u i) - (x i - u i - L * k i) := by ring
      calc L * |(k i : ℝ)| = |L * (k i : ℝ)| := by rw [abs_mul, abs_of_pos hL0]
        _ = |(x i - u i) - (x i - u i - L * k i)| := by rw [← this]
        _ ≤ _ := by rw [add_comm]; exact abs_sub _ _
    have h4 : |x i - u i| ≤ L / 2 + R := by
      calc |x i - u i| ≤ |x i| + |u i| := abs_sub _ _
        _ ≤ _ := by linarith [hx i]
    have h5 : L ≤ L * |(k i : ℝ)| := by nlinarith
    have h6 : R ≤ |(x - u - L • latticePt k) i| := by rw [e]; linarith
    exact h6.trans (by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le (x - u - L • latticePt k) i)

end HRS.MH.AdjointRd.Phase2SA12Construction
