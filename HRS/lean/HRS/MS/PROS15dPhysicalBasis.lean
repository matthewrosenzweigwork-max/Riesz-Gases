import HRS.MS.S21H2_S14aD5

/-!
# S15d: existence of an admissible orthonormal test basis for the physical reference measure

Unlike an arbitrary atomic probability measure, the positive density of a
physical trajectory is bounded by a Gaussian reference density. The existing
smooth-test Gram-Schmidt construction therefore applies at the initial time.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS.Whole

theorem s15d_physical_test_basis_exists
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) :
    ∃ a : ℕ → Euc p.d → ℝ, IsR2ZeroMeanONB (r26t3_mu R 0) a := by
  haveI : IsProbabilityMeasure (r26t3_mu R 0) :=
    s21h2_mu_prob hδ hδh R
  obtain ⟨-, -, -, href⟩ := r26t3_reference_data p δ hδ hδh R
  obtain ⟨M, c, S, hc, hTc⟩ := href 0
  have hM : ∀ x, R.ρ 0 x ≤ |M| := fun x => by
    have h1 := hTc.gauss x
    have h2 : Real.exp (-c * ‖x‖ ^ 2) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖x‖])
    have h0 : 0 ≤ M := by
      have := hTc.gauss 0
      have h3 := hTc.pos 0
      simp at this
      linarith
    calc
      R.ρ 0 x ≤ M * Real.exp (-c * ‖x‖ ^ 2) := h1
      _ ≤ M * 1 := mul_le_mul_of_nonneg_left h2 h0
      _ ≤ |M| := by rw [mul_one]; exact le_abs_self _
  have hρ : IsRound2Density p.d 1 |M| 0 (R.ρ 0) :=
    ⟨hTc.prob, hM, fun h => absurd h one_ne_zero⟩
  simpa only [r26t3_mu] using
    (HRS.MS.R2Chaos.s94_exists_onb p.hd hρ)

end HRS.MS.R26T3
