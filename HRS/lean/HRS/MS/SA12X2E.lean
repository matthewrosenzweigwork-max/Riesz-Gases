import HRS.MS.SA12X2D
import HRS.MS.SA12Z3NearN7H

/-!
# S.A.12 N9 (SA12X2), part E: real-form commutator bound, pairing, and `C_b^k` bookkeeping
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3

variable {d : ℕ}

theorem sa12x2_memCb_of_bdd {k : ℕ} {f : Euc d → ℝ} (hf : ContDiff ℝ k f) {K : ℝ}
    (hK : ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ K) : MemCb k f :=
  ⟨hf, fun j hj => ⟨K, by rintro _ ⟨x, rfl⟩; exact hK j hj x⟩⟩

theorem sa12x2_cb_le {k : ℕ} {f : Euc d → ℝ} {K : ℝ} (hK : ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ K) :
    cbNorm k f ≤ (k + 1) * K := by
  unfold cbNorm
  have h : ∀ j ∈ Finset.range (k + 1), (⨆ z : Euc d, ‖iteratedFDeriv ℝ j f z‖) ≤ K := fun j hj =>
    ciSup_le fun z => hK j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) z
  refine (Finset.sum_le_card_nsmul _ _ K h).trans ?_
  simp

/-- Real form of N2. -/
theorem sa12x2_comm_real (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ (d : ℝ) - 1) :
    ∃ C C₀ : ℝ, 0 ≤ C ∧ 0 ≤ C₀ ∧ ∀ (i j : Fin d) (R : ℝ), 1 ≤ R → ∀ w : Euc d → ℝ, MemCb 2 w →
      ∀ (c : Euc d) (v : Euc d → ℝ), MemCb 2 v → Function.support v ⊆ closedBall c R →
      Real.sqrt (∫ x, ((closedBall c R).indicator (fun x => w x * hessRiesz d s i j v x -
        hessRiesz d s i j (fun y => w y * v y) x) x) ^ 2) ≤
        C * cbNorm 2 w * R ^ C₀ * Real.sqrt (∫ x, v x ^ 2) := by
  obtain ⟨C, C₀, hC, hC₀, h⟩ := hess_comm_finite d hd s hs0 hs1
  refine ⟨C, C₀, hC.le, hC₀, fun i j R hR w hw c v hv hsupp => ?_⟩
  have hsd : s < d := by linarith
  obtain ⟨hv2, hvc⟩ := sa12z3_memCb_cc hv hsupp
  have hw2 : ContDiff ℝ 2 w := by simpa using hw.1
  have hcont : Continuous (fun x => w x * hessRiesz d s i j v x -
      hessRiesz d s i j (fun y => w y * v y) x) :=
    (hw2.continuous.mul (sa12n_hess_continuous hs0 hsd i j hv2 hvc)).sub
      (sa12n_hess_continuous hs0 hsd i j (hw2.mul hv2) hvc.mul_left)
  have hR0 : 0 < R := by linarith
  have hcb := sa12z3_cb_nonneg hw
  refine sa12z3_l2_of_eLp (sa12z3_memLp_ind hcont c R) (hv2.continuous.memLp_of_hasCompactSupport hvc)
    (by positivity) ?_
  exact h i j R hR w hw c v hv hsupp c R le_rfl

/-- Cauchy-Schwarz for a function supported in a ball. -/
theorem sa12x2_pairU {c : Euc d} {R : ℝ} {U X : Euc d → ℝ} (hU : Continuous U)
    (hUc : HasCompactSupport U) (hUs : Function.support U ⊆ closedBall c R) (hX : Continuous X) :
    |∫ x, U x * X x| ≤ Real.sqrt (∫ x, U x ^ 2) *
      Real.sqrt (∫ x, ((closedBall c R).indicator X x) ^ 2) := by
  have hUL : MemLp U 2 volume := hU.memLp_of_hasCompactSupport hUc
  have hgL : MemLp ((closedBall c R).indicator X) 2 volume := sa12z3_memLp_ind hX c R
  have hpt : ∀ x, U x * X x = U x * (closedBall c R).indicator X x := by
    intro x
    by_cases hx : x ∈ closedBall c R
    · simp [Set.indicator, hx]
    · have : U x = 0 := by
        by_contra h
        exact hx (hUs (Function.mem_support.2 h))
      simp [this]
  simp_rw [hpt]
  exact HRS.MS.UniqN3a.cs_real hUL hgL

/-- The matrix Hessian integral as a double sum. -/
theorem sa12x2_int_mH (s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (U v : Euc d → ℝ)
    (hI : ∀ i j : Fin d, Integrable (fun x => U x * hessRiesz d s i j v x) volume) :
    ∫ x, U x * matrixHess d s M v x =
      ∑ i, ∑ j, M j i * ∫ x, U x * hessRiesz d s i j v x := by
  have e : ∀ x, U x * matrixHess d s M v x =
      ∑ i, ∑ j, M j i * (U x * hessRiesz d s i j v x) := by
    intro x
    unfold matrixHess
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp_rw [e]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => (hI i j).const_mul _)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => (hI i j).const_mul _)]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

end HRS.MH.AdjointRd.Phase2SA12Near
