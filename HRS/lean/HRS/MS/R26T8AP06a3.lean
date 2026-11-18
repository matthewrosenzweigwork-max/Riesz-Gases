import HRS.MS.R26T8AP06a2

/-!
# S8.2 P06a infrastructure (3): iterated derivatives of a polynomial `v |-> sum_{l<m} c_l (v,...,v)`
Via the finite power series machinery of Mathlib: derivatives of order `>= m` vanish everywhere
(`HasFiniteFPowerSeriesOnBall.changeOrigin`), and the derivative of order `j < m` at `0` is `j! c_j` for symmetric `c_j`.
-/

set_option autoImplicit false
noncomputable section
open Real Filter Topology

namespace HRS.MS.R26T8A
open HRS

section Poly

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The polynomial with coefficient maps `c l`, `l < m`. -/
def r26t8a_p06_poly (m : ℕ) (c : (j : ℕ) → ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℝ) (v : E) : ℝ :=
  ∑ l ∈ Finset.range m, c l (fun _ => v)

/-- Its formal power series (truncated at `m`). -/
def r26t8a_p06_series (m : ℕ) (c : (j : ℕ) → ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℝ) :
    FormalMultilinearSeries ℝ E ℝ :=
  fun n => if n < m then c n else 0

theorem r26t8a_p06_poly_series (m : ℕ) (c : (j : ℕ) → ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℝ) :
    HasFiniteFPowerSeriesOnBall (r26t8a_p06_poly m c) (r26t8a_p06_series m c) 0 m ⊤ := by
  refine HasFiniteFPowerSeriesOnBall.mk' (fun n hn => ?_) (by simp) (fun y _ => ?_)
  · simp [r26t8a_p06_series, Nat.not_lt.2 hn]
  · simp only [r26t8a_p06_poly, zero_add]
    refine Finset.sum_congr rfl fun i hi => ?_
    simp [r26t8a_p06_series, Finset.mem_range.1 hi]

theorem r26t8a_p06_poly_contDiff (m : ℕ) (c : (j : ℕ) → ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℝ) :
    ContDiff ℝ ⊤ (r26t8a_p06_poly m c) := by
  unfold r26t8a_p06_poly
  exact ContDiff.sum fun l _ => (c l).contDiff.comp (contDiff_pi.2 fun _ => contDiff_id)

theorem r26t8a_p06_poly_high (m : ℕ) (c : (j : ℕ) → ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℝ)
    (j : ℕ) (hj : m ≤ j) (z : E) : iteratedFDeriv ℝ j (r26t8a_p06_poly m c) z = 0 := by
  have h0 := r26t8a_p06_poly_series m c
  have h1 := h0.changeOrigin (y := z) (by simp)
  ext v
  have := h1.toHasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace (n := j) v
  rw [zero_add] at this
  rw [this]
  simp [h1.finite j hj]

theorem r26t8a_p06_poly_zero (m : ℕ) (c : (j : ℕ) → ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℝ)
    (j : ℕ) (hj : j < m) (hsym : ∀ (σ : Equiv.Perm (Fin j)) (v : Fin j → E), c j (v ∘ σ) = c j v) :
    iteratedFDeriv ℝ j (r26t8a_p06_poly m c) 0 = (j.factorial : ℝ) • c j := by
  have h0 := r26t8a_p06_poly_series m c
  ext v
  have := h0.toHasFPowerSeriesOnBall.iteratedFDeriv_eq_sum_of_completeSpace (n := j) v
  rw [this]
  have hp : r26t8a_p06_series m c j = c j := by simp [r26t8a_p06_series, hj]
  rw [hp]
  have : ∀ σ : Equiv.Perm (Fin j), c j (fun i => v (σ i)) = c j v := fun σ => hsym σ v
  simp only [this, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin]
  simp

end Poly

end HRS.MS.R26T8A
