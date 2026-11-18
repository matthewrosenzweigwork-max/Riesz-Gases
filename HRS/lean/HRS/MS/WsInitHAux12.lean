import HRS.MS.WsInitHAux11

/-!
# S21H packet H, part 12: the box hypothesis for the Hermite index set

`s21h_box_osc`: with `λ_α = 2|α| + d + 1` and `5d/4 < γ`: if `0 ≤ cb_k ≤ A (1+n)^{-5/4} λ_α^{-γ}` for `(n,α) = σ k` (`σ : ℕ ≃ ℕ × MultiIndex d`),
then `∃ K τ₀ ≥ 0, ∀ Q ≥ 1, ∃ I, |I| ≤ K Q² ∧ ∑_{k ∉ I} cb_k² ≤ τ₀² Q^{-3/2}`, exactly the box hypothesis of `s21h_init_w1`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal Real

namespace HRS.MS.S21

open HRS.Whole

theorem s21h_rpow_sq {x : ℝ} (hx : 0 ≤ x) (p : ℝ) : (x ^ p) ^ 2 = x ^ (2 * p) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  congr 1; push_cast; ring

theorem s21h_box_osc {d : ℕ} (hd1 : 1 ≤ d) (σ : ℕ ≃ ℕ × MultiIndex d) {γ : ℝ} (hγ : 5 * (d : ℝ) / 4 < γ)
    (cb : ℕ → ℝ) (hcb0 : ∀ k, 0 ≤ cb k) {A : ℝ}
    (hcb : ∀ k, cb k ≤ A * (((1 : ℝ) + ((σ k).1 : ℝ)) ^ (-(5 : ℝ) / 4) * oscEigenvalue d (σ k).2 ^ (-γ))) :
    ∃ K τ₀ : ℝ, 0 ≤ K ∧ 0 ≤ τ₀ ∧ ∀ Q : ℕ, 1 ≤ Q → ∃ I : Finset ℕ, (I.card : ℝ) ≤ K * (Q : ℝ) ^ 2 ∧
      ∑' k : ℕ, (if k ∈ I then 0 else cb k ^ 2) ≤ τ₀ ^ 2 / (Q : ℝ) ^ ((3 : ℝ) / 2) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  set V : MultiIndex d → ℝ := fun α => oscEigenvalue d α ^ (-(2 * γ)) with hV
  have hV0 : ∀ α, 0 ≤ V α := fun α => Real.rpow_nonneg (oscEv_pos α).le _
  have hVs : Summable V := (summable_oscEigenvalue_rpow_iff hd1 (2 * γ)).2 (by linarith)
  have hVs' : Summable fun α => V α ^ ((2 : ℝ) / 5) := by
    have h := (summable_oscEigenvalue_rpow_iff hd1 (4 * γ / 5)).2 (by linarith)
    refine h.congr fun α => ?_
    simp only [hV]
    rw [← Real.rpow_mul (oscEv_pos α).le]; congr 1; ring
  refine s21h_box_of_product σ (fun k => cb k ^ 2) (fun k => sq_nonneg _) hV0 hVs (B := A ^ 2)
    (sq_nonneg _) ?_ hVs'
  intro k
  have hn : 0 ≤ ((1 : ℝ) + ((σ k).1 : ℝ)) ^ (-(5 : ℝ) / 4) := Real.rpow_nonneg (by positivity) _
  have hl : 0 ≤ oscEigenvalue d (σ k).2 ^ (-γ) := Real.rpow_nonneg (oscEv_pos _).le _
  have h1 : cb k ^ 2 ≤ (A * (((1 : ℝ) + ((σ k).1 : ℝ)) ^ (-(5 : ℝ) / 4) * oscEigenvalue d (σ k).2 ^ (-γ))) ^ 2 :=
    pow_le_pow_left₀ (hcb0 k) (hcb k) 2
  refine h1.trans (le_of_eq ?_)
  rw [mul_pow, mul_pow, s21h_rpow_sq (by positivity), s21h_rpow_sq (oscEv_pos _).le]
  simp only [hV]
  congr 3 <;> ring

end HRS.MS.S21
