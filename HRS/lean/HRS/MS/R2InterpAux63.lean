import HRS.MS.R2InterpAux24
import HRS.MC.S7PIG5Core

/-!
# S10.2 (worker S102), part 63 (packet G5, bounded-variation version): the `𝒥` Riemann--Stieltjes integral against a cumulative tensor path of bounded variation

The Lipschitz hypothesis of `s102_RS_J` is replaced by bounded variation: in the whole space `η_N^u` is not uniformly bounded, so the cumulative path of
`𝒥_{η_N}` is only controlled by `‖𝒥‖_TV ≤ K ∫_0^T ‖η_N^u‖_F du` (S10.1).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.Sec7 HRS.MC.Sec7.S7PIG5

theorem s102_fin_tele {n : ℕ} (w : Fin (n + 1) → ℝ) :
    ∑ i : Fin n, (w i.succ - w i.castSucc) = w (Fin.last n) - w 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    have := ih (fun i => w i.castSucc)
    simp only [Fin.succ_castSucc, Fin.succ_last, Fin.castSucc_zero] at this ⊢
    rw [this]
    simp

/-- A bound of the Riemann--Stieltjes terms by the increments of a function `v` bounds the integral by `C (v T - v 0)`. -/
theorem s102_rs_bound_mono {T : ℝ} (hT : 0 < T) {S : ℝ → ℝ → ℝ → ℝ} {I C : ℝ} (v : ℝ → ℝ)
    (h : HRS.Sec7.IsRS T S I)
    (hS : ∀ τ a b, 0 ≤ a → a ≤ τ → τ ≤ b → b ≤ T → |S τ a b| ≤ C * (v b - v a)) :
    |I| ≤ C * (v T - v 0) := by
  refine le_of_forall_pos_le_add (fun ε hε => ?_)
  obtain ⟨δ, hδ, H⟩ := h ε hε
  obtain ⟨n, u, τ, hu, hu0, huT, htag, hmesh⟩ := HRS.MC.Sec7.S7PIS2.S7PIS2_exists_partition hT hδ
  have hlt := H n u τ hu hu0 huT htag hmesh
  have hbnd : |∑ i : Fin n, S (τ i) (u i.castSucc) (u i.succ)| ≤ C * (v T - v 0) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i : Fin n, |S (τ i) (u i.castSucc) (u i.succ)|
        ≤ ∑ i : Fin n, C * (v (u i.succ) - v (u i.castSucc)) := Finset.sum_le_sum fun i _ => by
          have ha : 0 ≤ u i.castSucc := by
            have := hu.monotone (Fin.zero_le i.castSucc)
            rwa [hu0] at this
          have hb : u i.succ ≤ T := by
            have := hu.monotone (Fin.le_last i.succ)
            rwa [huT] at this
          exact hS _ _ _ ha (htag i).1 (htag i).2 hb
      _ = C * (v T - v 0) := by
          rw [← Finset.mul_sum, s102_fin_tele (fun i => v (u i)), huT, hu0]
  have h1 : |I| ≤ |∑ i : Fin n, S (τ i) (u i.castSucc) (u i.succ)| +
      |∑ i : Fin n, S (τ i) (u i.castSucc) (u i.succ) - I| := by
    have := abs_sub_abs_le_abs_sub I (∑ i : Fin n, S (τ i) (u i.castSucc) (u i.succ))
    rw [abs_sub_comm] at this
    linarith [abs_sub_comm I (∑ i : Fin n, S (τ i) (u i.castSucc) (u i.succ))]
  linarith

end HRS.MS.R2Interp

end
