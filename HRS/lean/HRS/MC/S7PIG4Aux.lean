import HRS.MC.S7PIDefs
import HRS.MC.S7PIS2RS

/-!
# Packet piG4, helpers: Riemann-Stieltjes congruence and the partition-sum bound
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIG4

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI

/-- cells of a partition of `[0,T]` lie in `[0,T]` -/
theorem S7PIG4_cell_bounds {T : ℝ} {n : ℕ} {u : Fin (n + 1) → ℝ} {τ : Fin n → ℝ} (hu : StrictMono u)
    (h0 : u 0 = 0) (hl : u (Fin.last n) = T) (htag : ∀ i : Fin n, u i.castSucc ≤ τ i ∧ τ i ≤ u i.succ)
    (i : Fin n) : 0 ≤ u i.castSucc ∧ u i.castSucc ≤ τ i ∧ τ i ≤ u i.succ ∧ u i.succ ≤ T := by
  refine ⟨?_, (htag i).1, (htag i).2, ?_⟩
  · rw [← h0]; exact hu.monotone (Fin.zero_le _)
  · rw [← hl]; exact hu.monotone (Fin.le_last _)

/-- a Riemann-Stieltjes limit only depends on the cells inside `[0,T]` -/
theorem S7PIG4_RS_congr {T : ℝ} {S S' : ℝ → ℝ → ℝ → ℝ} {I : ℝ} (hI : IsRS T S I)
    (h : ∀ τ a b, 0 ≤ a → a ≤ τ → τ ≤ b → b ≤ T → S τ a b = S' τ a b) : IsRS T S' I := by
  intro ε hε
  obtain ⟨δ, hδ, H⟩ := hI ε hε
  refine ⟨δ, hδ, fun n u τ hu h0 hl htag hmesh => ?_⟩
  have key := H n u τ hu h0 hl htag hmesh
  have e : ∑ i : Fin n, S' (τ i) (u i.castSucc) (u i.succ) = ∑ i : Fin n, S (τ i) (u i.castSucc) (u i.succ) :=
    Finset.sum_congr rfl fun i _ => by
      obtain ⟨a1, a2, a3, a4⟩ := S7PIG4_cell_bounds hu h0 hl htag i
      exact (h _ _ _ a1 a2 a3 a4).symm
  rw [e]; exact key

/-- a cellwise bound by an integral passes to the Riemann-Stieltjes limit -/
theorem S7PIG4_RS_bound {T : ℝ} (hT : 0 < T) {S : ℝ → ℝ → ℝ → ℝ} {I c : ℝ} (hI : IsRS T S I)
    (f : ℝ → ℝ) (hf : IntegrableOn f (Set.Icc 0 T)) (hc : 0 ≤ c)
    (hS : ∀ τ a b, 0 ≤ a → a ≤ τ → τ ≤ b → b ≤ T → |S τ a b| ≤ c * ∫ x in Set.Ioc a b, f x) :
    |I| ≤ c * ∫ x in Set.Ioc 0 T, f x := by
  by_contra hcon
  push_neg at hcon
  have hε : 0 < |I| - c * ∫ x in Set.Ioc 0 T, f x := by linarith
  obtain ⟨δ, hδ, H⟩ := hI _ hε
  obtain ⟨n, u, τ, hu, h0, hl, htag, hmesh⟩ := HRS.MC.Sec7.S7PIS2.S7PIS2_exists_partition hT hδ
  have key := H n u τ hu h0 hl htag hmesh
  have hsum : ∑ i : Fin n, ∫ x in Set.Ioc (u i.castSucc) (u i.succ), f x = ∫ x in Set.Ioc 0 T, f x := by
    have := HRS.MC.Sec7.S7PIS2.S7PIS2_partition_sum u hu f (by rw [h0, hl]; exact hf)
    rwa [h0, hl] at this
  have hle : |∑ i : Fin n, S (τ i) (u i.castSucc) (u i.succ)| ≤ c * ∫ x in Set.Ioc 0 T, f x := by
    calc |∑ i : Fin n, S (τ i) (u i.castSucc) (u i.succ)|
        ≤ ∑ i : Fin n, |S (τ i) (u i.castSucc) (u i.succ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin n, c * ∫ x in Set.Ioc (u i.castSucc) (u i.succ), f x := by
          refine Finset.sum_le_sum fun i _ => ?_
          obtain ⟨a1, a2, a3, a4⟩ := S7PIG4_cell_bounds hu h0 hl htag i
          exact hS _ _ _ a1 a2 a3 a4
      _ = c * ∫ x in Set.Ioc 0 T, f x := by rw [← Finset.mul_sum, hsum]
  have h1 := abs_sub_abs_le_abs_sub I (∑ i : Fin n, S (τ i) (u i.castSucc) (u i.succ))
  have h2 := abs_sub_comm I (∑ i : Fin n, S (τ i) (u i.castSucc) (u i.succ))
  linarith

end HRS.MC.Sec7.S7PIG4

end
