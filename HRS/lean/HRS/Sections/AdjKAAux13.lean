import HRS.Sections.AdjKAAux12

/-!
# ADJKA part 13: partitions through an intermediate time and the splitting of Riemann sums
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.AdjK

open HRS HRS.Uniform

/-- The partition of `[0,t]` through `s`, with `N+1` equal cells on `[0,s]` and on `[s,t]`. -/
def adjkCat (s t : ℝ) (N : ℕ) : Fin ((N + 1) + (N + 1) + 1) → ℝ := fun i =>
  (s * ((min (i : ℕ) (N + 1) : ℕ) : ℝ) + (t - s) * (((i : ℕ) - (N + 1) : ℕ) : ℝ)) / ((N : ℝ) + 1)

theorem adjkCat_zero (s t : ℝ) (N : ℕ) : adjkCat s t N 0 = 0 := by
  simp [adjkCat]

theorem adjkCat_last (s t : ℝ) (N : ℕ) : adjkCat s t N (Fin.last _) = t := by
  have hp : ((N : ℝ) + 1) ≠ 0 := by positivity
  simp only [adjkCat, Fin.val_last]
  have e1 : min (N + 1 + (N + 1)) (N + 1) = N + 1 := by omega
  have e2 : N + 1 + (N + 1) - (N + 1) = N + 1 := by omega
  rw [e1, e2]
  push_cast
  field_simp
  ring

theorem adjkCat_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (N : ℕ) : Monotone (adjkCat s t N) := by
  intro i j hij
  have h : (i : ℕ) ≤ (j : ℕ) := hij
  have h1 : ((min (i : ℕ) (N + 1) : ℕ) : ℝ) ≤ ((min (j : ℕ) (N + 1) : ℕ) : ℝ) := by
    exact_mod_cast min_le_min_right _ h
  have h2 : (((i : ℕ) - (N + 1) : ℕ) : ℝ) ≤ (((j : ℕ) - (N + 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_le_sub_right h _
  unfold adjkCat
  have hp : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have := sub_nonneg.2 hst
  gcongr

theorem adjkCat_step {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (N : ℕ) (i : Fin ((N + 1) + (N + 1))) :
    adjkCat s t N i.succ - adjkCat s t N i.castSucc ≤ t / ((N : ℝ) + 1) := by
  have hp : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  simp only [adjkCat, Fin.val_succ, Fin.val_castSucc]
  rw [← sub_div]
  rw [div_le_div_iff_of_pos_right hp]
  by_cases hi : (i : ℕ) < N + 1
  · have e1 : min ((i : ℕ) + 1) (N + 1) = (i : ℕ) + 1 := by omega
    have e2 : min (i : ℕ) (N + 1) = i := by omega
    have e3 : (i : ℕ) + 1 - (N + 1) = 0 := by omega
    have e4 : (i : ℕ) - (N + 1) = 0 := by omega
    rw [e1, e2, e3, e4]
    push_cast
    nlinarith
  · have e1 : min ((i : ℕ) + 1) (N + 1) = N + 1 := by omega
    have e2 : min (i : ℕ) (N + 1) = N + 1 := by omega
    have e3 : (i : ℕ) + 1 - (N + 1) = ((i : ℕ) - (N + 1)) + 1 := by omega
    rw [e1, e2, e3]
    push_cast
    nlinarith


theorem adjkGrid_nonneg_le {s : ℝ} (hs : 0 ≤ s) (N : ℕ) (i : Fin (N + 2)) :
    0 ≤ adjkGrid 0 s N i ∧ adjkGrid 0 s N i ≤ s := by
  have h0 := adjkGrid_zero 0 s N
  have h1 := adjkGrid_last 0 s N
  have hm := adjkGrid_mono hs N
  have a1 := hm (Fin.zero_le i)
  have a2 := hm (Fin.le_last i)
  rw [h0] at a1
  rw [h1] at a2
  exact ⟨a1, a2⟩

section RS

variable {Ω : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem adjka_rs_cat (V : ℝ → ℝ → E →L[ℝ] E) (M : ℝ → Ω → E) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hcoc : ∀ a b c : ℝ, 0 ≤ a → a ≤ b → b ≤ c → c ≤ t → (V c b).comp (V b a) = V c a) (N : ℕ) (ω : Ω) :
    riemannSum V (ContinuousLinearMap.id ℝ E) M t (adjkCat s t N) ω =
      V t s (riemannSum V (ContinuousLinearMap.id ℝ E) M s (adjkGrid 0 s N) ω) +
        riemannSum V (ContinuousLinearMap.id ℝ E) M t (adjkGrid s t N) ω := by
  have hp : ((N : ℝ) + 1) ≠ 0 := by positivity
  unfold riemannSum
  rw [Fin.sum_univ_add, map_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hv1 : adjkCat s t N (Fin.castAdd (N + 1) i).castSucc = adjkGrid 0 s N i.castSucc := by
      simp only [adjkCat, adjkGrid, Fin.val_castSucc, Fin.coe_castAdd]
      have e1 : min (i : ℕ) (N + 1) = i := by omega
      have e2 : (i : ℕ) - (N + 1) = 0 := by omega
      rw [e1, e2]; push_cast; ring
    have hv2 : adjkCat s t N (Fin.castAdd (N + 1) i).succ = adjkGrid 0 s N i.succ := by
      simp only [adjkCat, adjkGrid, Fin.val_succ, Fin.coe_castAdd]
      have e1 : min ((i : ℕ) + 1) (N + 1) = (i : ℕ) + 1 := by omega
      have e2 : (i : ℕ) + 1 - (N + 1) = 0 := by omega
      rw [e1, e2]; push_cast; ring
    rw [hv1, hv2]
    have hi := adjkGrid_nonneg_le hs N i.castSucc
    have := congrArg (fun L => L (((ContinuousLinearMap.id ℝ E)
      (M (adjkGrid 0 s N i.succ) ω - M (adjkGrid 0 s N i.castSucc) ω)))) (hcoc _ s t hi.1 hi.2 hst le_rfl)
    simpa using this.symm
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hv1 : adjkCat s t N (Fin.natAdd (N + 1) i).castSucc = adjkGrid s t N i.castSucc := by
      simp only [adjkCat, adjkGrid, Fin.val_castSucc, Fin.coe_natAdd]
      have e1 : min (N + 1 + (i : ℕ)) (N + 1) = N + 1 := by omega
      have e2 : N + 1 + (i : ℕ) - (N + 1) = i := by omega
      rw [e1, e2]; push_cast; field_simp
    have hv2 : adjkCat s t N (Fin.natAdd (N + 1) i).succ = adjkGrid s t N i.succ := by
      simp only [adjkCat, adjkGrid, Fin.val_succ, Fin.coe_natAdd]
      have e1 : min (N + 1 + (i : ℕ) + 1) (N + 1) = N + 1 := by omega
      have e2 : N + 1 + (i : ℕ) + 1 - (N + 1) = (i : ℕ) + 1 := by omega
      rw [e1, e2]; push_cast; field_simp
    rw [hv1, hv2]

end RS

end HRS.AdjK
