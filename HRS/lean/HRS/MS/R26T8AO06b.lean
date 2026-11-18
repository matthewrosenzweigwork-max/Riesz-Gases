import HRS.MS.R26T8AO06a

/-!
# S8.2 T8A O06 (part b): an exhaustion of the collision-free configurations
`V m = {‖x‖ < m+1, ‖x_i - x_j‖ > 1/(m+1)}` is open, contained in the compact `K m = {‖x‖ ≤ m+1, ‖x_i - x_j‖ ≥ 1/(m+1)}`
inside the collision-free set, and every compact collision-free set lies in `V m` for large `m`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set Metric
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d N : ℕ}

def r26t8a_o06_V (d N m : ℕ) : Set (EucConfig d N) :=
  {x | ‖x‖ < (m : ℝ) + 1 ∧ ∀ i j : Fin N, i ≠ j → 1 / ((m : ℝ) + 1) < ‖x i - x j‖}

def r26t8a_o06_K (d N m : ℕ) : Set (EucConfig d N) :=
  {x | ‖x‖ ≤ (m : ℝ) + 1 ∧ ∀ i j : Fin N, i ≠ j → 1 / ((m : ℝ) + 1) ≤ ‖x i - x j‖}

theorem r26t8a_o06_V_open (m : ℕ) : IsOpen (r26t8a_o06_V d N m) := by
  have : r26t8a_o06_V d N m = {x : EucConfig d N | ‖x‖ < (m : ℝ) + 1} ∩
      ⋂ i : Fin N, ⋂ j : Fin N, ⋂ (_ : i ≠ j), {x : EucConfig d N | 1 / ((m : ℝ) + 1) < ‖x i - x j‖} := by
    ext x; simp [r26t8a_o06_V]
  rw [this]
  refine IsOpen.inter (isOpen_lt continuous_norm continuous_const) ?_
  exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => isOpen_iInter_of_finite fun _ =>
    isOpen_lt continuous_const (((continuous_apply i).sub (continuous_apply j)).norm)

theorem r26t8a_o06_V_sub_K (m : ℕ) : r26t8a_o06_V d N m ⊆ r26t8a_o06_K d N m :=
  fun x hx => ⟨hx.1.le, fun i j hij => (hx.2 i j hij).le⟩

theorem r26t8a_o06_K_compact (m : ℕ) : IsCompact (r26t8a_o06_K d N m) := by
  have hc : IsClosed (r26t8a_o06_K d N m) := by
    have : r26t8a_o06_K d N m = {x : EucConfig d N | ‖x‖ ≤ (m : ℝ) + 1} ∩
        ⋂ i : Fin N, ⋂ j : Fin N, ⋂ (_ : i ≠ j), {x : EucConfig d N | 1 / ((m : ℝ) + 1) ≤ ‖x i - x j‖} := by
      ext x; simp [r26t8a_o06_K]
    rw [this]
    refine IsClosed.inter (isClosed_le continuous_norm continuous_const) ?_
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_le continuous_const (((continuous_apply i).sub (continuous_apply j)).norm)
  refine (isCompact_closedBall (0 : EucConfig d N) ((m : ℝ) + 1)).of_isClosed_subset hc ?_
  intro x hx
  simpa using hx.1

theorem r26t8a_o06_K_sub (m : ℕ) : r26t8a_o06_K d N m ⊆ (eucCollisionSet d N)ᶜ := by
  intro x hx ⟨i, j, hij, hxy⟩
  have h := hx.2 i j hij
  rw [hxy, sub_self, norm_zero] at h
  have : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
  linarith

theorem r26t8a_o06_exists_V {C : Set (EucConfig d N)} (hC : IsCompact C) (hCU : C ⊆ (eucCollisionSet d N)ᶜ) :
    ∃ m : ℕ, C ⊆ r26t8a_o06_V d N m := by
  obtain ⟨R, hR⟩ := hC.isBounded.exists_norm_le
  have hpair : ∀ p : Fin N × Fin N, ∃ n : ℕ, p.1 ≠ p.2 → ∀ x ∈ C, 1 / ((n : ℝ) + 1) < ‖x p.1 - x p.2‖ := by
    intro p
    by_cases hp : p.1 = p.2
    · exact ⟨0, fun h => absurd hp h⟩
    · rcases C.eq_empty_or_nonempty with rfl | hne
      · exact ⟨0, fun _ x hx => absurd hx (Set.notMem_empty x)⟩
      · have hcont : ContinuousOn (fun x : EucConfig d N => ‖x p.1 - x p.2‖) C :=
          (((continuous_apply p.1).sub (continuous_apply p.2)).norm).continuousOn
        obtain ⟨x0, hx0, hmin⟩ := hC.exists_isMinOn hne hcont
        have hpos : 0 < ‖x0 p.1 - x0 p.2‖ := by
          rw [norm_pos_iff, sub_ne_zero]
          intro h; exact hCU hx0 ⟨p.1, p.2, hp, h⟩
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
        exact ⟨n, fun _ x hx => lt_of_lt_of_le hn (hmin hx)⟩
  choose n hn using hpair
  obtain ⟨m1, hm1⟩ := exists_nat_gt R
  refine ⟨m1 + ∑ p : Fin N × Fin N, n p, fun x hx => ⟨?_, fun i j hij => ?_⟩⟩
  · have := hR x hx
    have : (R : ℝ) < (m1 : ℝ) + 1 := by linarith
    have h2 : (m1 : ℝ) ≤ ((m1 + ∑ p : Fin N × Fin N, n p : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_add_right _ _
    linarith [hR x hx]
  · have h1 := hn (i, j) hij x hx
    refine lt_of_le_of_lt ?_ h1
    have hle : n (i, j) ≤ m1 + ∑ p : Fin N × Fin N, n p :=
      (Finset.single_le_sum (fun p _ => Nat.zero_le (n p)) (Finset.mem_univ (i, j))).trans (Nat.le_add_left _ _)
    have : ((n (i, j) : ℕ) : ℝ) ≤ ((m1 + ∑ p : Fin N × Fin N, n p : ℕ) : ℝ) := by exact_mod_cast hle
    exact one_div_le_one_div_of_le (by positivity) (by linarith)

end HRS.MS.R26T8A

end
