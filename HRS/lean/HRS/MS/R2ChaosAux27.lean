import HRS.MS.R2ChaosAux26

/-!
# HRS.MS.R2ChaosAux27 -- concatenation of finitely many finite-rank kernels into one test list

Packet S94 (R1, part 3), namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.

Finitely many finite-rank kernels `r2FiniteRankKernel (c n) (u n)` (`n < K`) are rewritten with one common list of tests
`u' : Fin N → Euc d → ℝ` and coefficient matrices `c' n`; this makes a measurable choice of the index `n` a measurable
coefficient function of a single flat finite-rank kernel.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole

variable {d : ℕ}

theorem s94_concat {K : ℕ} (sz : Fin K → ℕ) (c : ∀ n, Fin (sz n) → Fin (sz n) → ℝ)
    (u : ∀ n, Fin (sz n) → Euc d → ℝ) (hsym : ∀ n a b, c n a b = c n b a)
    (hu : ∀ n a, IsR2Test (u n a)) :
    ∃ (N : ℕ) (u' : Fin N → Euc d → ℝ) (c' : Fin K → Fin N → Fin N → ℝ),
      (∀ a, IsR2Test (u' a)) ∧ (∀ n a b, c' n a b = c' n b a) ∧
      ∀ n x y, r2FiniteRankKernel (c' n) u' x y = r2FiniteRankKernel (c n) (u n) x y := by
  classical
  let ι := Σ n : Fin K, Fin (sz n)
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have he : ∀ p, e.symm (e p) = p := fun p => e.symm_apply_apply p
  refine ⟨Fintype.card ι, fun a => u (e.symm a).1 (e.symm a).2,
    fun n a b => ∑ i : Fin (sz n), ∑ j : Fin (sz n),
      if e ⟨n, i⟩ = a ∧ e ⟨n, j⟩ = b then c n i j else 0, fun a => hu _ _, ?_, ?_⟩
  · intro n a b
    beta_reduce
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h1 : e ⟨n, i⟩ = a ∧ e ⟨n, j⟩ = b
    · have h2 : e ⟨n, j⟩ = b ∧ e ⟨n, i⟩ = a := ⟨h1.2, h1.1⟩
      simp [h1, h2, hsym n i j]
    · have h2 : ¬ (e ⟨n, j⟩ = b ∧ e ⟨n, i⟩ = a) := fun h => h1 ⟨h.2, h.1⟩
      simp [h1, h2]
  · intro n x y
    unfold r2FiniteRankKernel
    simp only [Finset.sum_mul]
    calc _ = ∑ a, ∑ i : Fin (sz n), ∑ j : Fin (sz n), ∑ b, (if e ⟨n, i⟩ = a ∧ e ⟨n, j⟩ = b then c n i j else 0) *
          u (e.symm a).1 (e.symm a).2 x * u (e.symm b).1 (e.symm b).2 y :=
          Finset.sum_congr rfl fun a _ => by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i : Fin (sz n), ∑ a, ∑ j : Fin (sz n), ∑ b, (if e ⟨n, i⟩ = a ∧ e ⟨n, j⟩ = b then c n i j else 0) *
          u (e.symm a).1 (e.symm a).2 x * u (e.symm b).1 (e.symm b).2 y := Finset.sum_comm
      _ = ∑ i : Fin (sz n), ∑ j : Fin (sz n), ∑ a, ∑ b, (if e ⟨n, i⟩ = a ∧ e ⟨n, j⟩ = b then c n i j else 0) *
          u (e.symm a).1 (e.symm a).2 x * u (e.symm b).1 (e.symm b).2 y :=
          Finset.sum_congr rfl fun i _ => Finset.sum_comm
      _ = ∑ i : Fin (sz n), ∑ j : Fin (sz n), c n i j * u n i x * u n j y := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_eq_single (e ⟨n, i⟩)]
          · rw [Finset.sum_eq_single (e ⟨n, j⟩)]
            · rw [if_pos ⟨rfl, rfl⟩, he ⟨n, i⟩, he ⟨n, j⟩]
            · intro b _ hb
              simp [Ne.symm hb]
            · simp
          · intro a _ ha
            simp [Ne.symm ha]
          · simp

end HRS.MS.R2Chaos
