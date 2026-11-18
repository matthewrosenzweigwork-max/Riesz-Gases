import HRS.MS.SA16Y4Ap2
import HRS.MS.SA16Y4Dr1
import HRS.MS.SA16Y4Ip1

/-!
# S.A.16 (SA16Y11) Bb: the interpolated truncated mollified drift is an individually bounded coefficient

`sa16y11_bcInt_bdd`: for a drift family `b` with the `AdjointRdData` drift bounds (`C^{m+2}`, `‖b r 0‖ ≤ A`, `‖D^j b r‖ ≤ L`),
`SA16BddCoef (m+1) (B' N) (bcInt N t b σ)` with `B'` depending on `m, d, A, L` only (this is the content of the `hbcB` step of `sa16y5_approx3`,
extracted so that the difference lemmas can be applied to the two coefficients separately).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16

section Bb
variable {d : ℕ}

theorem sa16y11_bcInt_bdd (d m : ℕ) {A L : ℝ} (hA0 : 0 ≤ A) (hL0 : 0 ≤ L) :
    ∃ B' : ℕ → ℝ, ∀ (t : ℝ), 0 < t → ∀ b : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d),
      (∀ r ∈ Icc (0 : ℝ) t, ContDiff ℝ ((m + 2 : ℕ) : WithTop ℕ∞) (b r) ∧ ‖b r 0‖ ≤ A ∧
        ∀ j, 1 ≤ j → j ≤ m + 2 → ∀ x, ‖iteratedFDeriv ℝ j (b r) x‖ ≤ L) →
      ∀ N : ℕ, 1 ≤ N → ∀ σ ∈ Icc (0 : ℝ) t, SA16BddCoef (m + 1) (B' N) (sa16y4_bcInt d N t b σ) := by
  obtain ⟨B, hB0, B', hFam⟩ := sa16y4_trunc_mol_coef d m hA0 hL0
  refine ⟨B', fun t ht b hb N hN σ hσ => ?_⟩
  have hcoef : ∀ i ∈ Finset.range (N + 1),
      SA16BddCoef (m + 1) (B' N) (fun j => sa16y4_tm d N (fun y => b (t - (i : ℝ) * t / N) y j)) := by
    intro i hi
    obtain ⟨hbs, hb0, hbL⟩ := hb _ (sa16y4_node_mem hN ht hi)
    have hbs1 : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (b (t - (i : ℝ) * t / N)) :=
      hbs.of_le (by exact_mod_cast Nat.le_succ _)
    have hcomp := fun j => sa16y4_comp_bounds (k := m + 1) (by omega) hbs1 hb0
      (fun k hk1 hkk x => hbL k hk1 (by omega) x) j
    exact (hFam N _ (fun j => (hcomp j).1) (fun j y => (hcomp j).2.1 y)
      (fun j k hk1 hkk x => (hcomp j).2.2 k hk1 hkk x)).2
  exact sa16y4_bddCoef_convex (Finset.range (N + 1)) (fun i => sa16y4_hat N t i σ)
    (fun i _ => sa16y4_hat_nonneg N t i σ) (sa16y4_hat_sum hN ht hσ)
    (c := fun i j => sa16y4_tm d N (fun y => b (t - (i : ℝ) * t / N) y j)) hcoef

end Bb

end HRS.Whole.AppendixA.Phase2SA16R

end
