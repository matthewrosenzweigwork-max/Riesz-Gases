import HRS.MS.SA16SOp2

/-!
# S.A.16 (SA16Y3) Dc1: derivative-only coefficient class `SA16DerCoef` (decision (A), step 1)

`SA16DerCoef k B bc`: the same smoothness as `SA16BddCoef`, but the bound is only required for the
derivatives of order `1 ≤ j ≤ k` (no uniform bound on the coefficient itself).
`sa16y3_bdd_to_der`: every `SA16BddCoef` coefficient is an `SA16DerCoef` coefficient, so existing results survive.
No merged file is edited.
-/

noncomputable section
set_option autoImplicit false
open scoped ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R

/-- coefficients smooth with derivatives of order `1 ≤ j ≤ k` bounded by `B` (no bound on the coefficient) -/
structure SA16DerCoef {d : ℕ} (k : ℕ) (B : ℝ) (bc : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) : Prop where
  nonneg : 0 ≤ B
  smooth : ∀ i, ContDiff ℝ ∞ (bc i)
  bound : ∀ i, ∀ j, 1 ≤ j → j ≤ k → ∀ x, ‖iteratedFDeriv ℝ j (bc i) x‖ ≤ B

lemma sa16y3_bdd_to_der {d k : ℕ} {B : ℝ} {bc : Fin d → EuclideanSpace ℝ (Fin d) → ℝ}
    (h : SA16BddCoef k B bc) : SA16DerCoef k B bc :=
  { nonneg := h.nonneg
    smooth := h.smooth
    bound := fun i j _ hj x => h.bound i j hj x }

end HRS.Whole.AppendixA.Phase2SA16R
