import HRS.Main.A8PAux14

/-!
# Packet A8P, part 15: the covariance discrepancy of the killed vector martingale, entrywise
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

variable {d : ℕ}

/-- The gradient field of the `a`-th transported test, cut off outside `[0, t_a]`. -/
def a8pG {q : ℕ} (ts : Fin q → ℝ) (f : Fin q → ℝ → Torus d → ℝ) (a : Fin q) (r : ℝ) (x : Torus d) :
    Euc d :=
  if r ∈ Set.Icc 0 (ts a) then Torus.grad (f a r) x else 0

theorem a8p_cov_entry_eq {Ω : Type*} {N q : ℕ} (hN : 1 ≤ N) (D : DynData d) (σ : ℝ)
    (ts : Fin q → ℝ) (f : Fin q → ℝ → Torus d → ℝ) (X : ℝ≥0 → Ω → Config d N)
    (ρ : ℝ → Torus d → ℝ) (r : ℝ) (ω : Ω) (a b : Fin q) :
    killedCovMatrix (fun a => a8pPhi D σ (ts a) (f a) X) ts r ω a b -
      a8pSigBar ts (a8pG ts f) ρ (2 * (σ ^ 2 * D.invβ / N)) r a b =
    if 0 ≤ r ∧ r < min (ts a) (ts b) then
      2 * (σ ^ 2 * D.invβ / N) *
        (∫ x, inner ℝ (Torus.grad (f a r) x) (Torus.grad (f b r) x) ∂(empirical (X (Real.toNNReal r) ω)) -
          ∫ x, inner ℝ (Torus.grad (f a r) x) (Torus.grad (f b r) x) * ρ r x)
    else 0 := by
  unfold killedCovMatrix a8pSigBar
  simp only [Matrix.of_apply]
  rw [a8pPhi_cov hN]
  by_cases h : 0 ≤ r ∧ r < min (ts a) (ts b)
  · have h1 : r ∈ Set.Icc 0 (ts a) := ⟨h.1, (lt_min_iff.1 h.2).1.le⟩
    have h2 : r ∈ Set.Icc 0 (ts b) := ⟨h.1, (lt_min_iff.1 h.2).2.le⟩
    rw [if_pos h.2, if_pos ⟨h1, h2⟩, if_pos h, if_pos h]
    have : ∀ x, inner ℝ (a8pG ts f a r x) (a8pG ts f b r x) =
        inner ℝ (Torus.grad (f a r) x) (Torus.grad (f b r) x) := by
      intro x; simp [a8pG, h1, h2]
    simp only [this]
    ring
  · rw [if_neg h]
    by_cases h' : r < min (ts a) (ts b)
    · have : ¬ (r ∈ Set.Icc 0 (ts a) ∧ r ∈ Set.Icc 0 (ts b)) := by
        rintro ⟨⟨h0, _⟩, _⟩
        exact h ⟨h0, h'⟩
      rw [if_pos h', if_neg this, if_neg h]; ring
    · rw [if_neg h', if_neg h]; ring

end HRS.Main.A8P
