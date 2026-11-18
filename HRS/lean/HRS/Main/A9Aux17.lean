import HRS.Main.A9Aux16

/-!
# Packet A9, part 17: the per-`N` field bound with the rate `fieldRate`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A9

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

open HRS HRS.A33 HRS.PDE HRS.Main.A8P HRS.GF HRS.Uniform

variable {d : ℕ}

section Cost

variable {S : MainData d} {Ca Cq Cp Λ₁ Λ : ℝ}

theorem a9_cost_le (hCa : 0 ≤ Ca) (hCq : 0 ≤ Cq) (hCp : 0 ≤ Cp) (hΛ : 1 ≤ Λ) {N : ℕ} (hN : 1 ≤ N)
    {E t Kb : ℝ} (hE : 0 ≤ E) {q : ℕ} {k : Fin q → NonzeroLattice d} (hk : Function.Injective k)
    (hKb : ∑' j, a9K d Λ₁ t j ≤ Kb) :
    a8pCovCost S N Cq Cp Ca Λ₁ Λ E (fun _ : Fin q => t) (fun a => a9phi d (k a)) ≤
      2 * (S.sigma N ^ 2 * S.invβ N / N) * (S.T * Cq * (2 * d * Ca ^ 2 * smearScale d N Λ +
        Cp * Real.sqrt E)) * Kb ^ 2 := by
  have hT := S.hT.le
  have hq0 : 0 ≤ S.sigma N ^ 2 * S.invβ N / N := by
    have := S.hinvβ N
    positivity
  have hsm : 0 ≤ smearScale d N Λ := by
    unfold smearScale
    exact Real.rpow_nonneg (by have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; positivity) _
  set c : ℝ := 2 * (S.sigma N ^ 2 * S.invβ N / N) * (S.T * Cq * (2 * d * Ca ^ 2 * smearScale d N Λ +
    Cp * Real.sqrt E)) with hc
  have hc0 : 0 ≤ c := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have := Real.sqrt_nonneg E
    positivity
  have hsum : ∑ a : Fin q, a9K d Λ₁ t (k a) ≤ Kb := by
    refine le_trans ?_ hKb
    have h1 : ∑ a : Fin q, a9K d Λ₁ t (k a) = ∑ j ∈ Finset.univ.image k, a9K d Λ₁ t j :=
      (Finset.sum_image (fun a _ b _ h => hk h)).symm
    rw [h1]
    exact (a9K_summable (d := d) Λ₁ t).sum_le_tsum _ (fun j _ => a9K_nonneg _ _ j)
  have hsum0 : 0 ≤ ∑ a : Fin q, a9K d Λ₁ t (k a) := Finset.sum_nonneg fun a _ => a9K_nonneg _ _ _
  have heq : a8pCovCost S N Cq Cp Ca Λ₁ Λ E (fun _ : Fin q => t) (fun a => a9phi d (k a)) =
      c * (∑ a : Fin q, a9K d Λ₁ t (k a)) ^ 2 := by
    unfold a8pCovCost
    rw [show (∑ a : Fin q, a9K d Λ₁ t (k a)) ^ 2 =
      (∑ a : Fin q, a9K d Λ₁ t (k a)) * (∑ a : Fin q, a9K d Λ₁ t (k a)) from sq _,
      Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    simp only [hc, a9K]
    ring
  rw [heq]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsum0 hsum 2) hc0

end Cost

end HRS.Main.A9
