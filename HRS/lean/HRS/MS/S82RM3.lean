import HRS.External.Dobrushin
import HRS.MS.S82RM1

/-!
# S8.2 R02 (S82R), M3: one scan step of the position-weighted Lipschitz transfer
For two one-site specifications `S, S'` with conditional densities `kappa, kappa'` satisfying
`|kappa_i(x;z) - kappa'_i(y;z)| <= b z + sum_{l != i, x_l != y_l} (Gam z (x_l) + Gam z (y_l))`,
a pair `(F, F')` with `F x - F' y <= cost_W x y + k0` is mapped by the scan operators to a pair with
cost weights `S W` and constant `k0 + (1/n) sum_i int W_i b`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Function
open scoped ENNReal BigOperators Classical

namespace HRS.MS.S82R
open HRS.External

variable {E : Type*} [MeasurableSpace E] {n : ℕ}

/-- The position-weighted disagreement cost. -/
def s82r_cost (W : Fin n → E → ℝ) (x y : Fin n → E) : ℝ :=
  ∑ ℓ, if x ℓ = y ℓ then 0 else W ℓ (x ℓ) + W ℓ (y ℓ)

/-- `Γ`-transform of a weight. -/
def s82r_Gam (μ : Measure E) (Γ : E → E → ℝ) (W : E → ℝ) (u : E) : ℝ := ∫ z, W z * Γ z u ∂μ

/-- The weight recursion `S W`. -/
def s82r_Sw (μ : Measure E) (Γ : E → E → ℝ) (n : ℕ) (W : Fin n → E → ℝ) : Fin n → E → ℝ :=
  fun ℓ u => (1 - 1 / (n : ℝ)) * W ℓ u + (1 / (n : ℝ)) * ∑ i ∈ Finset.univ.erase ℓ, s82r_Gam μ Γ (W i) u

lemma s82r_cost_update (W : Fin n → E → ℝ) (x y : Fin n → E) (i : Fin n) (a b : E) :
    s82r_cost W (update x i a) (update y i b) =
      (if a = b then 0 else W i a + W i b) +
        ∑ ℓ ∈ Finset.univ.erase i, if x ℓ = y ℓ then 0 else W ℓ (x ℓ) + W ℓ (y ℓ) := by
  unfold s82r_cost
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun ℓ hℓ => ?_
    have h : ℓ ≠ i := Finset.ne_of_mem_erase hℓ
    simp [h]

structure s82r_WOK (W : Fin n → E → ℝ) : Prop where
  meas : ∀ ℓ, Measurable (W ℓ)
  nonneg : ∀ ℓ z, 0 ≤ W ℓ z
  bdd : ∀ ℓ, ∃ B : ℝ, ∀ z, W ℓ z ≤ B

lemma s82r_cost_nonneg {W : Fin n → E → ℝ} (hW : ∀ ℓ z, 0 ≤ W ℓ z) (x y : Fin n → E) :
    0 ≤ s82r_cost W x y :=
  Finset.sum_nonneg fun ℓ _ => by
    split_ifs
    · exact le_rfl
    · exact add_nonneg (hW _ _) (hW _ _)

end HRS.MS.S82R

end
