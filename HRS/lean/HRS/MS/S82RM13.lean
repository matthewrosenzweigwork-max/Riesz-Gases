import HRS.MS.S82RM12

/-!
# S8.2 R02 (S82R), M13: the position-weighted comparison of two one-site specifications
For a supersolution `rho` of `(1-1/n) rho + ((n-1)/n) Gam rho <= rho - b/n`:
`P(x_i0 in A) - P'(x_i0 in A) <= int_A rho dmu`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Function
open scoped ENNReal BigOperators Classical

namespace HRS.MS.S82R
open HRS.External

variable {E : Type*} [MeasurableSpace E] {n : ℕ}

/-- The initial weight `1_A` at site `i0`. -/
def s82r_W0 (i0 : Fin n) (A : Set E) : Fin n → E → ℝ :=
  fun ℓ => if ℓ = i0 then A.indicator (fun _ => (1 : ℝ)) else fun _ => 0

lemma s82r_W0_ok (i0 : Fin n) {A : Set E} (hA : MeasurableSet A) : s82r_WOK (s82r_W0 i0 A) where
  meas := fun ℓ => by
    unfold s82r_W0; split_ifs
    · exact measurable_const.indicator hA
    · exact measurable_const
  nonneg := fun ℓ z => by
    unfold s82r_W0; split_ifs
    · exact Set.indicator_nonneg (fun _ _ => zero_le_one) z
    · exact le_rfl
  bdd := fun ℓ => ⟨1, fun z => by
    unfold s82r_W0; split_ifs
    · by_cases hz : z ∈ A <;> simp [Set.indicator, hz]
    · exact zero_le_one⟩

end HRS.MS.S82R

end
