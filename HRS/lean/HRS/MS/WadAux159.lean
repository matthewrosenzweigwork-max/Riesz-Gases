import HRS.MS.WadAux158

/-!
# S8.3, packet S8G-10: assembly of `weighted_adjoint_decay` from the pair-inverse clause (5) alone

With clauses (2b), (3) (S8F) and (4b) (`s8g_clause4b`) proved, the frozen statement of `weighted_adjoint_decay` follows from the single
remaining open clause `S8eC5` (pair inverse): `s8g_wad_of_c5`.  Once `h5` is discharged:
`weighted_adjoint_decay_proof := fun hd a β ha hβ ρβ hρ M hM => s8g_wad_of_c5 hd ha hβ hρ hM h5`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8g_wad_of_c5 (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) {M : ℝ} (hM : 0 < M)
    (h5 : ∀ U, IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U → S8eC5 a β ρβ M U) :
    type_of% (@HRS.Whole.weighted_adjoint_decay d hd a β ha hβ ρβ hρ M hM) :=
  s8f_wad_of_pair hd ha hβ hρ hM (fun U hU => s8g_clause4b hd ha hβ hρ hM hU) h5

end HRS.MS.Wad
