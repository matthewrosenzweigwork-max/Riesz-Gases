import HRS.MS.WadAux116

/-!
# S8.3, packet S8F-17: assembly of `weighted_adjoint_decay` from the two tensor clauses

With clauses (2b) and (3) proved for all `j` (`s8f_clause2b`, `s8f_clause3`), the frozen statement of `weighted_adjoint_decay` follows from the
two remaining open clauses `S8eC4b` ((4b)) and `S8eC5` ((5), pair inverse): `s8f_wad_of_pair`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8f_wad_of_pair (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) {M : ℝ} (hM : 0 < M)
    (h4b : ∀ U, IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U → S8eC4b a β ρβ M U)
    (h5 : ∀ U, IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U → S8eC5 a β ρβ M U) :
    type_of% (@HRS.Whole.weighted_adjoint_decay d hd a β ha hβ ρβ hρ M hM) :=
  s8e_wad_of_open hd ha hβ hρ hM (fun U hU => s8f_clause2b hd ha hβ hρ hM hU)
    (fun U hU => s8f_clause3 hd ha hβ hρ hM hU) h4b h5

end HRS.MS.Wad
