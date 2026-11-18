import HRS.MC.SEdgeVocab
import HRS.Equilibrium.Parametrix.PX1AuxDeriv

/-!
# Packet B15d: permutation symmetry of the third derivative (relocation of `sed_B15d_d3_symm`)

Proof of the statement `HRS.MC.SEdge.sed_B15d_d3_symm` (SEdgeSpec.lean) in its own file.  The spec theorem
stays `sorry`; the `example` at the end ties this proof to it by `type_of%`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B15d

open HRS.Sec7

theorem sed_B15d_d3_symm_proof {p : ℕ} {f : EuclideanSpace ℝ (Fin p) → ℝ} (hf : ContDiff ℝ 3 f)
    (z : EuclideanSpace ℝ (Fin p)) (a b c : Fin p) :
    iteratedFDeriv ℝ 3 f z ![stdVec a, stdVec b, stdVec c] =
        iteratedFDeriv ℝ 3 f z ![stdVec b, stdVec a, stdVec c] ∧
      iteratedFDeriv ℝ 3 f z ![stdVec a, stdVec b, stdVec c] =
        iteratedFDeriv ℝ 3 f z ![stdVec a, stdVec c, stdVec b] := by
  have hz : ContDiffAt ℝ 3 f z := hf.contDiffAt
  have h01 := HRS.Parx.iteratedFDeriv_perm (n := 3) hz (Equiv.swap 0 1)
    ![stdVec a, stdVec b, stdVec c]
  have h12 := HRS.Parx.iteratedFDeriv_perm (n := 3) hz (Equiv.swap 1 2)
    ![stdVec a, stdVec b, stdVec c]
  have e01 : (![stdVec a, stdVec b, stdVec c] ∘ (Equiv.swap (0 : Fin 3) 1)) =
      ![stdVec b, stdVec a, stdVec c] := by
    funext i; fin_cases i <;> rfl
  have e12 : (![stdVec a, stdVec b, stdVec c] ∘ (Equiv.swap (1 : Fin 3) 2)) =
      ![stdVec a, stdVec c, stdVec b] := by
    funext i; fin_cases i <;> rfl
  rw [e01] at h01
  rw [e12] at h12
  exact ⟨h01.symm, h12.symm⟩

end HRS.MC.SEdge.B15d

end

