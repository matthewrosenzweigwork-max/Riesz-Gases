import HRS.MC.IID7
import HRS.MC.S7ChaosIIDVocab
import HRS.MC.S7E1Aux1
import HRS.MC.S7E3aAux1

/-!
# iid bridge, packet iid5, part B: the symmetric positive semidefinite covariance factor exists

`C_ij = susceptibilityCov (e_i) (e_j) = ⟪u_i, R u_j⟫` is a Gram matrix of the response operator `R`
(`e1a_resp`: self-adjoint, `0 ≤ R ≤ 1`) in the orthonormal family `u_i = [e_i]` of `L²(μ)`; the symmetric
factor is the matrix of the square root of `R` compressed to `ℓ²` (`exists_symm_factor`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace HRS.MC.IID

open HRS HRS.Sec7 HRS.MC.Sec7

variable {d : ℕ}

/-- **The symmetric positive semidefinite covariance factor exists** (`C^{1/2}` in the basis `e`). -/
theorem chaos_covariance_factor_exists_sym_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    {β : ℝ} (hβ : 0 < β) (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (e : ℕ → Torus d → ℝ)
    (he : IsONBL2Zero (withDensityReal ρ) e) :
    ∃ S : ℕ → ℕ → ℝ, s7_IsCovFactor d s β ρ e S ∧ (∀ i j, S i j = S j i) ∧
      ∀ (n : ℕ) (x : Fin n → ℝ), 0 ≤ ∑ i, ∑ j, x i * x j * S i j := by
  haveI := isProb_withDensityReal hρ.density
  obtain ⟨c, hc, -, R, hRs, hRle, hRge, hGram⟩ := E1Aux1.e1a_resp hd hs0 hsd hβ hρ
  have hu : Orthonormal ℝ (fun i => (he.memLp i).toLp (e i)) := E3Aux1.e3_orthonormal he
  have h0 : ∀ x, 0 ≤ inner ℝ (R x) x := fun x =>
    le_trans (mul_nonneg hc.le (sq_nonneg _)) (hRge x)
  obtain ⟨S, hsym, hsum, hpsd⟩ := exists_symm_factor (fun i => (he.memLp i).toLp (e i)) hu R hRs h0 hRle
  refine ⟨S, fun i j => ?_, hsym, hpsd⟩
  rw [hGram (he.memLp i) (he.memLp j) (he.centered i) (he.centered j)]
  exact hsum i j

end HRS.MC.IID
