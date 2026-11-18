import HRS.Sections.Sec7Fields
import HRS.Equilibrium.FieldSingAux

/-!
# Packet L2C-7: from test functions to the operator form on the real Fourier modes (proof)

Relocated proof of `HRS.MC.L2Cov.l2cs_mode_form` (the frozen statement stays `sorry` in `HRS/MC/L2CovSpec.lean`;
the tie is in `HRS/MC/L2C7Tie.lean`).  Route: for a finite set `S` of nonzero frequencies and coefficients `a`, the
trigonometric polynomial `φ = ∑_{k∈S} a_k e_k` is smooth; `NegSobolev.eval` on it is `∑_{k∈S} a_k F̂(k)`
(`HRS.FieldSingAux.eval_trigPoly`); and `‖φ‖²_{L²} = ∑_{k∈S} a_k²` (`HRS.FieldSingAux.integral_trigPoly_sq`, from
orthonormality of the real modes).  Apply the hypothesis to `φ`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace MC

namespace L2C7

open HRS.Sec7

variable {d : ℕ}

theorem l2c7_proof {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (r : ℝ)
    (Z : Ω → NegSobolev d r) (K : ℝ)
    (h : ∀ φ : Torus d → ℝ, Torus.IsSmooth φ →
      MemLp (fun ω => NegSobolev.eval (Z ω) φ) 2 P ∧
        ∫ ω, NegSobolev.eval (Z ω) φ ^ 2 ∂P ≤ K * PDE.l2NormSq φ) :
    ∀ (S : Finset (NonzeroLattice d)) (a : NonzeroLattice d → ℝ),
      ∫ ω, (∑ k ∈ S, a k * NegSobolev.fourierCoeff (Z ω) k) ^ 2 ∂P ≤ K * ∑ k ∈ S, a k ^ 2 := by
  intro S a
  have hs : Torus.IsSmooth (HRS.FieldSingAux.trigPoly S a) :=
    HRS.FieldSingAux.isSmooth_trigPoly S a
  have hev : ∀ ω, NegSobolev.eval (Z ω) (HRS.FieldSingAux.trigPoly S a) =
      ∑ k ∈ S, a k * NegSobolev.fourierCoeff (Z ω) k :=
    fun ω => HRS.FieldSingAux.eval_trigPoly (Z ω) S a
  have hn : PDE.l2NormSq (HRS.FieldSingAux.trigPoly S a) = ∑ k ∈ S, a k ^ 2 :=
    HRS.FieldSingAux.integral_trigPoly_sq S a
  have key := (h _ hs).2
  simp_rw [hev] at key
  rw [hn] at key
  exact key

end L2C7

end MC

end HRS

end
