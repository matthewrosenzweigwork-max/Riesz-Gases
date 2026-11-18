import HRS.Commutator.Torus.Layer
import HRS.Commutator.Torus.TLOWVAuxNRS
import HRS.Commutator.Torus.TLOWVAux7
import HRS.Commutator.Torus.TINHOMAux11

/-!
# Torus Lemmas 4.1 and 4.2 of the sub-Coulomb note (packet T-LOWV/T-INHOM, relocated)

`low_velocity_T` and `inhomogeneous_T` (Layer.lean) are proved here as `low_velocity_T_proof` and
`inhomogeneous_T_proof`, with the statements copied verbatim and tied by `type_of%`.  They cannot be proved in
place: the proofs use `nrs_T` (through `tlowv_nrs`, TLOWVAuxNRS), whose helper chain NRSTAux18-49 imports
`Layer.lean`.  The frozen statements in Layer.lean keep their `sorry`; downstream users take the `_proof` versions.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d N : ℕ} {s : ℝ}

theorem low_velocity_T_proof (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ (v : Torus d → Euc d) (K : ℝ),
      TorusSubTransport d s v K → ∀ σ : SMT d, σ.IsFinite → σ.mass = 0 →
        ENNReal.ofReal |CcommT (gloForceT s η) (PleqT η v) σ| ≤
          ENNReal.ofReal (C * K) * homSqT (-Whole.alphaE d s) (lowFreqT η 4 σ.coef) :=
  tlowv_main (tlowv_nrs hd hs0 hsd) hd hs0 hsd

theorem inhomogeneous_T_proof (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 → ∀ (v : Torus d → Euc d) (K : ℝ),
      TorusSubTransport d s v K → ∀ a : Torus d → ℝ, MemLp a 2 volume →
        ENNReal.ofReal |CcommFunT (ghiForceT s η) v a| ≤
          ENNReal.ofReal (C * K) *
            (ENNReal.ofReal (η ^ (-s)) * sobSqT η (-Whole.alphaE d s) (fun k => Torus.fcoef a k)) :=
  tinhom_main (tlowv_nrs hd hs0 hsd) hd hs0 hsd

example := (@low_velocity_T_proof : type_of% @low_velocity_T)
example := (@inhomogeneous_T_proof : type_of% @inhomogeneous_T)

end HRS.Commutator.TorusNote
