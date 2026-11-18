import HRS.MC.CepH0Aux6
import HRS.MC.CepH0Aux8

/-!
# Packet CEPH0: additivity of the Fisher information and Gibbs entropy over disjoint open components
-/

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MC.CepH0

open HRS

theorem cep_H0_component_additivity_proof {N : ℕ} {D : DynData 1} {ι : Type*} [Fintype ι]
    (C : ι → Set (Config 1 N))
    (hCo : ∀ c, IsOpen (C c)) (hCd : Pairwise fun c c' => Disjoint (C c) (C c'))
    (hCc : (⋃ c, C c) = (collisionSet 1 N)ᶜ) (ν : ι → Measure (Config 1 N))
    [∀ c, IsProbabilityMeasure (ν c)]
    (hν : ∀ c, ν c (C c)ᶜ = 0) (p : ι → ℝ) (hp0 : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) :
    fisherInfo D N (∑ c, ENNReal.ofReal (p c) • ν c) = ∑ c, ENNReal.ofReal (p c) * fisherInfo D N (ν c) ∧
    gibbsEntropy D (∑ c, ENNReal.ofReal (p c) • ν c) =
      ∑ c, ((p c : ℝ) : EReal) * gibbsEntropy D (ν c) + ∑ c, (((p c * Real.log (p c)) : ℝ) : EReal) :=
  ⟨h0_fisher_mix D C hCo hCd hCc ν hν p hp0 hp1, h0_gibbsEntropy_mix D C hCo hCd ν hν p hp0 hp1⟩

end HRS.MC.CepH0
