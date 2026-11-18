import HRS.Appendix.CepaFlow

/-!
# Packet CEPH4A: finite Gibbs entropy gives a density
-/

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MC.CepH4a

open HRS

theorem cep_H4a_density_of_entropy_proof {N : ℕ} {D : DynData 1} (hβ : 0 < D.invβ)
    (μ : Measure (Config 1 N))
    [IsProbabilityMeasure μ] (h : gibbsEntropy D μ < ⊤) : μ ≪ (volume : Measure (Config 1 N)) := by
  have hne : relEntropy μ (gibbsRef D N) ≠ ⊤ := by
    intro htop
    unfold gibbsEntropy at h
    rw [htop] at h
    simp at h
  have hac : μ ≪ gibbsRef D N := (InformationTheory.klDiv_ne_top_iff.mp hne).1
  refine hac.trans ?_
  unfold gibbsRef
  exact (Measure.AbsolutelyContinuous.smul_left (MeasureTheory.withDensity_absolutelyContinuous _ _) _)

end HRS.MC.CepH4a
