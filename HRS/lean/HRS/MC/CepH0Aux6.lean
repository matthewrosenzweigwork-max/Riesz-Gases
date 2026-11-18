import HRS.MC.CepH0Aux4
import HRS.MC.CepH0Aux5
import HRS.Appendix.CepaFlow

/-!
# Packet CEPH0, auxiliary 6: additivity of the Gibbs entropy over disjoint open components
-/

open MeasureTheory InformationTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MC.CepH0

open HRS

theorem h0_gibbsRef_cases {N : ℕ} (D : DynData 1) :
    IsProbabilityMeasure (gibbsRef D N) ∨ gibbsRef D N = 0 := by
  by_cases hZ : gibbsPartition D N = 0 ∨ gibbsPartition D N = ⊤
  · right
    rcases hZ with hZ | hZ
    · unfold gibbsRef
      have : (volume : Measure (Config 1 N)).withDensity (fun X => ENNReal.ofReal (gibbsWeight D X)) = 0 := by
        refine Measure.ext fun s _ => ?_
        rw [withDensity_apply']
        refine le_antisymm ?_ bot_le
        calc ∫⁻ a in s, ENNReal.ofReal (gibbsWeight D a) ≤ ∫⁻ a, ENNReal.ofReal (gibbsWeight D a) :=
              setLIntegral_le_lintegral _ _
          _ = 0 := hZ
      rw [this, smul_zero]
    · unfold gibbsRef; rw [hZ]; simp
  · left
    push_neg at hZ
    refine ⟨?_⟩
    unfold gibbsRef
    rw [Measure.smul_apply, withDensity_apply' _ Set.univ, Measure.restrict_univ]
    change (gibbsPartition D N)⁻¹ * gibbsPartition D N = 1
    exact ENNReal.inv_mul_cancel hZ.1 hZ.2

theorem h0_gibbsEntropy_mix {N : ℕ} (D : DynData 1) {ι : Type*} [Fintype ι] (C : ι → Set (Config 1 N))
    (hCo : ∀ c, IsOpen (C c)) (hCd : Pairwise fun c c' => Disjoint (C c) (C c'))
    (ν : ι → Measure (Config 1 N)) [∀ c, IsProbabilityMeasure (ν c)]
    (hν : ∀ c, ν c (C c)ᶜ = 0) (p : ι → ℝ) (hp0 : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) :
    gibbsEntropy D (∑ c, ENNReal.ofReal (p c) • ν c) =
      ∑ c, ((p c : ℝ) : EReal) * gibbsEntropy D (ν c) + ∑ c, (((p c * Real.log (p c)) : ℝ) : EReal) := by
  classical
  haveI := h0mix_prob p hp0 hp1 ν
  change gibbsEntropy D (h0mix p ν) = _
  unfold gibbsEntropy
  have hCm : ∀ c, MeasurableSet (C c) := fun c => (hCo c).measurableSet
  have hex : ∃ c, 0 < p c := by
    by_contra hcon
    push_neg at hcon
    have : ∑ c, p c = 0 := Finset.sum_eq_zero fun c _ => le_antisymm (hcon c) (hp0 c)
    rw [this] at hp1
    exact zero_ne_one hp1
  refine h0_ereal_mix (fun c => relEntropy (ν c) (gibbsRef D N)) (relEntropy (h0mix p ν) (gibbsRef D N))
    (Real.log (gibbsPartition D N).toReal) p hp0 hp1 ?_ ?_
  · rintro ⟨c, hc, hk⟩
    rcases h0_gibbsRef_cases (N := N) D with h | h
    · exact h0_klDiv_mix_top (gibbsRef D N) C hCm hCd ν hν p hp0 hp1 ⟨c, hc, hk⟩
    · unfold relEntropy; rw [h]; exact klDiv_zero_right
  · intro hfin
    rcases h0_gibbsRef_cases (N := N) D with h | h
    · exact h0_klDiv_mix_finite (gibbsRef D N) C hCm hCd ν hν p hp0 hp1 hfin
    · exfalso
      obtain ⟨c, hc⟩ := hex
      refine hfin c hc ?_
      unfold relEntropy; rw [h]; exact klDiv_zero_right

end HRS.MC.CepH0
