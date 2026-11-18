import HRS.MS.CanThmAux1
import HRS.Whole.CriticalNoise

/-!
# S8.8.P01: canonical law implies AEM, exchangeability, and a probability first marginal

`s88_canonical_map_facts`: if `law P X` is the canonical Gibbs ensemble then `X` is `P`-a.e. measurable (a non-AEM map
has the junk Dirac law at the pinned `Measure.map`, while the canonical ensemble has null singletons), the law is
exchangeable (canonical = modulated for the thermal density, and the modulated Gibbs law is exchangeable), and the first
marginal is a probability measure.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace HRS.MS.S88Breakdown

open HRS HRS.Whole

lemma s88_firstMarginal_prob {d N : ℕ} (hN : 1 ≤ N) {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → EucConfig d N) (hX : AEMeasurable X P) :
    IsProbabilityMeasure (HRS.Whole.firstMarginal (law P X)) := by
  haveI : IsProbabilityMeasure (law P X) := inferInstanceAs (IsProbabilityMeasure (P.map X))
  have hN' : 0 < N := hN
  unfold HRS.Whole.firstMarginal
  rw [dif_pos hN']
  exact inferInstanceAs (IsProbabilityMeasure ((law P X).map (fun Y : EucConfig d N => Y ⟨0, hN'⟩)))

theorem s88_canonical_map_facts {d N : ℕ} (hd : 2 ≤ d) (hN : 2 ≤ N)
    (a β : ℝ) (ha : 0 < a) (hβ : 0 < β)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → EucConfig d N)
    (hlaw : law P X = HRS.Whole.canonicalGibbs (rieszKernel d ((d : ℝ) / 2)) (confinement a) N β) :
    AEMeasurable X P ∧ HRS.Whole.IsExchangeable (law P X) ∧
      IsProbabilityMeasure (HRS.Whole.firstMarginal (law P X)) := by
  have hd1 : 1 ≤ d := by omega
  have hN1 : 1 ≤ N := by omega
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) < (d : ℝ) / 2 := by positivity
  have hsd : (d : ℝ) / 2 < d := by linarith
  have hcg := HRS.MS.Can2.can2_clause1_pos hd hs0 hsd ha hβ N
  have hexch : HRS.Whole.IsExchangeable
      (HRS.Whole.canonicalGibbs (rieszKernel d ((d : ℝ) / 2)) (confinement a) N β) := by
    rw [hcg]
    exact HRS.Whole.modulatedGibbs_isExchangeable _ _ _ (HRS.MS.Can2.can2_rieszKernel_neg _)
  have haem : AEMeasurable X P := by
    by_contra h
    have : Nonempty (Fin d) := ⟨⟨0, hd1⟩⟩
    have : Nonempty (Fin N) := ⟨⟨0, hN1⟩⟩
    have h1 : NullSingletonClass (volume : Measure (Euc d)) := inferInstance
    have : NullSingletonClass (volume : Measure (EucConfig d N)) := by
      rw [volume_pi]; exact Measure.pi_nullSingletonClass (μ := fun _ : Fin N => (volume : Measure (Euc d))) ⟨0, hN1⟩
    have h1 := hlaw
    rw [law, Measure.map_of_not_aemeasurable_of_ne_zero h (IsProbabilityMeasure.ne_zero P)] at h1
    set pt : EucConfig d N := Classical.ofNonempty with hpt
    have h2 : HRS.Whole.canonicalGibbs (rieszKernel d ((d : ℝ) / 2)) (confinement a) N β {pt} = 0 := by
      unfold HRS.Whole.canonicalGibbs
      rw [Measure.smul_apply, withDensity_apply _ (measurableSet_singleton pt)]
      rw [setLIntegral_measure_zero _ _ (measure_singleton pt)]
      simp
    have h3 : (Measure.dirac pt) {pt} = 1 := by simp
    rw [h1, h2] at h3
    simp at h3
  refine ⟨haem, hlaw ▸ hexch, s88_firstMarginal_prob hN1 P X haem⟩

end HRS.MS.S88Breakdown
