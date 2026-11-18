import HRS.MS.S113X2A2b
import HRS.MC.CepP3Aux14

/-!
# S11.3 X2 part A2c: the interior density of the killed space-time measure (parabolic Weyl lemma)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113X2

open HRS HRS.Whole

variable {d N : ℕ}

open Classical in
/-- Weyl's lemma applied to the killed space-time measure: a smooth nonnegative density on `(0,T) × D`. -/
theorem s113a_weyl_density {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {s q β : ℝ} (hβ : 0 < β) {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hX : MovParticleSetup P d s q β N X₀ W X)
    (D : Set (EucConfig d N)) (hD : IsOpen D) (hfree : D ⊆ (eucCollisionSet d N)ᶜ)
    (chi : EucConfig d N → ℝ) (hchi : Measurable chi)
    (hchi0 : ∀ z, 0 ≤ chi z) (hchi1 : ∀ z, chi z ≤ 1) :
    ∃ f : ℝ × EucConfig d N → ℝ, ContDiffOn ℝ ∞ f (Set.Ioo 0 T ×ˢ D) ∧
      (∀ p ∈ Set.Ioo 0 T ×ˢ D, 0 ≤ f p) ∧
      (s113a_killedSpacetime P D X₀ X chi T).restrict (Set.Ioo 0 T ×ˢ D) =
        (volume.restrict (Set.Ioo 0 T ×ˢ D)).withDensity (fun p => ENNReal.ofReal (f p)) := by
  obtain ⟨hae, hfin, hweak⟩ := s113a_killed_weak_fpe hβ hT hX D hD hfree chi hchi hchi0 hchi1
  have hO : IsOpen (Set.Ioo 0 T ×ˢ D) := isOpen_Ioo.prod hD
  have hb : ContDiffOn ℝ ∞ (s113a_drift d s q β N) (Set.Ioo 0 T ×ˢ D) := by
    have h1 : ContDiffOn ℝ ∞ (fun x : EucConfig d N => fun i => particleDriftW (quadraticGradientDyn d s q β) x i)
        D := (s113a_drift_contDiffOn (N := N) s q β).mono hfree
    exact h1.comp contDiff_snd.contDiffOn (fun p hp => hp.2)
  haveI := hfin
  exact HRS.MC.CepP3.weyl_cov hO hb (inv_pos.2 hβ) (fun K _ _ => measure_lt_top _ _)
    (fun F hF hc hts => (hweak F hF hc hts).2)

end HRS.MS.S113X2

end
