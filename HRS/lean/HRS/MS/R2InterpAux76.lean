import HRS.MS.R2InterpAux66
import HRS.Dynamics.Setup
import HRS.Whole.Dynamics

/-!
# S10.2 (worker S102), part 76 (packet M1a): transfer of the realization hypotheses to the reweighted measure

`W` is only a.e.-measurable in `IsR2Realization`; a measurable version `W̃` (from the Brownian filtration) is used.  Everything is stated for generic
`W W̃ : ℝ≥0 → Ω → Fin N → Euc d` with `W̃ t` measurable and `W̃ = W` a.e. (all `t` simultaneously).
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole

variable {d N : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- A vector Brownian motion stays one after an a.e. modification with continuous paths. -/
theorem s102_vecBrownian_of_ae {P : Measure Ω} {W W' : ℝ≥0 → Ω → (Fin N → Euc d)}
    (hB : IsVectorBrownian P W) (hae : ∀ᵐ ζ ∂P, ∀ t, W' t ζ = W t ζ)
    (hcont : ∀ᵐ ζ ∂P, ∀ i j, Continuous fun t => W' t ζ i j) : IsVectorBrownian P W' := by
  obtain ⟨h1, h2⟩ := hB
  refine ⟨fun i j => ?_, ?_⟩
  · refine ⟨(h1 i j).toIsPreBrownianReal.congr (fun t => ?_), ?_⟩
    · filter_upwards [hae] with ζ hζ
      rw [hζ t]
    · filter_upwards [hcont] with ζ hζ using hζ i j
  · refine (iIndepFun_congr (fun ij => ?_)).1 h2
    filter_upwards [hae] with ζ hζ
    funext t
    rw [hζ t]

section Rew

variable (P : Measure Ω) [IsProbabilityMeasure P] {E : Type*} [MeasurableSpace E] (X0 : Ω → E) (hX0 : Measurable X0)
  (Q : Measure E) [IsProbabilityMeasure Q] (φ : E → ℝ≥0∞) (hφ : Measurable φ)
  (hpos : ∀ x, 0 < φ x) (hfin : ∀ x, φ x ≠ ⊤) (hlaw : P.map X0 = Q.withDensity φ)

include hX0 hφ hpos hfin hlaw

/-- The vector Brownian property is preserved by the reweighting. -/
theorem s102_vecBrownian_rew (W : ℝ≥0 → Ω → (Fin N → Euc d)) (hWm : ∀ t, Measurable (W t))
    (hind : IndepFun X0 (fun ζ t => W t ζ) P) (hB : IsVectorBrownian P W) :
    IsVectorBrownian (s102_rew P X0 φ) W := by
  haveI := s102_rew_prob P X0 hX0 Q φ hφ hpos hfin hlaw
  have hWp : Measurable (fun ζ t => W t ζ) := measurable_pi_iff.2 hWm
  obtain ⟨hmap, -⟩ := s102_rew_indep P X0 hX0 Q φ hφ hpos hfin hlaw (fun ζ t => W t ζ) hWp hind
  have hac : s102_rew P X0 φ ≪ P := withDensity_absolutelyContinuous _ _
  obtain ⟨h1, h2⟩ := hB
  refine ⟨fun i j => ?_, ?_⟩
  · refine ⟨⟨fun I => ?_⟩, ?_⟩
    · have hlawI := (h1 i j).toIsPreBrownianReal.hasLaw I
      have hg : Measurable (fun w : ℝ≥0 → Fin N → Euc d => I.restrict (fun t => w t i j)) := by
        refine measurable_pi_iff.2 (fun t => ?_)
        exact (EuclideanSpace.proj j).continuous.measurable.comp
          ((measurable_pi_apply (i : Fin N)).comp (measurable_pi_apply (t : ℝ≥0)))
      have e : (fun ζ => I.restrict (fun t => W t ζ i j)) =
          (fun w : ℝ≥0 → Fin N → Euc d => I.restrict (fun t => w t i j)) ∘ (fun ζ t => W t ζ) := rfl
      refine ⟨hlawI.aemeasurable.mono_ac hac, ?_⟩
      rw [← hlawI.map_eq, e, ← Measure.map_map hg hWp, ← Measure.map_map hg hWp, hmap]
    · exact hac.ae_le (h1 i j).cont
  · have hP'P : ∀ B : Set (ℝ≥0 → Fin N → Euc d), MeasurableSet B →
        s102_rew P X0 φ ((fun ζ t => W t ζ) ⁻¹' B) = P ((fun ζ t => W t ζ) ⁻¹' B) := by
      intro B hB
      have := congrArg (fun μ => μ B) hmap
      simpa [Measure.map_apply hWp hB] using this
    rw [iIndepFun_iff_measure_inter_preimage_eq_mul] at h2 ⊢
    intro S sets hsets
    have hg : ∀ ij : Fin N × Fin d, Measurable (fun w : ℝ≥0 → Fin N → Euc d => fun t => w t ij.1 ij.2) := by
      intro ij
      refine measurable_pi_iff.2 (fun t => ?_)
      exact (EuclideanSpace.proj ij.2).continuous.measurable.comp
        ((measurable_pi_apply ij.1).comp (measurable_pi_apply (t : ℝ≥0)))
    have hset : ∀ ij, (fun ζ t => W t ζ ij.1 ij.2) ⁻¹' sets ij =
        (fun ζ t => W t ζ) ⁻¹' ((fun w : ℝ≥0 → Fin N → Euc d => fun t => w t ij.1 ij.2) ⁻¹' sets ij) := fun ij => rfl
    have hmeas : ∀ ij ∈ S, MeasurableSet ((fun w : ℝ≥0 → Fin N → Euc d => fun t => w t ij.1 ij.2) ⁻¹' sets ij) :=
      fun ij hij => hg ij (hsets ij hij)
    have hinter : (⋂ ij ∈ S, (fun ζ t => W t ζ ij.1 ij.2) ⁻¹' sets ij) =
        (fun ζ t => W t ζ) ⁻¹' (⋂ ij ∈ S, (fun w : ℝ≥0 → Fin N → Euc d => fun t => w t ij.1 ij.2) ⁻¹' sets ij) := by
      ext ζ; simp [hset]
    have hmI : MeasurableSet (⋂ ij ∈ S, (fun w : ℝ≥0 → Fin N → Euc d => fun t => w t ij.1 ij.2) ⁻¹' sets ij) :=
      Finset.measurableSet_biInter S hmeas
    rw [hinter, hP'P _ hmI]
    have := h2 S hsets
    rw [hinter] at this
    rw [this]
    refine Finset.prod_congr rfl (fun ij hij => ?_)
    rw [hset ij, hP'P _ (hmeas ij hij)]

end Rew

end HRS.MS.R2Interp

end
