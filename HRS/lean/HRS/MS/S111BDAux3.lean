import HRS.Prob.Metrics
import HRS.MS.R2InterpAux5

/-!
# S11.1 packet G1: Gaussian laws of the finite path projections
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S111BD

open HRS HRS.Whole

theorem s111_projection_gaussian (d : ℕ) (m T : ℝ) (hT : 0 < T)
    (μ : Measure (OscPath d m T)) [IsProbabilityMeasure μ]
    (hobs : ∀ (p : ℕ) (τ : Fin p → Set.Icc (0 : ℝ) T)
      (α : Fin p → MultiIndex d),
      HRS.IsCenteredGaussian (μ.map (HRS.MS.R2Interp.s102_obs (m := m) τ α))) :
    ∀ L : ℕ, HRS.IsCenteredGaussian
      (μ.map (HRS.MS.R2Interp.s102_Pj (d := d) (m := m) T hT L)) := by
  intro L
  classical
  set s := HRS.MS.R2Interp.s102_idx d L with hs
  let e : s ≃ Fin s.card := s.equivFin
  let pp : Fin s.card → ℕ × MultiIndex d := fun i => (e.symm i : s)
  let τ : Fin s.card → Set.Icc (0 : ℝ) T := fun i => HRS.MS.R2Interp.s102_node hT L (pp i).1
  let α : Fin s.card → MultiIndex d := fun i => (pp i).2
  let S : EuclideanSpace ℝ (Fin s.card) →L[ℝ] OscPath d m T :=
    ∑ i, (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin s.card) →L[ℝ] ℝ).smulRight
      (HRS.MS.R2Interp.s102_bpath (m := m) T L (pp i))
  have hPj : ∀ w, HRS.MS.R2Interp.s102_Pj (d := d) (m := m) T hT L w =
      S (HRS.MS.R2Interp.s102_obs (m := m) τ α w) := by
    intro w
    rw [HRS.MS.R2Interp.s102_Pj_decomp]
    simp only [S, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]
    rw [← Finset.sum_coe_sort s]
    exact (Equiv.sum_comp e.symm (fun x : s =>
      (HRS.MS.R2Interp.s102_ellp (m := m) hT L (x : ℕ × MultiIndex d)) w •
        HRS.MS.R2Interp.s102_bpath (m := m) T L (x : ℕ × MultiIndex d))).symm
  have hfun : (HRS.MS.R2Interp.s102_Pj (d := d) (m := m) T hT L : OscPath d m T → OscPath d m T) =
      fun w => S (HRS.MS.R2Interp.s102_obs (m := m) τ α w) := funext hPj
  have hmeas : Measurable (HRS.MS.R2Interp.s102_obs (m := m) τ α) :=
    (HRS.MS.R2Interp.s102_obs (m := m) τ α).continuous.measurable
  have hmap : μ.map (HRS.MS.R2Interp.s102_Pj (d := d) (m := m) T hT L) =
      (μ.map (HRS.MS.R2Interp.s102_obs (m := m) τ α)).map S := by
    rw [Measure.map_map S.continuous.measurable hmeas, hfun]
    rfl
  obtain ⟨hG, hc⟩ := hobs s.card τ α
  have := hG
  rw [hmap]
  refine ⟨inferInstance, fun Λ => ?_⟩
  rw [integral_map S.continuous.measurable.aemeasurable Λ.continuous.measurable.aestronglyMeasurable]
  exact hc (Λ.comp S)

end HRS.MS.S111BD
