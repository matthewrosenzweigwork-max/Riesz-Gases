import HRS.MS.R26T8AS00
import HRS.MS.R26T8AS03a

/-!
# S8.2 observed-time layer, packet T8A.S03: jointly measurable representative of an `L²(P)`-valued map

The generic representative lemma is `r26t8a_s03a_joint_rep`; this packet adds the `L²` norm identity.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS

theorem r26t8a_joint_representative {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P] (l u : ℝ) (hlu : l≤u)
    (V : ℝ → Lp ℝ 2 P) (hm : AEStronglyMeasurable V (volume.restrict (Set.Icc l u)))
    (he : (∫⁻ t in Set.Icc l u, ‖V t‖ₑ^2)<⊤) :
    ∃ G : ℝ → Omega → ℝ, Measurable (Function.uncurry G) ∧
      (∀ᵐ t ∂volume.restrict (Set.Icc l u), G t =ᵐ[P] (V t : Omega → ℝ)) ∧
      MemLp (Function.uncurry G) 2 ((volume.restrict (Set.Icc l u)).prod P) ∧
      (∫⁻ p, ‖G p.1 p.2‖ₑ^2 ∂((volume.restrict (Set.Icc l u)).prod P))=
        ∫⁻ t in Set.Icc l u, ‖V t‖ₑ^2 := by
  obtain ⟨G, hG, hGt⟩ := r26t8a_s03a_joint_rep (volume.restrict (Set.Icc l u)) P V hm
  have hnorm : (∫⁻ p, ‖G p.1 p.2‖ₑ^2 ∂((volume.restrict (Set.Icc l u)).prod P)) =
      ∫⁻ t in Set.Icc l u, ‖V t‖ₑ^2 := by
    have hmeas : AEMeasurable (fun p : ℝ × Omega => ‖G p.1 p.2‖ₑ ^ 2)
        ((volume.restrict (Set.Icc l u)).prod P) := (hG.enorm.pow_const 2).aemeasurable
    rw [lintegral_prod _ hmeas]
    refine lintegral_congr_ae ?_
    filter_upwards [hGt] with t ht
    calc ∫⁻ x, ‖G t x‖ₑ ^ 2 ∂P = ∫⁻ x, ‖(V t) x‖ₑ ^ 2 ∂P :=
          lintegral_congr_ae (ht.mono fun x h => by simp [h])
      _ = eLpNorm (V t) 2 P ^ 2 :=
          HRS.lintegral_enorm_sq_eq_eLpNorm_sq (Lp.aestronglyMeasurable (V t))
      _ = ‖V t‖ₑ ^ 2 := by rw [Lp.enorm_def]
  have hmem : MemLp (Function.uncurry G) 2 ((volume.restrict (Set.Icc l u)).prod P) := by
    rw [memLp_iff]
    have h1 := HRS.lintegral_enorm_sq_eq_eLpNorm_sq (μ := (volume.restrict (Set.Icc l u)).prod P)
      (f := Function.uncurry G) hG.aestronglyMeasurable
    have h2 : eLpNorm (Function.uncurry G) 2 ((volume.restrict (Set.Icc l u)).prod P) ^ 2 < ⊤ := by
      rw [← h1]
      exact hnorm ▸ he
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    rw [hcon] at h2
    simp at h2
  exact ⟨G, hG, hGt, hmem, hnorm⟩

end HRS.MS.R26T8A

end
