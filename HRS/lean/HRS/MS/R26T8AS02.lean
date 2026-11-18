import HRS.MS.R26T8AS00
import HRS.MS.R26T8AS02a

/-!
# S8.2 observed-time layer, packet T8A.S02: `L²` sections of a jointly measurable parameter family of integrands

The strong measurability of `t ↦ embL2 (H t) b` is the generic lemma `r26t8a_s02a_sections` (section map of a
jointly a.e. strongly measurable function; no separability of `L²` is assumed).  Here the clamp at `b` is removed
a.e. and the section map is lifted into the closed progressive span.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS

/-- joint a.e. strong measurability of the unclamped Euclidean-valued family on `μ × tsMeasure` -/
theorem r26t8a_s02_joint {Omega I : Type*} [mOmega : MeasurableSpace Omega] [Fintype I]
    (P : Measure Omega) [IsProbabilityMeasure P] (b l u : ℝ) (H : ℝ → ℝ → Omega → I → ℝ)
    (hm : AEStronglyMeasurable (fun p : (ℝ×ℝ)×Omega => H p.1.1 p.1.2 p.2)
      (((volume.restrict (Set.Icc l u)).prod (volume.restrict (Set.Icc 0 b))).prod P)) :
    AEStronglyMeasurable (Function.uncurry fun (t : ℝ) (q : ℝ × Omega) =>
      (WithLp.toLp 2 (H t q.1 q.2) : EuclideanSpace ℝ I))
      ((volume.restrict (Set.Icc l u)).prod (tsMeasure P b)) := by
  have h1 := hm.comp_measurePreserving
    (measurePreserving_prodAssoc (volume.restrict (Set.Icc l u)) (volume.restrict (Set.Icc 0 b)) P).symm
  exact (PiLp.continuous_toLp 2 (fun _ : I => ℝ)).comp_aestronglyMeasurable h1

/-- the section class of `embL2` is the unclamped Euclidean-valued integrand, `tsMeasure`-a.e. -/
theorem r26t8a_s02_coe_ae {Omega I : Type*} [mOmega : MeasurableSpace Omega] [Fintype I]
    (P : Measure Omega) [IsProbabilityMeasure P] (F : Filtration ℝ mOmega) (b l u : ℝ)
    (H : ℝ → ℝ → Omega → I → ℝ) (hH : ∀ t ∈ Set.Icc l u, IsProgressiveL2 P F (H t))
    (t : ℝ) (ht : t ∈ Set.Icc l u) :
    ⇑(embL2 (hH t ht) b) =ᵐ[tsMeasure P b]
      fun q : ℝ × Omega => (WithLp.toLp 2 (H t q.1 q.2) : EuclideanSpace ℝ I) := by
  have hclamp : ∀ᵐ q ∂(tsMeasure P b), q.1 ∈ Set.Icc 0 b := by
    have h0 : ∀ᵐ s ∂(volume.restrict (Set.Icc 0 b)), s ∈ Set.Icc (0 : ℝ) b :=
      ae_restrict_mem measurableSet_Icc
    exact (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Set.Icc 0 b)) (ν := P)).ae h0
  have hcoe : ⇑(embL2 (hH t ht) b) =ᵐ[tsMeasure P b] eclamp (H t) b :=
    (memLp_eclamp (hH t ht) b).coeFn_toLp
  filter_upwards [hcoe, hclamp] with q h1 h2
  rw [h1]
  simp [eclamp, min_eq_left h2.2]

theorem r26t8a_integrand_sections {Omega I : Type*} [mOmega : MeasurableSpace Omega] [Fintype I]
    (P : Measure Omega) [IsProbabilityMeasure P] (F : Filtration ℝ mOmega) (b l u : ℝ) (hb : 0≤b) (hlu : l≤u)
    (H : ℝ → ℝ → Omega → I → ℝ)
    (hH : ∀ t∈Set.Icc l u, IsProgressiveL2 P F (H t))
    (hm : AEStronglyMeasurable (fun p : (ℝ×ℝ)×Omega => H p.1.1 p.1.2 p.2)
      (((volume.restrict (Set.Icc l u)).prod (volume.restrict (Set.Icc 0 b))).prod P))
    (he : (∫⁻ t in Set.Icc l u, HRS.sqIntegralOn P (H t) b)<⊤) :
    ∃ V : ℝ → r26t8a_progSpan (I:=I) P F b,
      AEStronglyMeasurable V (volume.restrict (Set.Icc l u)) ∧
      (∀ t (ht : t∈Set.Icc l u), (V t : Lp (EuclideanSpace ℝ I) 2 (HRS.tsMeasure P b))=
        HRS.embL2 (hH t ht) b) ∧
      (∫⁻ t in Set.Icc l u, ‖V t‖ₑ^2)=∫⁻ t in Set.Icc l u, HRS.sqIntegralOn P (H t) b := by
  classical
  haveI : IsFiniteMeasure (tsMeasure P b) := by unfold tsMeasure; infer_instance
  let μ : Measure ℝ := volume.restrict (Set.Icc l u)
  let F' : ℝ → ℝ × Omega → EuclideanSpace ℝ I := fun t q => WithLp.toLp 2 (H t q.1 q.2)
  have hF : AEStronglyMeasurable (Function.uncurry F') (μ.prod (tsMeasure P b)) :=
    r26t8a_s02_joint P b l u H hm
  let V0 : ℝ → Lp (EuclideanSpace ℝ I) 2 (tsMeasure P b) := fun t =>
    if ht : t ∈ Set.Icc l u then embL2 (hH t ht) b else 0
  have hV0 : ∀ᵐ t ∂μ, ⇑(V0 t) =ᵐ[tsMeasure P b] F' t := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    have e : V0 t = embL2 (hH t ht) b := dif_pos ht
    rw [e]
    exact r26t8a_s02_coe_ae P F b l u H hH t ht
  have hAE : AEStronglyMeasurable V0 μ := r26t8a_s02a_sections μ (tsMeasure P b) F' hF V0 hV0
  let V : ℝ → r26t8a_progSpan (I := I) P F b := fun t =>
    if ht : t ∈ Set.Icc l u then r26t8a_progEmbed P F b (H t) (hH t ht) else 0
  have hVc : ∀ t, ((V t : r26t8a_progSpan (I := I) P F b) :
      Lp (EuclideanSpace ℝ I) 2 (tsMeasure P b)) = V0 t := by
    intro t
    by_cases ht : t ∈ Set.Icc l u
    · have e1 : V t = r26t8a_progEmbed P F b (H t) (hH t ht) := dif_pos ht
      have e2 : V0 t = embL2 (hH t ht) b := dif_pos ht
      rw [e1, e2]; rfl
    · have e1 : V t = 0 := dif_neg ht
      have e2 : V0 t = 0 := dif_neg ht
      rw [e1, e2]; rfl
  refine ⟨V, ?_, ?_, ?_⟩
  · have hemb := Topology.IsEmbedding.subtypeVal
      (p := fun x => x ∈ r26t8a_progSpan (I := I) P F b)
    rw [← hemb.aestronglyMeasurable_comp_iff]
    have : (fun t => Subtype.val (V t)) = V0 := funext hVc
    rw [this]
    exact hAE
  · intro t ht
    rw [hVc]
    exact dif_pos ht
  · refine setLIntegral_congr_fun measurableSet_Icc (fun t ht => ?_)
    have hn : ‖V t‖ = ‖embL2 (hH t ht) b‖ := by
      have e2 : V0 t = embL2 (hH t ht) b := dif_pos ht
      calc ‖V t‖ = ‖(V t : Lp (EuclideanSpace ℝ I) 2 (tsMeasure P b))‖ := (Submodule.coe_norm _)
        _ = ‖V0 t‖ := by rw [hVc]
        _ = ‖embL2 (hH t ht) b‖ := by rw [e2]
    have hfin : sqIntegralOn P (H t) b ≠ ⊤ := ((hH t ht).sq b).ne
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), hn, norm_embL2_sq,
      ENNReal.ofReal_toReal hfin]

end HRS.MS.R26T8A

end
