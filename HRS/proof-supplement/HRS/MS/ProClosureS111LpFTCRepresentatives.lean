import HRS.MS.ProClosureS111JointLp
import HRS.MS.ProClosureS111LpIntegral

/-!
Actual scalar representatives of an L³ fundamental theorem of calculus.
The derivative is represented correctly at every time. The path is defined
as the scalar primitive, giving a common full-measure set for its entire
time interval, without imposing a common null set on arbitrary L³ choices.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace HRS.MS.ProClosureS111

variable {X : Type*} [MeasurableSpace X]
local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

theorem L3_FTC_representatives (mu : Measure X) [IsProbabilityMeasure mu]
    (T : ℝ) (hT : 0 ≤ T) (F G : ℝ → Lp ℝ 3 mu)
    (hGm : StronglyMeasurable (fun t : Icc (0 : ℝ) T => G t))
    (hGi : IntegrableOn G (Icc (0 : ℝ) T))
    (hFTC : ∀ t ∈ Icc (0 : ℝ) T, F t = F 0 + ∫ v in Icc (0 : ℝ) t, G v) :
    ∃ f g : ℝ → X → ℝ,
      StronglyMeasurable (fun z : ℝ × X => g z.1 z.2) ∧
      (∀ t ∈ Icc (0 : ℝ) T,
        MemLp (f t) 3 mu ∧ f t =ᵐ[mu] (F t : X → ℝ) ∧
        MemLp (g t) 3 mu ∧ g t =ᵐ[mu] (G t : X → ℝ)) ∧
      ∀ᵐ x ∂mu, IntegrableOn (fun v => g v x) (Icc (0 : ℝ) T) ∧
        ∀ t ∈ Icc (0 : ℝ) T, f t x = f 0 x + ∫ v in Icc (0 : ℝ) t, g v x := by
  obtain ⟨g0, hg0, hg0rep⟩ := joint_Lp_representative mu 3 (by norm_num)
    (fun t : Icc (0 : ℝ) T => G t) hGm
  let clip : ℝ → Icc (0 : ℝ) T := fun t =>
    ⟨max 0 (min t T), le_max_left _ _, max_le hT (min_le_right _ _)⟩
  have hclip : Measurable clip :=
    (measurable_const.max (measurable_id.min measurable_const)).subtype_mk
  have hclip_eq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : clip t = ⟨t, ht⟩ := by
    apply Subtype.ext
    exact (max_eq_right (le_min ht.1 hT)).trans (min_eq_left ht.2)
  let g : ℝ → X → ℝ := fun t x => g0 (clip t, x)
  have hgm : StronglyMeasurable (fun z : ℝ × X => g z.1 z.2) :=
    hg0.comp_measurable ((hclip.comp measurable_fst).prodMk measurable_snd)
  have hg : ∀ t ∈ Icc (0 : ℝ) T,
      MemLp (g t) 3 mu ∧ g t =ᵐ[mu] (G t : X → ℝ) := by
    intro t ht
    simpa only [g, hclip_eq t ht] using hg0rep ⟨t, ht⟩
  have hGi_sub (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      IntegrableOn G (Icc (0 : ℝ) t) :=
    hGi.mono_set (fun v hv => ⟨hv.1, hv.2.trans ht.2⟩)
  have hint (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      Integrable (fun z : ℝ × X => g z.1 z.2)
        ((volume.restrict (Icc (0 : ℝ) t)).prod mu) ∧
      (fun x => ∫ v in Icc (0 : ℝ) t, g v x) =ᵐ[mu]
        ((∫ v in Icc (0 : ℝ) t, G v : Lp ℝ 3 mu) : X → ℝ) := by
    apply L3_integral_representative mu (volume.restrict (Icc (0 : ℝ) t))
      G (hGi_sub t ht) (fun z : ℝ × X => g z.1 z.2) hgm.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
    exact (hg v ⟨hv.1, hv.2.trans ht.2⟩).2
  let f : ℝ → X → ℝ := fun t x => (F 0 : X → ℝ) x + ∫ v in Icc (0 : ℝ) t, g v x
  have hf : ∀ t ∈ Icc (0 : ℝ) T, f t =ᵐ[mu] (F t : X → ℝ) := by
    intro t ht
    filter_upwards [(hint t ht).2,
      Lp.coeFn_add (F 0) (∫ v in Icc (0 : ℝ) t, G v)] with x hx hsum
    change (F 0 : X → ℝ) x + (∫ v in Icc (0 : ℝ) t, g v x) = (F t : X → ℝ) x
    rw [hFTC t ht]
    exact (congrArg (fun z => (F 0 : X → ℝ) x + z) hx).trans hsum.symm
  refine ⟨f, g, hgm, fun t ht =>
    ⟨(memLp_congr_ae (hf t ht)).2 (Lp.memLp (F t)), hf t ht, (hg t ht).1, (hg t ht).2⟩, ?_⟩
  filter_upwards [(hint T ⟨hT, le_rfl⟩).1.prod_left_ae] with x hx
  refine ⟨hx, fun t ht => ?_⟩
  have hfzero : f 0 x = (F 0 : X → ℝ) x := by simp [f]
  rw [hfzero]

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.L3_FTC_representatives
