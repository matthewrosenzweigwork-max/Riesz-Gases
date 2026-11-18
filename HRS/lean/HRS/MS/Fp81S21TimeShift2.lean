import HRS.MS.Fp81S21TimeShift
import HRS.MS.Fp81S21LeadingAdapter2
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace HRS.Fp81.S21

private def fp81s21_zeroExtendL1Linear {α : Type*} [MeasurableSpace α]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure α) (s : Set α) (hs : MeasurableSet s) :
    Lp E 1 (μ.restrict s) →ₗ[ℝ] Lp E 1 μ := {
    toFun := fun f =>
      ((memLp_indicator_iff_restrict hs).2 (Lp.memLp f)).toLp (s.indicator f)
    map_add' := fun f g => by
      let hf : MemLp (s.indicator f) 1 μ :=
        (memLp_indicator_iff_restrict hs).2 (Lp.memLp f)
      let hg : MemLp (s.indicator g) 1 μ :=
        (memLp_indicator_iff_restrict hs).2 (Lp.memLp g)
      have hfg : s.indicator (f + g) =ᵐ[μ] s.indicator f + s.indicator g := by
        have hsrc := ae_imp_of_ae_restrict (Lp.coeFn_add f g)
        filter_upwards [hsrc] with x hx
        by_cases hxs : x ∈ s
        · simpa [Set.indicator, hxs] using hx hxs
        · simp [Set.indicator, hxs]
      change ((memLp_indicator_iff_restrict hs).2 (Lp.memLp (f + g))).toLp
          (s.indicator (f + g)) = hf.toLp (s.indicator f) + hg.toLp (s.indicator g)
      calc
        _ = (hf.add hg).toLp (s.indicator f + s.indicator g) := by
          exact MemLp.toLp_congr _ _ hfg
        _ = _ := MemLp.toLp_add hf hg
    map_smul' := fun c f => by
      let hf : MemLp (s.indicator f) 1 μ :=
        (memLp_indicator_iff_restrict hs).2 (Lp.memLp f)
      have hcf : s.indicator (c • f) =ᵐ[μ] c • s.indicator f := by
        have hsrc := ae_imp_of_ae_restrict (Lp.coeFn_smul c f)
        filter_upwards [hsrc] with x hx
        by_cases hxs : x ∈ s
        · simp [Set.indicator, hxs, hx hxs]
        · simp [Set.indicator, hxs]
      change ((memLp_indicator_iff_restrict hs).2 (Lp.memLp (c • f))).toLp
          (s.indicator (c • f)) = c • hf.toLp (s.indicator f)
      calc
        _ = (hf.const_smul c).toLp (c • s.indicator f) := by
          exact MemLp.toLp_congr _ _ hcf
        _ = _ := MemLp.toLp_const_smul c hf
  }

@[simp]
private theorem fp81s21_zeroExtendL1Linear_apply {α : Type*} [MeasurableSpace α]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure α) (s : Set α) (hs : MeasurableSet s)
    (f : Lp E 1 (μ.restrict s)) :
    fp81s21_zeroExtendL1Linear E μ s hs f =
      ((memLp_indicator_iff_restrict hs).2 (Lp.memLp f)).toLp (s.indicator f) := rfl

/-- Extend an `L¹` function on a measurable subset by zero to the ambient space. -/
noncomputable def fp81s21_zeroExtendL1 {α : Type*} [MeasurableSpace α]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure α) (s : Set α) (hs : MeasurableSet s) :
    Lp E 1 (μ.restrict s) →L[ℝ] Lp E 1 μ :=
  (fp81s21_zeroExtendL1Linear E μ s hs).mkContinuous 1 (by
    intro f
    change ‖fp81s21_zeroExtendL1Linear E μ s hs f‖ ≤ 1 * ‖f‖
    rw [fp81s21_zeroExtendL1Linear_apply, Lp.norm_toLp,
      eLpNorm_indicator_eq_eLpNorm_restrict hs]
    simp [Lp.norm_def])

/-- The zero extension has the same `L¹` norm as the original function. -/
theorem fp81s21_zeroExtendL1_norm {α : Type*} [MeasurableSpace α]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure α) (s : Set α) (hs : MeasurableSet s)
    (f : Lp E 1 (μ.restrict s)) :
    ‖fp81s21_zeroExtendL1 E μ s hs f‖ = ‖f‖ := by
  change ‖fp81s21_zeroExtendL1Linear E μ s hs f‖ = ‖f‖
  rw [fp81s21_zeroExtendL1Linear_apply, Lp.norm_toLp,
    eLpNorm_indicator_eq_eLpNorm_restrict hs]
  simp [Lp.norm_def]

/-- The zero extension agrees with the indicator representative almost everywhere. -/
theorem fp81s21_zeroExtendL1_ae {α : Type*} [MeasurableSpace α]
    (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure α) (s : Set α) (hs : MeasurableSet s)
    (f : Lp E 1 (μ.restrict s)) :
    fp81s21_zeroExtendL1 E μ s hs f =ᵐ[μ] s.indicator f := by
  change fp81s21_zeroExtendL1Linear E μ s hs f =ᵐ[μ] s.indicator f
  rw [fp81s21_zeroExtendL1Linear_apply]
  let hf : MemLp (s.indicator f) 1 μ :=
    (memLp_indicator_iff_restrict hs).2 (Lp.memLp f)
  exact hf.coeFn_toLp

/-- Translation on `L¹(volume)` is the canonical composition by `t ↦ t-b`. -/
noncomputable def fp81s21_translateL1 {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (b : ℝ) :
    Lp E 1 (volume : Measure ℝ) →L[ℝ] Lp E 1 (volume : Measure ℝ) := by
  letI : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩
  have hm : MeasurePreserving (fun t : ℝ => t - b) volume volume := by
    simpa [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure ℝ) (-b)
  exact (Lp.compMeasurePreservingₗᵢ (𝕜 := ℝ) (E := E) (p := 1)
    (μ := volume) (μb := volume) (fun t : ℝ => t - b) hm).toContinuousLinearMap

/-- Almost-everywhere representative equation for Lebesgue translation. -/
theorem fp81s21_translateL1_ae {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (b : ℝ) (f : Lp E 1 (volume : Measure ℝ)) :
    fp81s21_translateL1 b f =ᵐ[volume] fun t => f (t - b) := by
  letI : Fact ((1 : ℝ≥0∞) ≤ 1) := ⟨le_rfl⟩
  have hm : MeasurePreserving (fun t : ℝ => t - b) volume volume := by
    simpa [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure ℝ) (-b)
  change Lp.compMeasurePreserving (E := E) (p := 1) (fun t : ℝ => t - b) hm f =ᵐ[volume]
      fun t => f (t - b)
  exact Lp.coeFn_compMeasurePreserving f hm

/-- Translate the length-`L+T` coefficient history by `b` and keep its part
through absolute time `a+T`. -/
noncomputable def fp81s21_recentShift
    (p : HRS.MS.R26T3.Parameters) (a : ℝ) (ha : 0 ≤ a)
    (L : ℝ) (hL : 0 < L) :
    HRS.MS.R26T6.r26t6_TimeCoeff (L + p.T) →L[ℝ]
      HRS.MS.R26T6.r26t6_TimeCoeff (a + p.T) := by
  let b : ℝ := max (a - L) 0
  have _hgeometry := HRS.Fp81.S21.fp81s21_recentWindowRestriction ha hL p.hT
  exact (LpToLpRestrictCLM ℝ HRS.MS.R26T6.r26t6_Coeff ℝ volume 1
      (Icc (0 : ℝ) (a + p.T))).comp
    ((fp81s21_translateL1 (E := HRS.MS.R26T6.r26t6_Coeff) b).comp
      (fp81s21_zeroExtendL1 HRS.MS.R26T6.r26t6_Coeff volume
        (Icc (0 : ℝ) (L + p.T)) measurableSet_Icc))

/-- Restriction to a closed interval is nonexpansive in `L¹`. -/
private theorem fp81s21_restrictL1_norm_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (A : ℝ) (f : Lp E 1 volume) :
    ‖LpToLpRestrictCLM ℝ E ℝ volume 1 (Icc (0 : ℝ) A) f‖ ≤ ‖f‖ := by
  have heq : LpToLpRestrictCLM ℝ E ℝ volume 1 (Icc (0 : ℝ) A) f =
      ((Lp.memLp f).restrict (Icc (0 : ℝ) A)).toLp f := by
    apply Lp.ext
    exact (LpToLpRestrictCLM_coeFn ℝ (Icc (0 : ℝ) A) f).trans
      (MemLp.coeFn_toLp ((Lp.memLp f).restrict (Icc (0 : ℝ) A))).symm
  rw [heq]
  exact norm_Lp_toLp_restrict_le (Icc (0 : ℝ) A) f

/-- The recent-history translation and truncation have operator norm at most one. -/
theorem fp81s21_recentShift_bound
    (p : HRS.MS.R26T3.Parameters) (a : ℝ) (ha : 0 ≤ a)
    (L : ℝ) (hL : 0 < L) :
    ‖fp81s21_recentShift p a ha L hL‖ ≤ 1 := by
  let b : ℝ := max (a - L) 0
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) ?_
  intro f
  calc
    ‖fp81s21_recentShift p a ha L hL f‖ ≤
        ‖fp81s21_translateL1 b
          (fp81s21_zeroExtendL1 HRS.MS.R26T6.r26t6_Coeff volume
            (Icc (0 : ℝ) (L + p.T)) measurableSet_Icc f)‖ := by
      exact fp81s21_restrictL1_norm_le (a + p.T) _
    _ = ‖fp81s21_zeroExtendL1 HRS.MS.R26T6.r26t6_Coeff volume
          (Icc (0 : ℝ) (L + p.T)) measurableSet_Icc f‖ := by
      simp [fp81s21_translateL1]
    _ = ‖f‖ := by
      exact fp81s21_zeroExtendL1_norm HRS.MS.R26T6.r26t6_Coeff volume
        (Icc (0 : ℝ) (L + p.T)) measurableSet_Icc f
    _ ≤ 1 * ‖f‖ := by simp

/-- Almost-everywhere absolute-time representative, with closed support; the
left endpoint is null and hence equivalent to `(b,a+T]`. -/
theorem fp81s21_recentShift_repr_Icc
    (p : HRS.MS.R26T3.Parameters) (a : ℝ) (ha : 0 ≤ a)
    (L : ℝ) (hL : 0 < L)
    (f : HRS.MS.R26T6.r26t6_TimeCoeff (L + p.T)) :
    fp81s21_recentShift p a ha L hL f =ᵐ[volume.restrict (Icc (0 : ℝ) (a + p.T))]
      (Icc (max (a - L) 0) (a + p.T)).indicator (fun t => f (t - max (a - L) 0)) := by
  let b : ℝ := max (a - L) 0
  let H : ℝ := L + p.T
  let A : ℝ := a + p.T
  let S : Set ℝ := Icc (0 : ℝ) H
  let mp : MeasurePreserving (fun t : ℝ => t - b) volume volume :=
    by simpa [sub_eq_add_neg] using measurePreserving_add_right volume (-b)
  have hb : 0 ≤ b := le_max_right _ _
  have hgeom := HRS.Fp81.S21.fp81s21_recentWindowRestriction ha hL p.hT
  have hshift0 : 0 ≤ a - b := hgeom.1
  have hu : p.T ∈ Icc (0 : ℝ) p.T := ⟨p.hT.le, le_rfl⟩
  have hinterval := hgeom.2 p.T hu
  have hH : 0 ≤ H := by linarith [p.hT, hL]
  have hA : 0 ≤ A := by linarith [ha, p.hT]
  have hba : b ≤ A := by linarith [hshift0, p.hT]
  have hAH : A ≤ b + H := by linarith [hinterval.1.2, hinterval.2]
  have hzero := fp81s21_zeroExtendL1_ae HRS.MS.R26T6.r26t6_Coeff volume
    S measurableSet_Icc f
  have hzeroShift :
      (fun t : ℝ =>
        fp81s21_zeroExtendL1 HRS.MS.R26T6.r26t6_Coeff volume S measurableSet_Icc f (t - b)) =ᵐ[volume]
      (fun t => S.indicator f (t - b)) := by
    exact mp.quasiMeasurePreserving.ae hzero
  have htrans := fp81s21_translateL1_ae b
    (fp81s21_zeroExtendL1 HRS.MS.R26T6.r26t6_Coeff volume S measurableSet_Icc f)
  have htransR :
      fp81s21_translateL1 b
        (fp81s21_zeroExtendL1 HRS.MS.R26T6.r26t6_Coeff volume S measurableSet_Icc f) =ᵐ[volume.restrict (Icc (0 : ℝ) A)]
        fun t => S.indicator f (t - b) := by
    exact htrans.trans hzeroShift |>.restrict
  have hrest := LpToLpRestrictCLM_coeFn ℝ (Icc (0 : ℝ) A)
    (fp81s21_translateL1 b
      (fp81s21_zeroExtendL1 HRS.MS.R26T6.r26t6_Coeff volume S measurableSet_Icc f))
  have hformula : ∀ t ∈ Icc (0 : ℝ) A,
      S.indicator f (t - b) = (Icc b A).indicator (fun z => f (z - b)) t := by
    intro t ht
    have hmem : t - b ∈ S ↔ t ∈ Icc b A := by
      constructor
      · intro hz
        change 0 ≤ t - b ∧ t - b ≤ H at hz
        change b ≤ t ∧ t ≤ A
        exact ⟨by linarith, ht.2⟩
      · intro hz
        change b ≤ t ∧ t ≤ A at hz
        change 0 ≤ t - b ∧ t - b ≤ H
        exact ⟨by linarith, by linarith [hAH]⟩
    simp [Set.indicator, hmem]
  change (LpToLpRestrictCLM ℝ HRS.MS.R26T6.r26t6_Coeff ℝ volume 1
      (Icc (0 : ℝ) A))
      (fp81s21_translateL1 b
        (fp81s21_zeroExtendL1 HRS.MS.R26T6.r26t6_Coeff volume S measurableSet_Icc f)) =ᵐ[
        volume.restrict (Icc (0 : ℝ) A)]
      (Icc b A).indicator (fun t => f (t - b))
  have hmem : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) A), t ∈ Icc (0 : ℝ) A :=
    ae_restrict_mem measurableSet_Icc
  filter_upwards [hrest, htransR, hmem] with t htOut htTrans htMem
  rw [htOut, htTrans]
  exact hformula t (by simpa [A] using htMem)

/-- The retained interval is `(b,a+T]` up to its null left endpoint. -/
theorem fp81s21_recentShift_repr_Ioc
    (p : HRS.MS.R26T3.Parameters) (a : ℝ) (ha : 0 ≤ a)
    (L : ℝ) (hL : 0 < L)
    (f : HRS.MS.R26T6.r26t6_TimeCoeff (L + p.T)) :
    fp81s21_recentShift p a ha L hL f =ᵐ[volume.restrict (Icc (0 : ℝ) (a + p.T))]
      (Ioc (max (a - L) 0) (a + p.T)).indicator
        (fun t => f (t - max (a - L) 0)) := by
  let b : ℝ := max (a - L) 0
  have hIcc := fp81s21_recentShift_repr_Icc p a ha L hL f
  have hsets : Ioc b (a + p.T) =ᵐ[volume] Icc b (a + p.T) :=
    Ioc_ae_eq_Icc
  have hind :
      (Ioc b (a + p.T)).indicator (fun t => f (t - b)) =ᵐ[volume]
        (Icc b (a + p.T)).indicator (fun t => f (t - b)) := by
    filter_upwards [hsets] with t ht
    by_cases hi : t ∈ Ioc b (a + p.T)
    · have hc : t ∈ Icc b (a + p.T) := (ht.mp hi)
      simp [hi, hc]
    · have hc : t ∉ Icc b (a + p.T) := fun hc => hi (ht.mpr hc)
      simp [hi, hc]
  have hindR := hind.restrict (s := Icc (0 : ℝ) (a + p.T))
  exact hIcc.trans hindR.symm

#print axioms fp81s21_zeroExtendL1_norm
#print axioms fp81s21_zeroExtendL1_ae
#print axioms fp81s21_translateL1_ae
#print axioms fp81s21_recentShift_bound
#print axioms fp81s21_recentShift_repr_Icc
#print axioms fp81s21_recentShift_repr_Ioc

end HRS.Fp81.S21
