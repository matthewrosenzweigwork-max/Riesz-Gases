import Mathlib

/-!
# S8.2 T8A.S05a: the primitive of a jointly measurable integrable family, defined on the good event (generic)

`r26t8a_s05a_prim G0 Gd T t w = G0 w + ∫_{[0,t]} Gd v w dv` if `∫_{[0,T]} ‖Gd v w‖ dv < ∞` and `0` otherwise.  It is
jointly measurable and, for every `w`, continuous on `[0,T]`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace HRS.MS.R26T8A

open Classical in
/-- the primitive on the good event, zero elsewhere -/
def r26t8a_s05a_prim {Ω : Type*} (G0 : Ω → ℝ) (Gd : ℝ → Ω → ℝ) (T : ℝ) : ℝ → Ω → ℝ :=
  fun t w => if (∫⁻ v in Icc 0 T, ‖Gd v w‖ₑ) < ∞ then G0 w + ∫ v in Icc 0 t, Gd v w else 0

theorem r26t8a_s05a_meas {Ω : Type*} [MeasurableSpace Ω] (G0 : Ω → ℝ) (hG0 : Measurable G0)
    (Gd : ℝ → Ω → ℝ) (hGd : Measurable (Function.uncurry Gd)) (T : ℝ) :
    Measurable (Function.uncurry (r26t8a_s05a_prim G0 Gd T)) := by
  classical
  have hgood : MeasurableSet {w : Ω | (∫⁻ v in Icc 0 T, ‖Gd v w‖ₑ) < ∞} := by
    have : Measurable fun w => ∫⁻ v in Icc 0 T, ‖Gd v w‖ₑ :=
      Measurable.lintegral_prod_left' (f := fun p : ℝ × Ω => ‖Gd p.1 p.2‖ₑ) hGd.enorm
    exact measurableSet_lt this measurable_const
  have hI : Measurable fun p : ℝ × Ω => ∫ v in Icc 0 p.1, Gd v p.2 := by
    have hset : MeasurableSet {q : (ℝ × Ω) × ℝ | q.2 ∈ Icc 0 q.1.1} := by
      have h1 : MeasurableSet {q : (ℝ × Ω) × ℝ | 0 ≤ q.2} :=
        measurableSet_le measurable_const measurable_snd
      have h2 : MeasurableSet {q : (ℝ × Ω) × ℝ | q.2 ≤ q.1.1} :=
        measurableSet_le measurable_snd (measurable_fst.comp measurable_fst)
      exact h1.inter h2
    have hf : Measurable fun q : (ℝ × Ω) × ℝ => if q.2 ∈ Icc 0 q.1.1 then Gd q.2 q.1.2 else 0 :=
      Measurable.ite hset
        (hGd.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))) measurable_const
    have h3 := (hf.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))).measurable
    have e : (fun p : ℝ × Ω => ∫ v in Icc 0 p.1, Gd v p.2) =
        fun p : ℝ × Ω => ∫ y, (if y ∈ Icc 0 p.1 then Gd y p.2 else 0) := by
      funext p
      rw [← integral_indicator measurableSet_Icc]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp [Set.indicator_apply]
    rw [e]
    exact h3
  show Measurable fun p : ℝ × Ω => r26t8a_s05a_prim G0 Gd T p.1 p.2
  unfold r26t8a_s05a_prim
  exact Measurable.ite (measurable_snd hgood) ((hG0.comp measurable_snd).add hI) measurable_const

theorem r26t8a_s05a_cont {Ω : Type*} [MeasurableSpace Ω] (G0 : Ω → ℝ) (Gd : ℝ → Ω → ℝ)
    (hGd : Measurable (Function.uncurry Gd)) (T : ℝ) (w : Ω) :
    ContinuousOn (fun t => r26t8a_s05a_prim G0 Gd T t w) (Icc 0 T) := by
  classical
  by_cases hg : (∫⁻ v in Icc 0 T, ‖Gd v w‖ₑ) < ∞
  · have hint : IntegrableOn (fun v => Gd v w) (Icc 0 T) :=
      ⟨(hGd.comp measurable_prodMk_right).aestronglyMeasurable, hg⟩
    have hc : ContinuousOn (fun t => ∫ v in (0 : ℝ)..t, Gd v w) (Icc 0 T) := by
      rcases le_or_gt 0 T with hT | hT
      · have := intervalIntegral.continuousOn_primitive_interval (a := 0) (b := T)
          (μ := (volume : Measure ℝ)) (f := fun v => Gd v w) (by rwa [uIcc_of_le hT])
        simpa [uIcc_of_le hT] using this
      · simp [Icc_eq_empty_of_lt hT]
    have h2 : ContinuousOn (fun t => G0 w + ∫ v in (0 : ℝ)..t, Gd v w) (Icc 0 T) :=
      continuousOn_const.add hc
    refine h2.congr fun t ht => ?_
    simp only [r26t8a_s05a_prim, if_pos hg]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht.1]
  · have : (fun t => r26t8a_s05a_prim G0 Gd T t w) = fun _ => 0 := by
      funext t
      simp [r26t8a_s05a_prim, hg]
    rw [this]
    exact continuousOn_const

theorem r26t8a_s05a_zero {Ω : Type*} (G0 : Ω → ℝ) (Gd : ℝ → Ω → ℝ) (T : ℝ) (w : Ω)
    (hg : (∫⁻ v in Icc 0 T, ‖Gd v w‖ₑ) < ∞) :
    r26t8a_s05a_prim G0 Gd T 0 w = G0 w := by
  classical
  simp [r26t8a_s05a_prim, hg]

theorem r26t8a_s05a_ftc {Ω : Type*} (G0 : Ω → ℝ) (Gd : ℝ → Ω → ℝ) (T : ℝ) (w : Ω)
    (hg : (∫⁻ v in Icc 0 T, ‖Gd v w‖ₑ) < ∞) (t : ℝ) :
    r26t8a_s05a_prim G0 Gd T t w = G0 w + ∫ v in Icc 0 t, Gd v w := by
  classical
  simp [r26t8a_s05a_prim, hg]

end HRS.MS.R26T8A

end
