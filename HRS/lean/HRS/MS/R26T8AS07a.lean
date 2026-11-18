import Mathlib

/-!
# S8.2 T8A.S07a: martingale plus parameter primitive from `a`, on the good event (generic)

`r26t8a_s07a_prim M Jd a T t w = M (a+t) w + ∫_{[a,a+t]} Jd v w dv` if `∫_{[a,a+T]} ‖Jd v w‖ dv < ∞`, and `0` otherwise.
For `M` with continuous adapted-measurable paths and `Jd` jointly measurable, it is jointly measurable and
continuous on `[0,T]` for every `w`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
namespace HRS.MS.R26T8A

open Classical in
/-- the martingale plus primitive on the good event, zero elsewhere -/
def r26t8a_s07a_prim {Ω : Type*} (M : ℝ → Ω → ℝ) (Jd : ℝ → Ω → ℝ) (a T : ℝ) : ℝ → Ω → ℝ :=
  fun t w => if (∫⁻ v in Icc a (a + T), ‖Jd v w‖ₑ) < ∞ then
    M (a + t) w + ∫ v in Icc a (a + t), Jd v w else 0

theorem r26t8a_s07a_meas {Ω : Type*} [MeasurableSpace Ω] (M : ℝ → Ω → ℝ)
    (hMc : ∀ w, Continuous fun t => M t w) (hMm : ∀ t, Measurable (M t))
    (Jd : ℝ → Ω → ℝ) (hJd : Measurable (Function.uncurry Jd)) (a T : ℝ) :
    Measurable (Function.uncurry (r26t8a_s07a_prim M Jd a T)) := by
  classical
  have hgood : MeasurableSet {w : Ω | (∫⁻ v in Icc a (a + T), ‖Jd v w‖ₑ) < ∞} := by
    have : Measurable fun w => ∫⁻ v in Icc a (a + T), ‖Jd v w‖ₑ :=
      Measurable.lintegral_prod_left' (f := fun p : ℝ × Ω => ‖Jd p.1 p.2‖ₑ) hJd.enorm
    exact measurableSet_lt this measurable_const
  have hI : Measurable fun p : ℝ × Ω => ∫ v in Icc a (a + p.1), Jd v p.2 := by
    have hset : MeasurableSet {q : (ℝ × Ω) × ℝ | q.2 ∈ Icc a (a + q.1.1)} := by
      have h1 : MeasurableSet {q : (ℝ × Ω) × ℝ | a ≤ q.2} :=
        measurableSet_le measurable_const measurable_snd
      have h2 : MeasurableSet {q : (ℝ × Ω) × ℝ | q.2 ≤ a + q.1.1} :=
        measurableSet_le measurable_snd (measurable_const.add (measurable_fst.comp measurable_fst))
      exact h1.inter h2
    have hf : Measurable fun q : (ℝ × Ω) × ℝ =>
        if q.2 ∈ Icc a (a + q.1.1) then Jd q.2 q.1.2 else 0 :=
      Measurable.ite hset
        (hJd.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst))) measurable_const
    have h3 := (hf.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))).measurable
    have e : (fun p : ℝ × Ω => ∫ v in Icc a (a + p.1), Jd v p.2) =
        fun p : ℝ × Ω => ∫ y, (if y ∈ Icc a (a + p.1) then Jd y p.2 else 0) := by
      funext p
      rw [← integral_indicator measurableSet_Icc]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp [Set.indicator_apply]
    rw [e]
    exact h3
  have hM : Measurable fun p : ℝ × Ω => M (a + p.1) p.2 :=
    measurable_uncurry_of_continuous_of_measurable (u := fun t w => M (a + t) w)
      (fun w => (hMc w).comp (continuous_const.add continuous_id)) (fun t => hMm (a + t))
  show Measurable fun p : ℝ × Ω => r26t8a_s07a_prim M Jd a T p.1 p.2
  unfold r26t8a_s07a_prim
  exact Measurable.ite (measurable_snd hgood) (hM.add hI) measurable_const

theorem r26t8a_s07a_cont {Ω : Type*} [MeasurableSpace Ω] (M : ℝ → Ω → ℝ)
    (hMc : ∀ w, Continuous fun t => M t w)
    (Jd : ℝ → Ω → ℝ) (hJd : Measurable (Function.uncurry Jd)) (a T : ℝ) (w : Ω) :
    ContinuousOn (fun t => r26t8a_s07a_prim M Jd a T t w) (Icc 0 T) := by
  classical
  by_cases hg : (∫⁻ v in Icc a (a + T), ‖Jd v w‖ₑ) < ∞
  · have hint : IntegrableOn (fun v => Jd v w) (Icc a (a + T)) :=
      ⟨(hJd.comp measurable_prodMk_right).aestronglyMeasurable, hg⟩
    have hc : ContinuousOn (fun t => ∫ v in a..(a + t), Jd v w) (Icc 0 T) := by
      rcases le_or_gt 0 T with hT | hT
      · have h1 := intervalIntegral.continuousOn_primitive_interval (a := a) (b := a + T)
          (μ := (volume : Measure ℝ)) (f := fun v => Jd v w)
          (by rwa [uIcc_of_le (by linarith)])
        rw [uIcc_of_le (by linarith)] at h1
        refine h1.comp (continuous_const.add continuous_id).continuousOn fun t ht => ?_
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
      · simp [Icc_eq_empty_of_lt hT]
    have h2 : ContinuousOn (fun t => M (a + t) w + ∫ v in a..(a + t), Jd v w) (Icc 0 T) :=
      ((hMc w).comp (continuous_const.add continuous_id)).continuousOn.add hc
    refine h2.congr fun t ht => ?_
    simp only [r26t8a_s07a_prim, if_pos hg]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith [ht.1])]
  · have : (fun t => r26t8a_s07a_prim M Jd a T t w) = fun _ => 0 := by
      funext t
      simp [r26t8a_s07a_prim, hg]
    rw [this]
    exact continuousOn_const

theorem r26t8a_s07a_ftc {Ω : Type*} (M : ℝ → Ω → ℝ) (Jd : ℝ → Ω → ℝ) (a T : ℝ) (w : Ω)
    (hg : (∫⁻ v in Icc a (a + T), ‖Jd v w‖ₑ) < ∞) (t : ℝ) :
    r26t8a_s07a_prim M Jd a T t w = M (a + t) w + ∫ v in Icc a (a + t), Jd v w := by
  classical
  simp [r26t8a_s07a_prim, hg]

end HRS.MS.R26T8A

end
