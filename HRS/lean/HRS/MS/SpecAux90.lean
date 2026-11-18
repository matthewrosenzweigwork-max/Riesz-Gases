import HRS.MS.SpecAux89
import HRS.MS.PsdAux1

/-!
# S8M: convolution with the Riesz kernel on bounded integrable functions (S8.7, R4)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_Good G`: `G` is measurable, integrable and bounded.  For such `G`
(and `0 < s < d`, `g = rieszKernel d s`): `y ↦ g(x-y) G(y)` is integrable for every `x`, `convFun g G` is
measurable and bounded, and the energy is nonnegative, `0 ≤ ∫ G · (g * G)` (`s8p_Good_energy_nonneg`, from `riesz_energy_nonneg`).
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HRS.MS.Spec

open HRS HRS.Whole

variable {d : ℕ}

/-- Measurable, integrable and bounded. -/
def s8p_Good (G : Euc d → ℝ) : Prop :=
  Measurable G ∧ Integrable G ∧ ∃ m : ℝ, ∀ x, |G x| ≤ m

theorem s8p_Good.add {G H : Euc d → ℝ} (hG : s8p_Good G) (hH : s8p_Good H) :
    s8p_Good (fun x => G x + H x) := by
  obtain ⟨m1, hm1⟩ := hG.2.2
  obtain ⟨m2, hm2⟩ := hH.2.2
  exact ⟨hG.1.add hH.1, hG.2.1.add hH.2.1, m1 + m2, fun x => (abs_add_le _ _).trans (add_le_add (hm1 x) (hm2 x))⟩

theorem s8p_Good.sub {G H : Euc d → ℝ} (hG : s8p_Good G) (hH : s8p_Good H) :
    s8p_Good (fun x => G x - H x) := by
  obtain ⟨m1, hm1⟩ := hG.2.2
  obtain ⟨m2, hm2⟩ := hH.2.2
  exact ⟨hG.1.sub hH.1, hG.2.1.sub hH.2.1, m1 + m2, fun x => (abs_sub _ _).trans (add_le_add (hm1 x) (hm2 x))⟩

theorem s8p_Good.const_mul {G : Euc d → ℝ} (hG : s8p_Good G) (c : ℝ) : s8p_Good (fun x => c * G x) := by
  obtain ⟨m1, hm1⟩ := hG.2.2
  refine ⟨hG.1.const_mul c, hG.2.1.const_mul c, |c| * m1, fun x => ?_⟩
  rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hm1 x) (abs_nonneg _)

/-- The real local kernel. -/
def s8p_kr (d : ℕ) (s : ℝ) : Euc d → ℝ := (ball (0 : Euc d) 1).indicator (rieszKernel d s)

theorem s8p_kr_int {s : ℝ} (hs0 : 0 < s) (hsd : s < d) : Integrable (s8p_kr d s) := by
  have h := (rieszKernel_locallyIntegrable (d := d) hs0.le hsd).integrableOn_isCompact
    (isCompact_closedBall (0 : Euc d) 1)
  exact (h.mono_set ball_subset_closedBall).integrable_indicator measurableSet_ball

theorem s8p_kr_nonneg {s : ℝ} (hs0 : 0 < s) (z : Euc d) : 0 ≤ s8p_kr d s z := by
  unfold s8p_kr
  exact Set.indicator_nonneg (fun z _ => s8p_riesz_nonneg hs0 z) z

theorem s8p_riesz_le_kr_add_one {s : ℝ} (hs0 : 0 < s) (z : Euc d) :
    rieszKernel d s z ≤ s8p_kr d s z + 1 := by
  by_cases hz : z ∈ ball (0 : Euc d) 1
  · unfold s8p_kr; rw [Set.indicator_of_mem hz]; linarith
  · have := s8p_riesz_le_one hs0 (z := z) (by simpa using hz)
    unfold s8p_kr; rw [Set.indicator_of_notMem hz]; linarith

theorem s8p_Good.conv_int {s : ℝ} (hs0 : 0 < s) (hsd : s < d) {G : Euc d → ℝ} (hG : s8p_Good G) (x : Euc d) :
    Integrable (fun y => rieszKernel d s (x - y) * G y) := by
  obtain ⟨m, hm⟩ := hG.2.2
  have hkx : Integrable (fun y => s8p_kr d s (x - y)) := (s8p_kr_int hs0 hsd).comp_sub_left x
  have hdom : Integrable (fun y => m * s8p_kr d s (x - y) + |G y|) := (hkx.const_mul m).add hG.2.1.abs
  refine hdom.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
  · exact ((s8p_riesz_meas s).comp (measurable_const.sub measurable_id)).mul hG.1 |>.aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (s8p_riesz_nonneg hs0 _)]
    have h1 := s8p_riesz_le_kr_add_one hs0 (x - y)
    have h2 := hm y
    have h3 := s8p_kr_nonneg hs0 (d := d) (x - y)
    have h4 : 0 ≤ |G y| := abs_nonneg _
    nlinarith [mul_le_mul h1 h2 h4 (by linarith [s8p_riesz_nonneg hs0 (d := d) (x - y)])]

theorem s8p_convFun_meas {s : ℝ} {G : Euc d → ℝ} (hG : Measurable G) :
    Measurable (HRS.Whole.convFun (rieszKernel d s) G) := by
  have hm : Measurable (fun p : Euc d × Euc d => rieszKernel d s (p.1 - p.2) * G p.2) :=
    ((s8p_riesz_meas s).comp (measurable_fst.sub measurable_snd)).mul (hG.comp measurable_snd)
  have hsm : MeasureTheory.StronglyMeasurable
      (fun p : Euc d × Euc d => rieszKernel d s (p.1 - p.2) * G p.2) := hm.stronglyMeasurable
  have h2 : MeasureTheory.StronglyMeasurable
      (fun x : Euc d => ∫ y : Euc d, rieszKernel d s (x - y) * G y) :=
    hsm.integral_prod_right' (ν := (volume : Measure (Euc d)))
  exact h2.measurable

theorem s8p_Good.conv_bound {s : ℝ} (hs0 : 0 < s) (hsd : s < d) {G : Euc d → ℝ} (hG : s8p_Good G) :
    ∃ b : ℝ, ∀ x, |HRS.Whole.convFun (rieszKernel d s) G x| ≤ b := by
  obtain ⟨m, hm⟩ := hG.2.2
  refine ⟨|m| * (∫ z, s8p_kr d s z) + ∫ y, |G y|, fun x => ?_⟩
  have hkx : Integrable (fun y => s8p_kr d s (x - y)) := (s8p_kr_int hs0 hsd).comp_sub_left x
  have hdom : Integrable (fun y => |m| * s8p_kr d s (x - y) + |G y|) := (hkx.const_mul _).add hG.2.1.abs
  unfold HRS.Whole.convFun
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le (f := fun y => rieszKernel d s (x - y) * G y) hdom
    (Filter.Eventually.of_forall fun y => ?_)).trans ?_
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (s8p_riesz_nonneg hs0 _)]
    have h1 := s8p_riesz_le_kr_add_one hs0 (x - y)
    have h2 : |G y| ≤ |m| := (hm y).trans (le_abs_self m)
    have h4 : 0 ≤ |G y| := abs_nonneg _
    nlinarith [mul_le_mul h1 h2 h4 (by linarith [s8p_riesz_nonneg hs0 (d := d) (x - y)]),
      s8p_kr_nonneg hs0 (d := d) (x - y)]
  · refine le_of_eq ?_
    rw [integral_add (hkx.const_mul _) hG.2.1.abs, integral_const_mul]
    have : ∫ y, s8p_kr d s (x - y) = ∫ z, s8p_kr d s z := integral_sub_left_eq_self (s8p_kr d s) volume x
    rw [this]

theorem s8p_Good.abs {G : Euc d → ℝ} (hG : s8p_Good G) : s8p_Good (fun x => |G x|) := by
  obtain ⟨m1, hm1⟩ := hG.2.2
  exact ⟨hG.1.abs, hG.2.1.abs, m1, fun x => by rw [abs_abs]; exact hm1 x⟩

/-- Positivity of the Riesz energy on bounded integrable functions. -/
theorem s8p_Good_energy_nonneg (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) {G : Euc d → ℝ}
    (hG : s8p_Good G) :
    0 ≤ ∫ x, G x * HRS.Whole.convFun (rieszKernel d s) G x := by
  have hGa := hG.abs
  obtain ⟨b, hb⟩ := hGa.conv_bound hs0 hsd
  have hmeas : Measurable (fun p : Euc d × Euc d => rieszKernel d s (p.1 - p.2) * (G p.1 * G p.2)) :=
    ((s8p_riesz_meas s).comp (measurable_fst.sub measurable_snd)).mul
      ((hG.1.comp measurable_fst).mul (hG.1.comp measurable_snd))
  have hP : Integrable (fun p : Euc d × Euc d => rieszKernel d s (p.1 - p.2) * (G p.1 * G p.2))
      (volume.prod volume) := by
    rw [integrable_prod_iff hmeas.aestronglyMeasurable]
    refine ⟨Filter.Eventually.of_forall fun x => ?_, ?_⟩
    · have := (hG.conv_int hs0 hsd x).const_mul (G x)
      refine this.congr (Filter.Eventually.of_forall fun y => ?_)
      simp only; ring
    · have e : ∀ x, ∫ y, ‖rieszKernel d s (x - y) * (G x * G y)‖ =
          |G x| * HRS.Whole.convFun (rieszKernel d s) (fun y => |G y|) x := fun x => by
        unfold HRS.Whole.convFun
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (s8p_riesz_nonneg hs0 _), abs_mul]
        ring
      simp_rw [e]
      refine Integrable.mono' (hG.2.1.abs.mul_const b) ?_ (Filter.Eventually.of_forall fun x => ?_)
      · exact (hG.1.abs.mul (s8p_convFun_meas hG.1.abs)).aestronglyMeasurable
      · have h0 : 0 ≤ HRS.Whole.convFun (rieszKernel d s) (fun y => |G y|) x := by
          unfold HRS.Whole.convFun
          exact integral_nonneg fun y => mul_nonneg (s8p_riesz_nonneg hs0 _) (abs_nonneg _)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0, abs_abs]
        exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hb x)) (abs_nonneg _)
  have hE := HRS.MS.Psd.riesz_energy_nonneg hd hs0 hG.2.1 hP
  refine hE.trans (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  unfold HRS.Whole.convFun
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only
  ring

end HRS.MS.Spec
