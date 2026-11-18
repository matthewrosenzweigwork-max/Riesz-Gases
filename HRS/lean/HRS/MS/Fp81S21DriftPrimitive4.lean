import HRS.MS.Fp81S21DriftPrimitive3

/-! Fixed-time measurability of the triangular source primitive. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
namespace HRS.Fp81.S21

/-- Measurability of the iterated primitive follows from joint measurability
of the zero extensions, independently of pathwise integrability. -/
theorem fp81s21_measurable_source_primitive
    {Ω : Type*} [MeasurableSpace Ω] {b t : ℝ} (hbt : b ≤ t)
    (Q : ℝ × Ω → ℝ) (K : (ℝ × ℝ) × Ω → ℝ)
    (hQ : Measurable Q) (hK : Measurable K) :
    Measurable (fun ω => ∫ s in b..t, Q (s, ω) + ∫ v in b..s, K ((v, s), ω)) := by
  let S : Set ((ℝ × Ω) × ℝ) := {z | b < z.2 ∧ z.2 ≤ z.1.1}
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd (measurable_fst.comp measurable_fst))
  let F : (ℝ × Ω) × ℝ → ℝ := fun z => K ((z.2, z.1.1), z.1.2)
  have hF : Measurable F := by
    apply hK.comp
    exact (measurable_snd.prodMk (measurable_fst.comp measurable_fst)).prodMk
      (measurable_snd.comp measurable_fst)
  let H : ℝ × Ω → ℝ := fun z => ∫ v, S.indicator F (z, v) ∂volume
  have hH : Measurable H := (hF.indicator hS).stronglyMeasurable.integral_prod_right'.measurable
  have hInner : ∀ s ω, b ≤ s → H (s, ω) = ∫ v in b..s, K ((v, s), ω) := by
    intro s ω hs
    rw [intervalIntegral.integral_of_le hs, ← integral_indicator measurableSet_Ioc]
    apply integral_congr_ae
    filter_upwards with v
    by_cases hv : v ∈ Ioc b s
    · have hm : ((s, ω), v) ∈ S := hv
      rw [indicator_of_mem hm, indicator_of_mem hv]
    · have hm : ((s, ω), v) ∉ S := hv
      rw [indicator_of_notMem hm, indicator_of_notMem hv]
  have hP : Measurable (fun z : Ω × ℝ => Q (z.2, z.1) + H (z.2, z.1)) :=
    (hQ.comp (measurable_snd.prodMk measurable_fst)).add
      (hH.comp (measurable_snd.prodMk measurable_fst))
  have hOut := hP.stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioc b t))
  have hEq : (fun ω => ∫ s in b..t, Q (s, ω) + ∫ v in b..s, K ((v, s), ω)) =
      (fun ω => ∫ s in Ioc b t, Q (s, ω) + H (s, ω)) := by
    funext ω
    rw [intervalIntegral.integral_of_le hbt]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro s hs
    dsimp only
    rw [hInner s ω hs.1.le]
  rw [hEq]
  exact hOut.measurable

#print axioms fp81s21_measurable_source_primitive
end HRS.Fp81.S21
end
