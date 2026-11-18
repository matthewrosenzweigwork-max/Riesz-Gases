import HRS.MS.Fp81S21DriftPrimitive2

/-! Deterministic triangular Fubini for an integrable square. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
namespace HRS.Fp81.S21

/-- Reverse the order of integration over the source-time triangle. -/
theorem fp81s21_triangular_fubini {F : ℝ → ℝ → ℝ} {b t T : ℝ}
    (hbt : b ≤ t) (htT : t ≤ T)
    (hF : IntegrableOn (fun z : ℝ × ℝ => F z.2 z.1)
      (Icc b T ×ˢ Icc b T) (volume.prod volume)) :
    (∫ v in b..t, ∫ s in v..t, F v s) =
      ∫ s in b..t, ∫ v in b..s, F v s := by
  let R : Set (ℝ × ℝ) := {z | b < z.2 ∧ z.2 ≤ z.1 ∧ z.1 ≤ t}
  have hRm : MeasurableSet R :=
    (measurableSet_lt measurable_const measurable_snd).inter
      ((measurableSet_le measurable_snd measurable_fst).inter
        (measurableSet_le measurable_fst measurable_const))
  let G : ℝ → ℝ → ℝ := fun s v => R.indicator (fun z => F z.2 z.1) (s, v)
  have hRsub : R ⊆ Icc b T ×ˢ Icc b T := by
    intro z hz
    exact ⟨⟨hz.1.le.trans hz.2.1, hz.2.2.trans htT⟩,
      ⟨hz.1.le, hz.2.1.trans (hz.2.2.trans htT)⟩⟩
  have hGi : Integrable (Function.uncurry G) (volume.prod volume) := by
    exact (integrable_indicator_iff hRm).2 (hF.mono_set hRsub)
  have hswap := integral_integral_swap hGi
  have hL : ∀ s : ℝ, ∫ v, G s v =
      (Ioc b t).indicator (fun s => ∫ v in Ioc b s, F v s) s := by
    intro s
    by_cases hs : s ∈ Ioc b t
    · rw [indicator_of_mem hs, ← integral_indicator measurableSet_Ioc]
      refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
      simp only [G, R]
      by_cases hv : v ∈ Ioc b s
      · rw [indicator_of_mem hv, indicator_of_mem]
        exact ⟨hv.1, hv.2, hs.2⟩
      · rw [indicator_of_notMem hv, indicator_of_notMem]
        intro h; exact hv ⟨h.1, h.2.1⟩
    · rw [indicator_of_notMem hs]
      have : ∀ v, G s v = 0 := by
        intro v
        simp only [G, R]
        refine indicator_of_notMem ?_ _
        intro h; exact hs ⟨by linarith [h.1, h.2.1], h.2.2⟩
      simp [this]
  have hRr : ∀ v : ℝ, ∫ s, G s v =
      (Ioc b t).indicator (fun v => ∫ s in Ioc v t, F v s) v := by
    intro v
    by_cases hv : v ∈ Ioc b t
    · rw [indicator_of_mem hv, ← integral_indicator measurableSet_Ioc]
      refine integral_congr_ae ?_
      filter_upwards [(Set.countable_singleton v).ae_notMem (volume : Measure ℝ)] with s hsv
      simp only [G, R]
      by_cases hs : s ∈ Ioc v t
      · rw [indicator_of_mem hs, indicator_of_mem]
        exact ⟨hv.1, hs.1.le, hs.2⟩
      · rw [indicator_of_notMem hs, indicator_of_notMem]
        intro h
        refine hs ⟨lt_of_le_of_ne h.2.1 ?_, h.2.2⟩
        intro heq; exact hsv (by simpa using heq.symm)
    · rw [indicator_of_notMem hv]
      have : ∀ s, G s v = 0 := by
        intro s
        simp only [G, R]
        refine indicator_of_notMem ?_ _
        intro h; exact hv ⟨h.1, by linarith [h.2.1, h.2.2]⟩
      simp [this]
  simp only [hL, hRr] at hswap
  rw [integral_indicator measurableSet_Ioc, integral_indicator measurableSet_Ioc] at hswap
  rw [intervalIntegral.integral_of_le hbt, intervalIntegral.integral_of_le hbt]
  calc
    (∫ v in Ioc b t, ∫ s in v..t, F v s) =
        ∫ v in Ioc b t, ∫ s in Ioc v t, F v s := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro v hv
          dsimp only
          rw [intervalIntegral.integral_of_le hv.2]
    _ = ∫ s in Ioc b t, ∫ v in Ioc b s, F v s := hswap.symm
    _ = ∫ s in Ioc b t, ∫ v in b..s, F v s := by
          apply setIntegral_congr_fun measurableSet_Ioc
          intro s hs
          dsimp only
          rw [intervalIntegral.integral_of_le hs.1.le]

#print axioms fp81s21_triangular_fubini
end HRS.Fp81.S21
end
