import HRS.MP.KolmChentsov
import HRS.Whole.Oscillator

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace HRS.Fp81.S21

open HRS.Whole

/-- A measurable process with a local fourth-moment increment bound has a continuous
`OscDual`-valued modification on the given compact horizon. -/
theorem fp81s21_local_modification
    {d : ℕ} {m : ℝ} {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {H C : ℝ} (hH : 0 < H) (X : ℝ → Ω → OscDual d m)
    (hm : ∀ t, Measurable (X t))
    (h4 : ∀ s ∈ Set.Icc (0 : ℝ) H, ∀ t ∈ Set.Icc (0 : ℝ) H,
      ∫⁻ ω, ‖X t ω - X s ω‖ₑ ^ (4 : ℝ) ∂P ≤
        ENNReal.ofReal (C * |t - s| ^ (2 : ℝ))) :
    ∃ Y : Ω → OscPath d m H, Measurable Y ∧
      ∀ t (ht : t ∈ Set.Icc (0 : ℝ) H),
        (fun ω => OscPath.at' (Y ω) ⟨t, ht⟩) =ᵐ[P] X t := by
  classical
  obtain ⟨r, q, hr0, hr1, hq0, hq1, hqr⟩ :=
    HRS.MP.KC.mkc_consts (β := (1 : ℝ)) (p := (4 : ℝ)) (by norm_num) (by norm_num)
  have hmoment : ∀ s ∈ Set.Icc (0 : ℝ) H, ∀ t ∈ Set.Icc (0 : ℝ) H,
      ∫⁻ ω, ‖X t ω - X s ω‖ₑ ^ (4 : ℝ) ∂P ≤
        ENNReal.ofReal (C * |t - s| ^ (1 + (1 : ℝ))) := by
    intro s hs t ht
    simpa only [show (1 : ℝ) + 1 = 2 by norm_num] using h4 s hs t ht
  have hZmeas : ∀ t, Measurable (HRS.MP.KC.mkc_Zc X H r t) :=
    fun t => HRS.MP.KC.mkc_Zc_meas X H r hH hr0.le hr1 hm t
  refine ⟨fun ω =>
      ⟨fun t => HRS.MP.KC.mkc_Zc X H r t ω,
        HRS.MP.KC.mkc_continuous X H r hH hr0.le hr1 ω⟩, ?_, ?_⟩
  · refine ContinuousMap.measurable_iff_eval.2 fun t => ?_
    change Measurable (fun ω => HRS.MP.KC.mkc_Zc X H r t ω)
    exact hZmeas t
  · intro t ht
    exact HRS.MP.KC.mkc_Zc_ae_eq X H r P hm hH (by norm_num) (by norm_num)
      hmoment hr0 hr1 hq0 hq1 hqr ht

#print axioms fp81s21_local_modification

end HRS.Fp81.S21

end
