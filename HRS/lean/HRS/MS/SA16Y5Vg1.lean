import HRS.MS.SA16RVol4

/-!
# S.A.16 (SA16Y5) Vg1: weakly singular Volterra operators with kernel bound `C s^{-γ}`, `0 ≤ γ < 1` (B7, part 1)

`VoltKerG γ T C P`: `‖P τ s‖ ≤ C s^{-γ}` and strong joint continuity on `{0 < s ≤ τ ≤ T}` (`γ = 1/2` is `VoltKer`).  Generalisation of `SA16RVol1-2`:
continuity of the Volterra operator `voltOp P w` (`sa16y5g_volt_contOn`) and the integrability of the integrand.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.Whole.AppendixA.Phase2SA16R

structure VoltKerG {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (γ T C : ℝ)
    (P : ℝ → ℝ → X →L[ℝ] X) : Prop where
  γ0 : 0 ≤ γ
  γ1 : γ < 1
  bound : ∀ τ s : ℝ, 0 < s → s ≤ τ → τ ≤ T → ‖P τ s‖ ≤ C * s ^ (-γ)
  cont : ∀ x : X, ContinuousOn (fun q : ℝ × ℝ => P q.1 q.2 x) {q | 0 < q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ T}

section Volt
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] {γ : ℝ}

lemma VoltKerG.contApply {T C : ℝ} {P : ℝ → ℝ → X →L[ℝ] X} (hP : VoltKerG γ T C P) {w : ℝ → X}
    (hw : ContinuousOn w (Icc 0 T)) :
    ContinuousOn (fun q : ℝ × ℝ => P q.1 q.2 (w (q.1 - q.2)))
      {q | 0 < q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ T} := by
  intro q0 hq0
  obtain ⟨h0, h1, h2⟩ := hq0
  have hmem : ∀ q ∈ {q : ℝ × ℝ | 0 < q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ T}, q.1 - q.2 ∈ Icc (0 : ℝ) T := by
    rintro q ⟨a, b, c⟩
    exact ⟨by linarith, by linarith⟩
  refine sa16r_clm_apply_strong (B := C * (q0.2 / 2) ^ (-γ)) (fun v => hP.cont v q0 ⟨h0, h1, h2⟩) ?_ ?_
  · have hs : ∀ᶠ q in 𝓝[{q : ℝ × ℝ | 0 < q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ T}] q0, q0.2 / 2 < q.2 := by
      have hc : Continuous (fun q : ℝ × ℝ => q.2) := continuous_snd
      have : ∀ᶠ q in 𝓝 q0, q0.2 / 2 < q.2 := hc.continuousAt.eventually (lt_mem_nhds (by linarith))
      exact nhdsWithin_le_nhds this
    filter_upwards [hs, self_mem_nhdsWithin] with q hq hqS
    refine (hP.bound q.1 q.2 hqS.1 hqS.2.1 hqS.2.2).trans ?_
    have h3 : 0 < q0.2 / 2 := by linarith
    have := Real.rpow_le_rpow_of_nonpos h3 hq.le (by linarith [hP.γ0] : -γ ≤ 0)
    have hC : 0 ≤ C := by
      have := hP.bound q0.1 q0.2 h0 h1 h2
      have h5 : 0 ≤ ‖P q0.1 q0.2‖ := norm_nonneg _
      have h6 : 0 < q0.2 ^ (-γ) := Real.rpow_pos_of_pos h0 _
      by_contra hneg
      have hneg' : C < 0 := lt_of_not_ge hneg
      nlinarith
    exact mul_le_mul_of_nonneg_left this hC
  · have hl : ContinuousWithinAt (fun q : ℝ × ℝ => q.1 - q.2)
        {q : ℝ × ℝ | 0 < q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ T} q0 :=
      (continuous_fst.sub continuous_snd).continuousWithinAt
    exact ContinuousWithinAt.comp (g := w) (f := fun q : ℝ × ℝ => q.1 - q.2) (t := Icc (0 : ℝ) T)
      (hw (q0.1 - q0.2) ⟨by linarith, by linarith⟩) hl (fun q hq => hmem q hq)

lemma VoltKerG.C_nonneg {T C : ℝ} {P : ℝ → ℝ → X →L[ℝ] X} (hP : VoltKerG γ T C P) (hT : 0 < T) : 0 ≤ C := by
  have h := hP.bound T T hT le_rfl le_rfl
  have h5 : 0 ≤ ‖P T T‖ := norm_nonneg _
  have h6 : 0 < T ^ (-γ) := Real.rpow_pos_of_pos hT _
  by_contra hneg
  have hneg' : C < 0 := lt_of_not_ge hneg
  nlinarith

lemma sa16y5g_rpow_int (hγ1 : γ < 1) (T : ℝ) : IntegrableOn (fun s : ℝ => s ^ (-γ)) (Ioc 0 T) := by
  have h := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := T) (r := -γ)
    (by linarith)
  rcases le_total 0 T with hT | hT
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1 h
  · rw [Ioc_eq_empty_of_le hT]; exact integrableOn_empty

lemma VoltKerG.integrand_contOn {T C : ℝ} {P : ℝ → ℝ → X →L[ℝ] X} (hP : VoltKerG γ T C P) {w : ℝ → X}
    (hw : ContinuousOn w (Icc 0 T)) {τ : ℝ} (hτ : τ ≤ T) :
    ContinuousOn (fun s : ℝ => P τ s (w (τ - s))) (Ioc 0 τ) := by
  have h := hP.contApply hw
  have hc : ContinuousOn (fun s : ℝ => (τ, s)) (Ioc 0 τ) :=
    (continuous_const.prodMk continuous_id).continuousOn
  exact h.comp hc (fun s hs => ⟨hs.1, hs.2, hτ⟩)

lemma VoltKerG.integrable_integrand {T C : ℝ} {P : ℝ → ℝ → X →L[ℝ] X} (hP : VoltKerG γ T C P) (hT : 0 < T)
    {w : ℝ → X} (hw : ContinuousOn w (Icc 0 T)) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ : τ ≤ T) :
    IntegrableOn (fun s : ℝ => P τ s (w (τ - s))) (Ioc 0 τ) := by
  obtain ⟨M, hM0, hM⟩ := sa16r_bdd hw
  have hC := hP.C_nonneg hT
  refine Integrable.mono' (g := fun s : ℝ => C * M * s ^ (-γ))
    (((sa16y5g_rpow_int hP.γ1 τ).const_mul (C * M))) ?_ ?_
  · exact (hP.integrand_contOn hw hτ).aestronglyMeasurable measurableSet_Ioc
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun s hs => ?_
    have h1 := hP.bound τ s hs.1 hs.2 hτ
    have h2 := hM (τ - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
    calc ‖P τ s (w (τ - s))‖ ≤ ‖P τ s‖ * ‖w (τ - s)‖ := (P τ s).le_opNorm _
      _ ≤ (C * s ^ (-γ)) * M :=
          mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hC (Real.rpow_nonneg hs.1.le _))
      _ = C * M * s ^ (-γ) := by ring

theorem sa16y5g_volt_contOn {T C : ℝ} {P : ℝ → ℝ → X →L[ℝ] X} (hP : VoltKerG γ T C P) (hT : 0 < T) {w : ℝ → X}
    (hw : ContinuousOn w (Icc 0 T)) : ContinuousOn (voltOp P w) (Icc 0 T) := by
  obtain ⟨M, hM0, hM⟩ := sa16r_bdd hw
  have hC := hP.C_nonneg hT
  set F : ℝ → ℝ → X := fun τ s => (Ioc 0 τ).indicator (fun s => P τ s (w (τ - s))) s with hF
  have heq : ∀ τ ∈ Icc (0 : ℝ) T, voltOp P w τ = ∫ s, F τ s := fun τ hτ =>
    sa16r_volt_eq_indicator P w hτ.1
  refine ContinuousOn.congr ?_ heq
  intro τ0 hτ0
  refine continuousWithinAt_of_dominated (bound := (Ioc 0 T).indicator
    (fun s : ℝ => C * M * s ^ (-γ))) ?_ ?_ ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact (aestronglyMeasurable_indicator_iff measurableSet_Ioc).2
      ((hP.integrand_contOn hw hτ.2).aestronglyMeasurable measurableSet_Ioc)
  · filter_upwards [self_mem_nhdsWithin] with τ hτ
    refine Filter.Eventually.of_forall fun s => ?_
    by_cases hs : s ∈ Ioc 0 τ
    · have hs' : s ∈ Ioc 0 T := ⟨hs.1, hs.2.trans hτ.2⟩
      simp only [hF, indicator_of_mem hs, indicator_of_mem hs']
      have h1 := hP.bound τ s hs.1 hs.2 hτ.2
      have h2 := hM (τ - s) ⟨by linarith [hs.2], by linarith [hs.1, hτ.2]⟩
      calc ‖P τ s (w (τ - s))‖ ≤ ‖P τ s‖ * ‖w (τ - s)‖ := (P τ s).le_opNorm _
        _ ≤ (C * s ^ (-γ)) * M :=
            mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hC (Real.rpow_nonneg hs.1.le _))
        _ = C * M * s ^ (-γ) := by ring
    · simp only [hF, indicator_of_notMem hs, norm_zero]
      refine indicator_nonneg (fun s' hs' => ?_) s
      exact mul_nonneg (mul_nonneg hC hM0) (Real.rpow_nonneg hs'.1.le _)
  · have hI : IntegrableOn (fun s : ℝ => C * M * s ^ (-γ)) (Ioc 0 T) :=
      (sa16y5g_rpow_int hP.γ1 T).const_mul (C * M)
    exact hI.integrable_indicator measurableSet_Ioc
  · -- pointwise continuity for a.e. s
    have hne : ∀ᵐ s : ℝ, s ≠ τ0 := by
      filter_upwards [(Set.countable_singleton τ0).ae_notMem (volume : Measure ℝ)] with s hs
      exact hs
    filter_upwards [hne] with s hs
    rcases lt_or_gt_of_ne hs with hlt | hgt
    · -- s < τ0
      by_cases hs0 : 0 < s
      · have hmem : Icc s T ∈ 𝓝[Icc 0 T] τ0 := by
          refine mem_nhdsWithin.2 ⟨Ioi s, isOpen_Ioi, hlt, fun τ hτ => ?_⟩
          exact ⟨hτ.1.le, hτ.2.2⟩
        have hg : ContinuousWithinAt (fun τ : ℝ => P τ s (w (τ - s))) (Icc s T) τ0 := by
          have h := hP.contApply hw
          have hc : ContinuousOn (fun τ : ℝ => (τ, s)) (Icc s T) :=
            (continuous_id.prodMk continuous_const).continuousOn
          exact (h.comp hc (fun τ hτ => ⟨hs0, hτ.1, hτ.2⟩)) τ0 (show τ0 ∈ Icc s T from ⟨hlt.le, hτ0.2⟩)
        have hev : ∀ᶠ τ in 𝓝[Icc 0 T] τ0, F τ s = P τ s (w (τ - s)) := by
          have : ∀ᶠ τ in 𝓝 τ0, s < τ := Ioi_mem_nhds hlt
          filter_upwards [nhdsWithin_le_nhds this] with τ hτ
          simp only [hF]
          exact indicator_of_mem (show s ∈ Ioc 0 τ from ⟨hs0, le_of_lt hτ⟩) _
        refine ContinuousWithinAt.congr_of_eventuallyEq ?_ hev (by
          simp only [hF]
          exact indicator_of_mem (show s ∈ Ioc 0 τ0 from ⟨hs0, hlt.le⟩) _)
        exact hg.mono_of_mem_nhdsWithin hmem
      · have hev : ∀ᶠ τ in 𝓝[Icc 0 T] τ0, F τ s = 0 := by
          refine Filter.Eventually.of_forall fun τ => ?_
          simp only [hF]
          exact indicator_of_notMem (fun h => hs0 h.1) _
        exact continuousWithinAt_const.congr_of_eventuallyEq hev (by
          simp only [hF]
          exact indicator_of_notMem (fun h => hs0 h.1) _)
    · -- s > τ0
      have hev : ∀ᶠ τ in 𝓝[Icc 0 T] τ0, F τ s = 0 := by
        have : ∀ᶠ τ in 𝓝 τ0, τ < s := Iio_mem_nhds hgt
        filter_upwards [nhdsWithin_le_nhds this] with τ hτ
        simp only [hF]
        exact indicator_of_notMem (fun h => by linarith [h.2]) _
      exact continuousWithinAt_const.congr_of_eventuallyEq hev (by
        simp only [hF]
        exact indicator_of_notMem (fun h => by linarith [h.2]) _)


end Volt

end HRS.Whole.AppendixA.Phase2SA16R
