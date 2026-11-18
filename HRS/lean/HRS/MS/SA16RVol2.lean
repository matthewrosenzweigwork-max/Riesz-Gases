import HRS.MS.SA16RVol1

/-!
# S.A.16 (SA16R) Vol2: continuity of the weakly singular Volterra operator

`sa16r_volt_contOn`: `(V w)(τ) = ∫_0^τ P τ s (w (τ - s)) ds` is continuous on `[0,T]` for `w` continuous on `[0,T]`.
`sa16r_volt_norm_le`: `‖(V w)(τ)‖ ≤ ∫_0^τ C s^{-1/2} sup‖w‖`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.Whole.AppendixA.Phase2SA16R

section Volt
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

lemma VoltKer.C_nonneg {T C : ℝ} {P : ℝ → ℝ → X →L[ℝ] X} (hP : VoltKer T C P) (hT : 0 < T) : 0 ≤ C := by
  have h := hP.bound T T hT le_rfl le_rfl
  have h5 : 0 ≤ ‖P T T‖ := norm_nonneg _
  have h6 : 0 < T ^ (-(1 / 2 : ℝ)) := Real.rpow_pos_of_pos hT _
  by_contra hneg
  have hneg' : C < 0 := lt_of_not_ge hneg
  nlinarith

lemma sa16r_rpow_int (T : ℝ) : IntegrableOn (fun s : ℝ => s ^ (-(1 / 2 : ℝ))) (Ioc 0 T) := by
  have h := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := T) (r := -(1 / 2 : ℝ))
    (by norm_num)
  rcases le_total 0 T with hT | hT
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).1 h
  · rw [Ioc_eq_empty_of_le hT]; exact integrableOn_empty

lemma sa16r_bdd {T : ℝ} {w : ℝ → X} (hw : ContinuousOn w (Icc 0 T)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ τ ∈ Icc (0 : ℝ) T, ‖w τ‖ ≤ M := by
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hw
  exact ⟨max M 0, le_max_right _ _, fun τ hτ => (hM τ hτ).trans (le_max_left _ _)⟩

lemma VoltKer.integrand_contOn {T C : ℝ} {P : ℝ → ℝ → X →L[ℝ] X} (hP : VoltKer T C P) {w : ℝ → X}
    (hw : ContinuousOn w (Icc 0 T)) {τ : ℝ} (hτ : τ ≤ T) :
    ContinuousOn (fun s : ℝ => P τ s (w (τ - s))) (Ioc 0 τ) := by
  have h := hP.contApply hw
  have hc : ContinuousOn (fun s : ℝ => (τ, s)) (Ioc 0 τ) :=
    (continuous_const.prodMk continuous_id).continuousOn
  exact h.comp hc (fun s hs => ⟨hs.1, hs.2, hτ⟩)

/-- the Volterra operator as an integral of an indicator -/
lemma sa16r_volt_eq_indicator (P : ℝ → ℝ → X →L[ℝ] X) (w : ℝ → X) {τ : ℝ} (hτ : 0 ≤ τ) :
    voltOp P w τ = ∫ s, (Ioc 0 τ).indicator (fun s => P τ s (w (τ - s))) s := by
  unfold voltOp
  rw [intervalIntegral.integral_of_le hτ, integral_indicator measurableSet_Ioc]

lemma VoltKer.integrable_integrand {T C : ℝ} {P : ℝ → ℝ → X →L[ℝ] X} (hP : VoltKer T C P) (hT : 0 < T)
    {w : ℝ → X} (hw : ContinuousOn w (Icc 0 T)) {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ : τ ≤ T) :
    IntegrableOn (fun s : ℝ => P τ s (w (τ - s))) (Ioc 0 τ) := by
  obtain ⟨M, hM0, hM⟩ := sa16r_bdd hw
  have hC := hP.C_nonneg hT
  refine Integrable.mono' (g := fun s : ℝ => C * M * s ^ (-(1 / 2 : ℝ)))
    (((sa16r_rpow_int τ).const_mul (C * M))) ?_ ?_
  · exact (hP.integrand_contOn hw hτ).aestronglyMeasurable measurableSet_Ioc
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun s hs => ?_
    have h1 := hP.bound τ s hs.1 hs.2 hτ
    have h2 := hM (τ - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩
    calc ‖P τ s (w (τ - s))‖ ≤ ‖P τ s‖ * ‖w (τ - s)‖ := (P τ s).le_opNorm _
      _ ≤ (C * s ^ (-(1 / 2 : ℝ))) * M :=
          mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hC (Real.rpow_nonneg hs.1.le _))
      _ = C * M * s ^ (-(1 / 2 : ℝ)) := by ring

theorem sa16r_volt_contOn {T C : ℝ} {P : ℝ → ℝ → X →L[ℝ] X} (hP : VoltKer T C P) (hT : 0 < T) {w : ℝ → X}
    (hw : ContinuousOn w (Icc 0 T)) : ContinuousOn (voltOp P w) (Icc 0 T) := by
  obtain ⟨M, hM0, hM⟩ := sa16r_bdd hw
  have hC := hP.C_nonneg hT
  set F : ℝ → ℝ → X := fun τ s => (Ioc 0 τ).indicator (fun s => P τ s (w (τ - s))) s with hF
  have heq : ∀ τ ∈ Icc (0 : ℝ) T, voltOp P w τ = ∫ s, F τ s := fun τ hτ =>
    sa16r_volt_eq_indicator P w hτ.1
  refine ContinuousOn.congr ?_ heq
  intro τ0 hτ0
  refine continuousWithinAt_of_dominated (bound := (Ioc 0 T).indicator
    (fun s : ℝ => C * M * s ^ (-(1 / 2 : ℝ)))) ?_ ?_ ?_ ?_
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
        _ ≤ (C * s ^ (-(1 / 2 : ℝ))) * M :=
            mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg hC (Real.rpow_nonneg hs.1.le _))
        _ = C * M * s ^ (-(1 / 2 : ℝ)) := by ring
    · simp only [hF, indicator_of_notMem hs, norm_zero]
      refine indicator_nonneg (fun s' hs' => ?_) s
      exact mul_nonneg (mul_nonneg hC hM0) (Real.rpow_nonneg hs'.1.le _)
  · have hI : IntegrableOn (fun s : ℝ => C * M * s ^ (-(1 / 2 : ℝ))) (Ioc 0 T) :=
      (sa16r_rpow_int T).const_mul (C * M)
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
