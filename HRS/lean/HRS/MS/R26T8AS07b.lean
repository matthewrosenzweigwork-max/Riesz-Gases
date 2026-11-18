import HRS.MS.R26T8AD01

/-!
# S8.2 T8A.S07b: locality of the Itô integral of a time-clipped integrand

For `Ψ` progressive `L²` and `0 ≤ a ≤ s`, the integral of `1_{[a,s]} Ψ` is `M_{u ∧ s} - M_{u ∧ a}` (`M` the integral of `Ψ`),
a.s. simultaneously in `u`; and an integrand vanishing before `a` has integral vanishing at time `a`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS

theorem r26t8a_s07b_sq_null {Omega I : Type*} [mOmega : MeasurableSpace Omega] [Fintype I]
    (P : Measure Omega) (Φ : ℝ → Omega → I → ℝ) (c T : ℝ)
    (h : ∀ r w k, r ∈ Icc 0 T → r ≠ c → Φ r w k = 0) : sqIntegralOn P Φ T = 0 := by
  unfold sqIntegralOn
  have hw : ∀ w, ∫⁻ r in Icc 0 T, ∑ k, ‖Φ r w k‖ₑ ^ 2 = 0 := by
    intro w
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [(Set.countable_singleton c).ae_notMem (volume : Measure ℝ)] with r hr hrm
    have hrc : r ≠ c := by simpa using hr
    exact Finset.sum_eq_zero fun k _ => by simp [h r w k hrm hrc]
  simp [hw]

theorem r26t8a_s07b_local {Omega I : Type*} [mOmega : MeasurableSpace Omega] [Fintype I]
    (P : Measure Omega) [IsProbabilityMeasure P] (F : Filtration ℝ mOmega) (W : ℝ≥0 → Omega → I → ℝ)
    (hW : IsBrownianFiltration P F W) (Ψ : ℝ → Omega → I → ℝ) (hΨ : IsProgressiveL2 P F Ψ)
    (a s : ℝ) (ha : 0 ≤ a) (has : a ≤ s)
    (hcl : IsProgressiveL2 P F (r26t8a_clipIntegrand a s Ψ)) :
    ∀ᵐ w ∂P, ∀ u, itoIntegral P F W (r26t8a_clipIntegrand a s Ψ) u w =
      itoIntegral P F W Ψ (min u s) w - itoIntegral P F W Ψ (min u a) w := by
  classical
  have hA : MeasurableSet[F a] (Set.univ : Set Omega) := MeasurableSet.univ
  have hR : IsProgressiveL2 P F (restrictFun Ψ a s Set.univ) := hΨ.restrictFun hA
  have hRI := (isItoIntegral_itoIntegral hW hΨ).restrict hW hΨ ha has hA
  have h1 := (isItoIntegral_itoIntegral hW hR).ae_eq_forall hW hRI hR
  have h2 := itoIntegral_congr hW hcl hR (fun T => by
    refine r26t8a_s07b_sq_null P _ a T fun r w k _ hne => ?_
    have hiff : r ∈ Icc a s ↔ r ∈ Ioc a s := by
      simp only [mem_Icc, mem_Ioc]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨lt_of_le_of_ne h1 (Ne.symm hne), h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1.le, h2⟩
    by_cases hr : r ∈ Icc a s
    · simp [r26t8a_clipIntegrand, restrictFun, hr, hiff.1 hr]
    · simp [r26t8a_clipIntegrand, restrictFun, hr, mt hiff.2 hr])
  filter_upwards [h1, h2] with w a1 a2 u
  rw [a2 u, a1 u]
  simp

theorem r26t8a_s07b_zero {Omega I : Type*} [mOmega : MeasurableSpace Omega] [Fintype I]
    (P : Measure Omega) [IsProbabilityMeasure P] (F : Filtration ℝ mOmega) (W : ℝ≥0 → Omega → I → ℝ)
    (hW : IsBrownianFiltration P F W) (D : ℝ → Omega → I → ℝ) (a b : ℝ)
    (hD : IsProgressiveL2 P F (r26t8a_clipIntegrand a b D)) :
    ∀ᵐ w ∂P, itoIntegral P F W (r26t8a_clipIntegrand a b D) a w = 0 := by
  have hsq : sqIntegralOn P (r26t8a_clipIntegrand a b D) a = 0 := by
    refine r26t8a_s07b_sq_null P _ a a fun r w k hr hne => ?_
    have : r ∉ Icc a b := fun h => hne (le_antisymm hr.2 h.1)
    simp [r26t8a_clipIntegrand, this]
  have h1 := (isItoIntegral_itoIntegral hW hD).lintegral_sq hW hD a
  rw [hsq] at h1
  have hmeas : AEMeasurable (fun w => itoIntegral P F W (r26t8a_clipIntegrand a b D) a w) P :=
    ((adapted_itoIntegral P F W _ a).mono (F.le a) le_rfl).aemeasurable
  exact ae_eq_zero_of_lintegral_enorm_sq_eq_zero hmeas h1

end HRS.MS.R26T8A

end
