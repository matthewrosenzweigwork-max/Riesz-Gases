import HRS.MS.R26T8AP03b

/-!
# S8.2 local Newton layer, packet T8A.P03 (part c): Y-derivatives of `int Theta(Y,w) T(w) dw`
`r26t8a_stage2`: for `C^p` compactly supported `Theta (Y,w)` and `C^p` vector valued `T`, `D^p_Y` commutes with the `w`-integral
(merged `lc4_iteratedFDeriv_integral`, majorant = joint jets bound on the compact projection of the support).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_jets_bdd2 {X' : Type} [NormedAddCommGroup X'] [NormedSpace ℝ X'] {V : Type} [NormedAddCommGroup V]
    [NormedSpace ℝ V] {f : X' → V} {p : ℕ} (hf : ContDiff ℝ (p : WithTop ℕ∞) f) (hc : HasCompactSupport f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i ≤ p, ∀ x, ‖iteratedFDeriv ℝ i f x‖ ≤ B := by
  have hC : ∀ i : ℕ, ∃ C : ℝ, ∀ y, i ≤ p → ‖iteratedFDeriv ℝ i f y‖ ≤ C := fun i => by
    by_cases hi : i ≤ p
    · obtain ⟨C, hC⟩ := (hf.continuous_iteratedFDeriv (by exact_mod_cast hi)).bounded_above_of_compact_support
        (hc.iteratedFDeriv i)
      exact ⟨C, fun y _ => hC y⟩
    · exact ⟨0, fun y h => absurd h hi⟩
  choose C hC using hC
  refine ⟨∑ i ∈ Finset.range (p + 1), max (C i) 0, Finset.sum_nonneg fun i _ => le_max_right _ _,
    fun i hi y => ?_⟩
  have h1 : C i ≤ ∑ i ∈ Finset.range (p + 1), max (C i) 0 :=
    (le_max_left _ _).trans (Finset.single_le_sum (f := fun i => max (C i) 0)
      (fun i _ => le_max_right _ _) (Finset.mem_range.2 (by omega)))
  exact (hC i y hi).trans h1

theorem r26t8a_stage2 {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {Θ : Euc d × Euc d → ℝ} {T : Euc d → V} {p : ℕ}
    (hΘ : ContDiff ℝ (p : WithTop ℕ∞) Θ) (hT : ContDiff ℝ (p : WithTop ℕ∞) T) (hc : HasCompactSupport Θ) (X : Euc d) :
    iteratedFDeriv ℝ p (fun Y => ∫ w, Θ (Y, w) • T w) X = ∫ w, iteratedFDeriv ℝ p (fun Y => Θ (Y, w) • T w) X := by
  set Λ : Euc d × Euc d → V := fun Yw => Θ Yw • T Yw.2 with hΛ
  have hΛd : ContDiff ℝ (p : WithTop ℕ∞) Λ := hΘ.smul (hT.comp contDiff_snd)
  have hsupp : Function.support Λ ⊆ tsupport Θ := fun y hy =>
    subset_tsupport _ (fun h => hy (by simp [hΛ, h]))
  have hΛc : HasCompactSupport Λ := HasCompactSupport.of_support_subset_isCompact hc hsupp
  obtain ⟨B, hB0, hB⟩ := r26t8a_jets_bdd2 hΛd hΛc
  set K2 : Set (Euc d) := Prod.snd '' tsupport Θ with hK2
  have hK2c : IsCompact K2 := hc.image continuous_snd
  have hint : Integrable (K2.indicator fun _ => B) :=
    (integrable_indicator_iff hK2c.measurableSet).2 (integrableOn_const hK2c.measure_lt_top.ne)
  have key := HRS.MS.Lc.lc4_iteratedFDeriv_integral (μ := (volume : Measure (Euc d)))
    (fun w Y => Θ (Y, w) • T w) p
    (fun w => (hΘ.comp (contDiff_id.prodMk contDiff_const)).smul contDiff_const)
    (Φ := K2.indicator fun _ => B) hint
    (fun i hi w x => by
      have h1 : ‖iteratedFDeriv ℝ i (fun Y => Λ (Y, w)) x‖ ≤ ‖iteratedFDeriv ℝ i Λ (x, w)‖ :=
        r26t8a_slice_jet_norm (hΛd.of_le (by exact_mod_cast hi)) x w
      by_cases hw : (x, w) ∈ tsupport Θ
      · have : w ∈ K2 := ⟨_, hw, rfl⟩
        rw [Set.indicator_of_mem this]
        exact h1.trans (hB i hi _)
      · have hΛt : tsupport Λ ⊆ tsupport Θ := closure_minimal hsupp (isClosed_tsupport _)
        have h0 : iteratedFDeriv ℝ i Λ (x, w) = 0 :=
          image_eq_zero_of_notMem_tsupport (fun h => hw (hΛt (tsupport_iteratedFDeriv_subset i h)))
        have hnn : 0 ≤ (K2.indicator fun _ => B) w := Set.indicator_nonneg (fun _ _ => hB0) w
        rw [h0, norm_zero] at h1
        exact h1.trans hnn)
    (fun i hi x => by
      have hΛi : ContDiff ℝ (i : WithTop ℕ∞) Λ := hΛd.of_le (by exact_mod_cast hi)
      have e : (fun w => iteratedFDeriv ℝ i (fun Y => Θ (Y, w) • T w) x) = fun w =>
          (iteratedFDeriv ℝ i Λ (x, w)).compContinuousLinearMap (fun _ => ContinuousLinearMap.inl ℝ (Euc d) (Euc d)) :=
        funext fun w => r26t8a_slice_jet hΛi x w
      rw [e]
      exact ((ContinuousMultilinearMap.compContinuousLinearMapL
        (fun _ : Fin i => ContinuousLinearMap.inl ℝ (Euc d) (Euc d))).continuous.comp
        ((hΛd.continuous_iteratedFDeriv (by exact_mod_cast hi)).comp
          (continuous_const.prodMk continuous_id))).aestronglyMeasurable)
  exact key.2 p le_rfl X

end HRS.MS.R26T8A
