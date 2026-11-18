import HRS.MC.CepH2Sde1
import HRS.Appendix.B15DAux3

/-!
# CEPH2, S1b (part 1): Dynkin's formula for an additive-noise SDE on `Ch N` with a bounded gradient
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

/-- Pathwise Itô formula with integrable mean-zero remainder, for `g ∈ C²` with bounded gradient. -/
theorem h2_dynkin [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → Fin N → ℝ}
    (hW : IsBrownianFiltration P ℱ W) {σ : Fin N → Ch N} {B : Ch N → Ch N} (hB : Continuous B)
    {Z : ℝ → Ω → Ch N} (hZ0 : ∀ t : ℝ, Measurable[ℱ t] (Z 0))
    (hZad : ∀ t : ℝ, 0 ≤ t → Measurable[ℱ t] (Z t)) (hZc : ∀ ω, Continuous fun t => Z t ω)
    (hZeq : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Z t ω = Z 0 ω + (∫ s in Icc (0 : ℝ) t, B (Z s ω)) + ∑ k, (W (Real.toNNReal t) ω k - W 0 ω k) • σ k)
    {g : Ch N → ℝ} (hg : ContDiff ℝ 2 g) {C : ℝ} (hC : ∀ y, ‖fderiv ℝ g y‖ ≤ C) (t : ℝ) (ht : 0 ≤ t) :
    ∃ M : Ω → ℝ, Integrable M P ∧ ∫ ω, M ω ∂P = 0 ∧
      ∀ᵐ ω ∂P, g (Z t ω) = g (Z 0 ω) +
        (∫ s in Icc (0 : ℝ) t, fderiv ℝ g (Z s ω) (B (Z s ω)) +
          (1 / 2) * ∑ k, fderiv ℝ (fderiv ℝ g) (Z s ω) (σ k) (σ k)) + M ω := by
  have hYcI : ∀ ω, ContinuousOn (fun s => Z s ω) (Set.Ici 0) := fun ω => (hZc ω).continuousOn
  -- progressivity of the path
  have hXprog : IsProgressive ℱ (ofNNRealTime (fun u : ℝ≥0 => Z (u : ℝ))) := by
    have e : ofNNRealTime (fun u : ℝ≥0 => Z (u : ℝ)) = fun s ω => Z (max s 0) ω := by
      funext s ω
      simp [ofNNRealTime, Real.coe_toNNReal']
    rw [e]
    exact b15d2_isProgressive_clampPath hZ0 hZad hYcI
  have hbprog : IsProgressive ℱ (ofNNRealTime (fun (u : ℝ≥0) (ω : Ω) => B (Z (u : ℝ) ω))) :=
    isProgressive_comp_measurable' (ofNNRealTime (fun u : ℝ≥0 => Z (u : ℝ))) hXprog
      (fun _ y => B y) (hB.comp continuous_snd).measurable
  -- the Itô integrand: progressive and bounded
  have hdc : Continuous (fun y => fderiv ℝ g y) := hg.continuous_fderiv (by simp)
  let G : ℝ → Ch N → (Fin N) → ℝ := fun s y k => if s ∈ Set.Icc 0 t then fderiv ℝ g y (σ k) else 0
  have hΨeq : ∀ s ω k, itoIntegrand t Set.univ (fun _ x => g x) (ofNNRealTime (fun u : ℝ≥0 => Z (u : ℝ)))
      (fun _ _ => σ) s ω k = G s (ofNNRealTime (fun u : ℝ≥0 => Z (u : ℝ)) s ω) k := by
    intro s ω k
    by_cases hs : s ∈ Set.Icc 0 t
    · simp only [itoIntegrand, G, if_pos hs, Set.indicator_of_mem hs, Set.mem_univ, Set.setOf_true,
        Set.indicator_univ]
    · simp only [itoIntegrand, G, if_neg hs, Set.indicator_of_notMem hs]
  have hΨprog : IsProgressive ℱ (fun s ω k => itoIntegrand t Set.univ (fun _ x => g x)
      (ofNNRealTime (fun u : ℝ≥0 => Z (u : ℝ))) (fun _ _ => σ) s ω k) := by
    have hk : ∀ k : Fin N, IsProgressive ℱ (fun s ω => itoIntegrand t Set.univ (fun _ x => g x)
        (ofNNRealTime (fun u : ℝ≥0 => Z (u : ℝ))) (fun _ _ => σ) s ω k) := by
      intro k
      have hc := hdc.clm_apply (continuous_const (y := σ k))
      have hm : Measurable (Function.uncurry (fun (s : ℝ) (y : Ch N) =>
          if s ∈ Set.Icc 0 t then fderiv ℝ g y (σ k) else 0)) :=
        Measurable.ite (measurableSet_Icc.preimage measurable_fst) (hc.measurable.comp measurable_snd)
          measurable_const
      have hg' := isProgressive_comp_measurable' (ofNNRealTime (fun u : ℝ≥0 => Z (u : ℝ))) hXprog
        (fun (s : ℝ) (y : Ch N) => if s ∈ Set.Icc 0 t then fderiv ℝ g y (σ k) else 0) hm
      have e : (fun s ω => itoIntegrand t Set.univ (fun _ x => g x) (ofNNRealTime (fun u : ℝ≥0 => Z (u : ℝ)))
          (fun _ _ => σ) s ω k) = fun s ω => (fun (s : ℝ) (y : Ch N) =>
            if s ∈ Set.Icc 0 t then fderiv ℝ g y (σ k) else 0) s
              (ofNNRealTime (fun u : ℝ≥0 => Z (u : ℝ)) s ω) := by
        funext s ω
        exact hΨeq s ω k
      rw [e]
      exact hg'
    exact isProgressive_pi hk
  have hΨbd : ∀ s ω k, |itoIntegrand t Set.univ (fun _ x => g x) (ofNNRealTime (fun u : ℝ≥0 => Z (u : ℝ)))
      (fun _ _ => σ) s ω k| ≤ max C 0 * ∑ j : Fin N, ‖σ j‖ := by
    intro s ω k
    rw [hΨeq s ω k]
    simp only [G]
    split_ifs with hs
    · have hb : ‖fderiv ℝ g (ofNNRealTime (fun u : ℝ≥0 => Z (u : ℝ)) s ω)‖ ≤ max C 0 :=
        (hC _).trans (le_max_left _ _)
      calc |fderiv ℝ g (ofNNRealTime (fun u : ℝ≥0 => Z (u : ℝ)) s ω) (σ k)|
          ≤ ‖fderiv ℝ g (ofNNRealTime (fun u : ℝ≥0 => Z (u : ℝ)) s ω)‖ * ‖σ k‖ := by
            rw [← Real.norm_eq_abs]
            exact ContinuousLinearMap.le_opNorm _ _
        _ ≤ max C 0 * ‖σ k‖ := mul_le_mul hb le_rfl (norm_nonneg _) ((norm_nonneg _).trans hb)
        _ ≤ max C 0 * ∑ j : Fin N, ‖σ j‖ :=
            mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j _ => norm_nonneg (σ j))
              (Finset.mem_univ k)) (le_max_right _ _)
    · simp only [abs_zero]
      exact mul_nonneg (le_max_right _ _) (Finset.sum_nonneg fun j _ => norm_nonneg _)
  have hΨL2 : IsProgressiveL2 P ℱ (fun s ω k => itoIntegrand t Set.univ (fun _ x => g x)
      (ofNNRealTime (fun u : ℝ≥0 => Z (u : ℝ))) (fun _ _ => σ) s ω k) :=
    IsProgressiveL2.of_bounded P hΨprog _ hΨbd
  -- the Itô formula
  have hXmeas : ∀ u : ℝ≥0, Measurable (fun ω => Z (u : ℝ) ω) := fun u =>
    (hZad (u : ℝ) u.2).mono (ℱ.le _) le_rfl
  have hX₀ : ∀ s : ℝ, Measurable[ℱ s] (fun ω => Z ((0 : ℝ≥0) : ℝ) ω) := fun s => by
    simpa using hZ0 s
  have hbint : ∀ᵐ ω ∂P, IntegrableOn (fun s : ℝ => B (Z (Real.toNNReal s : ℝ) ω)) (Set.Icc 0 t) := by
    refine ae_of_all _ fun ω => ?_
    refine Continuous.integrableOn_Icc ?_
    exact hB.comp ((hZc ω).comp (continuous_subtype_val.comp continuous_real_toNNReal))
  have hX : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, (u : ℝ) ≤ t →
      Z (u : ℝ) ω = Z ((0 : ℝ≥0) : ℝ) ω
        + (∫ s in Set.Icc (0 : ℝ) (u : ℝ), B (Z (Real.toNNReal s : ℝ) ω))
        + ∑ k, (W u ω k - W 0 ω k) • σ k := by
    filter_upwards [hZeq] with ω hω u hu
    have h := hω (u : ℝ) u.2
    have hint : ∫ s in Set.Icc (0 : ℝ) (u : ℝ), B (Z s ω)
        = ∫ s in Set.Icc (0 : ℝ) (u : ℝ), B (Z (Real.toNNReal s : ℝ) ω) :=
      setIntegral_congr_fun measurableSet_Icc (fun s hs => by rw [Real.coe_toNNReal _ hs.1])
    rw [h, hint, NNReal.coe_zero, Real.toNNReal_coe]
  have hito := ito_formula_additive_time_independent (P := P) (ℱ := ℱ) hW (T := t) ht g hg σ
    (fun (u : ℝ≥0) (ω : Ω) => Z (u : ℝ) ω) hXmeas hX₀
    (fun (u : ℝ≥0) (ω : Ω) => B (Z (u : ℝ) ω)) hbprog hbint hX
  have hloc := localItoIntegral_eq_itoIntegral hW hΨL2
  refine ⟨fun ω => localItoIntegral P ℱ W (itoIntegrand t Set.univ (fun _ x => g x)
      (ofNNRealTime (fun u : ℝ≥0 => Z (u : ℝ))) (fun _ _ => σ)) t ω, ?_, ?_, ?_⟩
  · refine (memLp_two_itoIntegral hW hΨL2 t).integrable one_le_two |>.congr ?_
    filter_upwards [hloc] with ω hω
    exact (hω t).symm
  · rw [integral_congr_ae (by filter_upwards [hloc] with ω hω using hω t)]
    exact integral_itoIntegral hW hΨL2 t
  · filter_upwards [hito] with ω hω
    have h := hω (Real.toNNReal t) (by rw [Real.coe_toNNReal _ ht])
    simp only [Real.coe_toNNReal _ ht, NNReal.coe_zero] at h
    have hD : ∫ s in Set.Icc (0 : ℝ) t, (fderiv ℝ g (Z (Real.toNNReal s : ℝ) ω) (B (Z (Real.toNNReal s : ℝ) ω)) +
        (1 / 2) * ∑ k, fderiv ℝ (fderiv ℝ g) (Z (Real.toNNReal s : ℝ) ω) (σ k) (σ k))
        = ∫ s in Set.Icc (0 : ℝ) t, (fderiv ℝ g (Z s ω) (B (Z s ω)) +
        (1 / 2) * ∑ k, fderiv ℝ (fderiv ℝ g) (Z s ω) (σ k) (σ k)) :=
      setIntegral_congr_fun measurableSet_Icc (fun s hs => by simp only [Real.coe_toNNReal _ hs.1])
    rw [hD] at h
    exact h

end HRS.MC.CepH2
