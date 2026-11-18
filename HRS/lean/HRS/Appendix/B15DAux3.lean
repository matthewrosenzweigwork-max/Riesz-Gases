import HRS.Appendix.B15DAux2

/-!
# Packet D2 (proofs, part 3): Itô duality along the regularised solution

Relocated proofs of `d1_ito_pathwise` (Dynkin form with integrable mean-zero remainder).  The frozen
sorried statement lives in `HRS/Appendix/B15DAux1.lean`; this file restates it verbatim as
`d1_ito_pathwise_proof`.  Helpers are prefixed `b15d2_`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS

section D2proofs3

variable {d N : ℕ}

/-- A function continuous on every `[0,u]` is continuous on `[0,∞)`. -/
theorem b15d2_contOn_Ici {E : Type*} [TopologicalSpace E] {g : ℝ → E}
    (h : ∀ u : ℝ, 0 ≤ u → ContinuousOn g (Set.Icc 0 u)) : ContinuousOn g (Set.Ici 0) := by
  intro x hx
  have hx' : (0 : ℝ) ≤ x := hx
  have hmem : Set.Icc 0 (x + 1) ∈ 𝓝[Set.Ici 0] x :=
    mem_nhdsWithin.2 ⟨Set.Iio (x + 1), isOpen_Iio, show x ∈ Set.Iio (x + 1) by simp,
      fun y hy => ⟨hy.2, le_of_lt hy.1⟩⟩
  exact ((h (x + 1) (by linarith)) x ⟨hx', by linarith⟩).mono_of_mem_nhdsWithin hmem

/-- Progressivity of the path `s ↦ Y (max s 0)` of an adapted process with continuous paths on `[0,∞)`,
where `Y 0` is `ℱ_s`-measurable for every `s` (the negative times are frozen at `0`). -/
theorem b15d2_isProgressive_clampPath {Ω : Type*} [mΩ : MeasurableSpace Ω] {ℱ : Filtration ℝ mΩ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {Y : ℝ → Ω → E} (hY₀ : ∀ t : ℝ, Measurable[ℱ t] (Y 0))
    (had : ∀ t : ℝ, 0 ≤ t → Measurable[ℱ t] (Y t)) (hc : ∀ ω, ContinuousOn (fun s => Y s ω) (Set.Ici 0)) :
    IsProgressive ℱ (fun s ω => Y (max s 0) ω) := by
  have hZad : ∀ t : ℝ, Measurable[ℱ t] (fun ω => Y (max t 0) ω) := by
    intro t
    rcases le_total 0 t with h | h
    · rw [max_eq_left h]
      exact had t h
    · rw [max_eq_right h]
      exact hY₀ t
  have hZc : ∀ ω, Continuous fun s => Y (max s 0) ω := fun ω =>
    (hc ω).comp_continuous (continuous_id.max continuous_const)
      (fun s => show (0 : ℝ) ≤ max s 0 from le_max_right _ _)
  exact (StronglyAdapted.isStronglyProgressive_of_continuous
    (fun t => (hZad t).stronglyMeasurable) hZc).isProgressive

/-- Itô formula along the regularised solution, Dynkin form (see the frozen statement's docstring). -/
theorem d1_ito_pathwise_proof {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hW' : IsBrownianFiltration P ℱ W') {κ : ℝ} (hκ : 0 ≤ κ) {bC : Config d N → Fin N → Euc d}
    (hbC : Continuous (d1_liftDrift bC)) {Y₀ : Ω → Fin N → Euc d}
    (hY₀ : ∀ t : ℝ, Measurable[ℱ t] Y₀) {Y : ℝ → Ω → Fin N → Euc d}
    (hY : IsAdditiveSDESolution P ℱ W' (fun _ => d1_liftDrift bC) (d1_noise d N κ) Y₀
      (fun _ => ⊤) Y)
    {T : ℝ} (hT : 0 ≤ T) {f : ℝ → (Fin N → Euc d) → ℝ} (hf : IsC12On T Set.univ f)
    (hbd : ∃ C : ℝ, ∀ s ∈ Set.Icc 0 T, ∀ y, |f s y| ≤ C ∧ ‖fderiv ℝ (f s) y‖ ≤ C ∧
      ‖fderiv ℝ (fderiv ℝ (f s)) y‖ ≤ C ∧ |derivWithin (fun r => f r y) (Set.Icc 0 T) s| ≤ C) :
    ∀ t ∈ Set.Icc 0 T, ∃ M : Ω → ℝ, Integrable M P ∧ ∫ ω, M ω ∂P = 0 ∧
      ∀ᵐ ω ∂P, f t (Y t ω) = f 0 (Y 0 ω) +
        (∫ s in Set.Icc (0 : ℝ) t, d1_itoGen κ bC T f s (Y s ω)) + M ω := by
  intro t ht
  obtain ⟨C, hC⟩ := hbd
  have hYc : ∀ ω, ∀ u : ℝ, 0 ≤ u → ContinuousOn (fun s => Y s ω) (Set.Icc 0 u) := fun ω u hu =>
    hY.cont ω u hu (WithTop.coe_lt_top _)
  have hYcI : ∀ ω, ContinuousOn (fun s => Y s ω) (Set.Ici 0) := fun ω =>
    b15d2_contOn_Ici (fun u hu => hYc ω u hu)
  have hY0 : Y 0 = Y₀ := funext hY.init
  have hY0' : ∀ s : ℝ, Measurable[ℱ s] (Y 0) := fun s => by rw [hY0]; exact hY₀ s
  have hYad : ∀ u : ℝ, 0 ≤ u → Measurable[ℱ u] (Y u) := fun u _ => hY.adapted u
  -- the path and the drift are progressive
  have hXprog : IsProgressive ℱ (ofNNRealTime (fun u : ℝ≥0 => Y (u : ℝ))) := by
    have e : ofNNRealTime (fun u : ℝ≥0 => Y (u : ℝ)) = fun s ω => Y (max s 0) ω := by
      funext s ω
      simp [ofNNRealTime, Real.coe_toNNReal']
    rw [e]
    exact b15d2_isProgressive_clampPath hY0' hYad hYcI
  have hbprog : IsProgressive ℱ
      (ofNNRealTime (fun (u : ℝ≥0) (ω : Ω) => d1_liftDrift bC (Y (u : ℝ) ω))) :=
    isProgressive_comp_measurable' (ofNNRealTime (fun u : ℝ≥0 => Y (u : ℝ))) hXprog
      (fun _ y => d1_liftDrift bC y) (hbC.comp continuous_snd).measurable
  -- the Itô integrand: progressive and bounded
  have hclampD : Continuous (fun q : ℝ × (Fin N → Euc d) => fderiv ℝ (f (clampTI T q.1)) q.2) := by
    have hq : Continuous (fun q : ℝ × (Fin N → Euc d) => (clampTI T q.1, q.2)) :=
      ((continuous_clampTI T).comp continuous_fst).prodMk continuous_snd
    exact ContinuousOn.comp_continuous hf.cont_fderiv hq
      (fun q => ⟨clampTI_mem hT q.1, mem_univ _⟩)
  let g : ℝ → (Fin N → Euc d) → (Fin N × Fin d) → ℝ := fun s y k =>
    if s ∈ Set.Icc 0 T then fderiv ℝ (f (clampTI T s)) y (d1_noise d N κ k) else 0
  have hΨeq : ∀ s ω k, itoIntegrand T Set.univ f (ofNNRealTime (fun u : ℝ≥0 => Y (u : ℝ)))
      (fun _ _ => d1_noise d N κ) s ω k = g s (ofNNRealTime (fun u : ℝ≥0 => Y (u : ℝ)) s ω) k := by
    intro s ω k
    by_cases hs : s ∈ Set.Icc 0 T
    · simp only [itoIntegrand, g, if_pos hs, Set.indicator_of_mem hs, Set.mem_univ, Set.setOf_true,
        Set.indicator_univ, clampTI_of_mem hs, ofNNRealTime_apply]
    · simp only [itoIntegrand, g, if_neg hs, Set.indicator_of_notMem hs]
  have hΨprog : IsProgressive ℱ (fun s ω k => itoIntegrand T Set.univ f
      (ofNNRealTime (fun u : ℝ≥0 => Y (u : ℝ))) (fun _ _ => d1_noise d N κ) s ω k) := by
    have hk : ∀ k : Fin N × Fin d, IsProgressive ℱ (fun s ω =>
        itoIntegrand T Set.univ f (ofNNRealTime (fun u : ℝ≥0 => Y (u : ℝ)))
          (fun _ _ => d1_noise d N κ) s ω k) := by
      intro k
      have hc := hclampD.clm_apply (continuous_const (y := d1_noise d N κ k))
      have hm : Measurable (Function.uncurry (fun (s : ℝ) (y : Fin N → Euc d) =>
          if s ∈ Set.Icc 0 T then fderiv ℝ (f (clampTI T s)) y (d1_noise d N κ k) else 0)) :=
        Measurable.ite (measurableSet_Icc.preimage measurable_fst) hc.measurable measurable_const
      have hg := isProgressive_comp_measurable' (ofNNRealTime (fun u : ℝ≥0 => Y (u : ℝ))) hXprog
        (fun (s : ℝ) (y : Fin N → Euc d) =>
          if s ∈ Set.Icc 0 T then fderiv ℝ (f (clampTI T s)) y (d1_noise d N κ k) else 0) hm
      have e : (fun s ω => itoIntegrand T Set.univ f (ofNNRealTime (fun u : ℝ≥0 => Y (u : ℝ)))
          (fun _ _ => d1_noise d N κ) s ω k)
          = fun s ω => (fun (s : ℝ) (y : Fin N → Euc d) =>
            if s ∈ Set.Icc 0 T then fderiv ℝ (f (clampTI T s)) y (d1_noise d N κ k) else 0)
              s (ofNNRealTime (fun u : ℝ≥0 => Y (u : ℝ)) s ω) := by
        funext s ω
        exact hΨeq s ω k
      rw [e]
      exact hg
    exact isProgressive_pi hk
  have hΨbd : ∀ s ω k, |itoIntegrand T Set.univ f (ofNNRealTime (fun u : ℝ≥0 => Y (u : ℝ)))
      (fun _ _ => d1_noise d N κ) s ω k| ≤ max C 0 * ∑ j : Fin N × Fin d, ‖d1_noise d N κ j‖ := by
    intro s ω k
    rw [hΨeq s ω k]
    simp only [g]
    split_ifs with hs
    · have hb : ‖fderiv ℝ (f (clampTI T s)) (ofNNRealTime (fun u : ℝ≥0 => Y (u : ℝ)) s ω)‖ ≤ max C 0 :=
        ((hC (clampTI T s) (clampTI_mem hT s) _).2.1).trans (le_max_left _ _)
      calc |fderiv ℝ (f (clampTI T s)) (ofNNRealTime (fun u : ℝ≥0 => Y (u : ℝ)) s ω) (d1_noise d N κ k)|
          ≤ ‖fderiv ℝ (f (clampTI T s)) (ofNNRealTime (fun u : ℝ≥0 => Y (u : ℝ)) s ω)‖
              * ‖d1_noise d N κ k‖ := by
            rw [← Real.norm_eq_abs]
            exact ContinuousLinearMap.le_opNorm _ _
        _ ≤ max C 0 * ‖d1_noise d N κ k‖ :=
            mul_le_mul hb le_rfl (norm_nonneg _) ((norm_nonneg _).trans hb)
        _ ≤ max C 0 * ∑ j : Fin N × Fin d, ‖d1_noise d N κ j‖ :=
            mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun j _ => norm_nonneg _)
              (Finset.mem_univ k)) (le_max_right _ _)
    · simp only [abs_zero]
      exact mul_nonneg (le_max_right _ _) (Finset.sum_nonneg fun j _ => norm_nonneg _)
  have hΨL2 : IsProgressiveL2 P ℱ (fun s ω k => itoIntegrand T Set.univ f
      (ofNNRealTime (fun u : ℝ≥0 => Y (u : ℝ))) (fun _ _ => d1_noise d N κ) s ω k) :=
    IsProgressiveL2.of_bounded P hΨprog _ hΨbd
  -- the Itô formula
  have hXmeas : ∀ u : ℝ≥0, Measurable (fun ω => Y (u : ℝ) ω) := fun u =>
    (hY.adapted (u : ℝ)).mono (ℱ.le _) le_rfl
  have hX0 : ∀ ω, Y ((0 : ℝ≥0) : ℝ) ω = Y₀ ω := fun ω => by
    rw [NNReal.coe_zero]
    exact congrFun hY0 ω
  have hX₀ : ∀ s : ℝ, Measurable[ℱ s] (fun ω => Y ((0 : ℝ≥0) : ℝ) ω) := fun s => by
    have e : (fun ω => Y ((0 : ℝ≥0) : ℝ) ω) = Y₀ := funext hX0
    rw [e]
    exact hY₀ s
  have hbint : ∀ᵐ ω ∂P, IntegrableOn (fun s : ℝ => d1_liftDrift bC (Y (Real.toNNReal s : ℝ) ω))
      (Set.Icc 0 T) := by
    filter_upwards [hY.eq] with ω hω
    have h := (hω T hT (WithTop.coe_lt_top _)).1
    refine h.congr_fun (fun s hs => ?_) measurableSet_Icc
    rw [Real.coe_toNNReal _ hs.1]
  have hX : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, (u : ℝ) ≤ T →
      Y (u : ℝ) ω = Y ((0 : ℝ≥0) : ℝ) ω
        + (∫ s in Set.Icc (0 : ℝ) (u : ℝ), d1_liftDrift bC (Y (Real.toNNReal s : ℝ) ω))
        + ∑ k, (W' u ω k - W' 0 ω k) • d1_noise d N κ k := by
    filter_upwards [hY.eq] with ω hω u hu
    have h := hω (u : ℝ) u.2 (WithTop.coe_lt_top _)
    have hint : ∫ s in Set.Icc (0 : ℝ) (u : ℝ), d1_liftDrift bC (Y s ω)
        = ∫ s in Set.Icc (0 : ℝ) (u : ℝ), d1_liftDrift bC (Y (Real.toNNReal s : ℝ) ω) :=
      setIntegral_congr_fun measurableSet_Icc (fun s hs => by
        rw [Real.coe_toNNReal _ hs.1])
    have h2 : Y (u : ℝ) ω = Y₀ ω + (∫ s in Set.Icc (0 : ℝ) (u : ℝ), d1_liftDrift bC (Y s ω))
        + ∑ k, ofNNRealTime W' (u : ℝ) ω k • d1_noise d N κ k := h.2
    rw [h2, hX0 ω, hint]
    simp [ofNNRealTime, hW'.zero]
  have hito := ito_formula_additive (P := P) (ℱ := ℱ) hW' (T := T) hT f hf (d1_noise d N κ)
    (fun (u : ℝ≥0) (ω : Ω) => Y (u : ℝ) ω) hXmeas hX₀
    (fun (u : ℝ≥0) (ω : Ω) => d1_liftDrift bC (Y (u : ℝ) ω)) hbprog hbint hX
  have hloc := localItoIntegral_eq_itoIntegral hW' hΨL2
  refine ⟨fun ω => localItoIntegral P ℱ W' (itoIntegrand T Set.univ f
      (ofNNRealTime (fun u : ℝ≥0 => Y (u : ℝ))) (fun _ _ => d1_noise d N κ)) t ω, ?_, ?_, ?_⟩
  · refine (memLp_two_itoIntegral hW' hΨL2 t).integrable one_le_two |>.congr ?_
    filter_upwards [hloc] with ω hω
    exact (hω t).symm
  · rw [integral_congr_ae (by filter_upwards [hloc] with ω hω using hω t)]
    exact integral_itoIntegral hW' hΨL2 t
  · filter_upwards [hito] with ω hω
    have h := hω.2 (Real.toNNReal t) (by rw [Real.coe_toNNReal _ ht.1]; exact ht.2)
    simp only [Real.coe_toNNReal _ ht.1, NNReal.coe_zero] at h
    have hD : ∫ s in Set.Icc (0 : ℝ) t, itoDrift T f
        (ofNNRealTime (fun u : ℝ≥0 => Y (u : ℝ))) (ofNNRealTime (fun (u : ℝ≥0) (ω : Ω) =>
          d1_liftDrift bC (Y (u : ℝ) ω))) (fun _ _ => d1_noise d N κ) s ω
        = ∫ s in Set.Icc (0 : ℝ) t, d1_itoGen κ bC T f s (Y s ω) :=
      setIntegral_congr_fun measurableSet_Icc (fun s hs => by
        simp only [itoDrift, d1_itoGen, ofNNRealTime_apply, Real.coe_toNNReal _ hs.1])
    rw [hD] at h
    exact h

example := (@d1_ito_pathwise_proof : type_of% @d1_ito_pathwise)

end D2proofs3

end HRS
