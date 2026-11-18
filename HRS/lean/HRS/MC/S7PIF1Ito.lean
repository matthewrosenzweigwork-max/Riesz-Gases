import HRS.Stochastic.EmpiricalIto

/-!
# Packet piF1: the empirical Itô formula (Lemma 3.6) for every `N ≥ 1`

`HRS.empirical_ito_of_contact` (Stochastic/EmpiricalIto.lean:1132) is stated for `2 ≤ N`, but `2 ≤ N` is used there
only to obtain `0 < N` (`omega`).  These are verbatim copies of `drift_pointwise`, `itoDrift_eq_rhs`, `empirical_ito_pos`,
`empirical_ito_of_contact` with the hypothesis `0 < N`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.Sec7.S7PIF1

open HRS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {d N : ℕ}

/-- The deterministic drift identity at a configuration `X` with lift `Y`. -/
theorem S7PIF1_drift_pointwise {D : DynData d} (hN : 0 < N) {t : ℝ} (ht : 0 < t) {f ft : ℝ → Torus d → ℝ}
    (hf : IsC12Test t f ft) {r : ℝ} (hr : r ∈ Set.Icc 0 t) (X : Config d N) (Y : Fin N → Euc d)
    (hY : ∀ i, Torus.mk (Y i) = X i) (hcol : X ∉ collisionSet d N ∨ D.M = 0) :
    derivWithin (fun r => empiricalLift N f r Y) (Set.Icc 0 t) r
      + fderiv ℝ (empiricalLift N f r) Y (fun i => particleDrift D X i)
      + (1 / 2 : ℝ) * ∑ k : Fin N × Fin d,
          fderiv ℝ (fderiv ℝ (empiricalLift N f r)) Y (liftedNoise D k) (liftedNoise D k)
    = pair (empirical X) (fun x => ft r x + D.invβ * Torus.laplacian (f r) x
          - inner ℝ (Torus.grad D.V x) (Torus.grad (f r) x))
      + interactionPairing D (f r) (empirical X) (empirical X) := by
  have hc2 : ContDiff ℝ 2 (Torus.lift (f r)) := hf.c2 r hr
  have hN0 : 0 < N := hN
  have hoff := offdiag_identity D (f r) hN0 X hcol
  rw [derivWithin_empiricalLift ht hf hr, empiricalLift_eq, fderiv_sumLift_lift_apply hc2,
    sum_fderiv_fderiv_sumLift_liftedNoise D hc2, pair_empirical hN0,
    interactionPairing_empirical hN0]
  simp only [sum_lap_eq, hY, particleDrift, inner_sub_right, inner_smul_right, inner_sum,
    real_inner_comm (Torus.grad D.V _)]
  have hsL : ∑ i, ((1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i,
        inner ℝ (Torus.grad (f r) (X i)) (Torus.matVec D.M (periodicRieszGrad d D.s (X i - X j)))
        - inner ℝ (Torus.grad D.V (X i)) (Torus.grad (f r) (X i)))
      = ∑ i, (1 / (N : ℝ)) * ∑ j ∈ Finset.univ.erase i,
          inner ℝ (Torus.grad (f r) (X i)) (Torus.matVec D.M (periodicRieszGrad d D.s (X i - X j)))
        - ∑ i, inner ℝ (Torus.grad D.V (X i)) (Torus.grad (f r) (X i)) := by
    rw [Finset.sum_sub_distrib]
  have hsR : ∑ x, (ft r (X x) + D.invβ * Torus.laplacian (f r) (X x)
        - inner ℝ (Torus.grad D.V (X x)) (Torus.grad (f r) (X x)))
      = ∑ x, ft r (X x) + D.invβ * ∑ x, Torus.laplacian (f r) (X x)
        - ∑ x, inner ℝ (Torus.grad D.V (X x)) (Torus.grad (f r) (X x)) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
  linear_combination hoff + (N : ℝ)⁻¹ * hsL - (N : ℝ)⁻¹ * hsR


section Covering

variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
  {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N} {D : DynData d}

/-- The deterministic drift identity in the form of Itô's formula. -/
theorem S7PIF1_itoDrift_eq_rhs {t : ℝ} (hN : 0 < N) (ht : 0 < t) {f ft : ℝ → Torus d → ℝ}
    (hf : IsC12Test t f ft) (Z : ℝ≥0 → Ω → (Fin N → Euc d)) (ω : Ω) {s : ℝ}
    (hs : s ∈ Set.Icc 0 t)
    (hY : ∀ i, Torus.mk (Z (Real.toNNReal s) ω i) = X (Real.toNNReal s) ω i)
    (hcol : X (Real.toNNReal s) ω ∉ collisionSet d N ∨ D.M = 0) :
    itoDrift t (empiricalLift N f) (ofNNRealTime Z) (ofNNRealTime (driftProc D X))
        (fun _ _ => liftedNoise D) s ω
      = pair (empirical (X (Real.toNNReal s) ω))
          (fun x => ft s x + D.invβ * Torus.laplacian (f s) x
            - inner ℝ (Torus.grad D.V x) (Torus.grad (f s) x))
        + interactionPairing D (f s) (empirical (X (Real.toNNReal s) ω))
            (empirical (X (Real.toNNReal s) ω)) := by
  unfold itoDrift
  exact S7PIF1_drift_pointwise hN ht hf hs (X (Real.toNNReal s) ω) (Z (Real.toNNReal s) ω) hY hcol


end Covering

section Assembly

variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
  {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
  {X : ℝ≥0 → Ω → Config d N} {D : DynData d}

/-- The empirical Itô identity for `0 < t` (Lemma 3.6, general contact-allowing form). -/
theorem S7PIF1_empirical_ito_pos {T : ℝ} {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Config d N} {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hN : 0 < N) (hV : Torus.IsCk 2 D.V)
    (hX : IsContactStrongSolution P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X)
    (hocc : D.M = 0 ∨ NullContactOccupation P T X)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) (ht0 : 0 < t) {f ft : ℝ → Torus d → ℝ}
    (hf : IsC12Test t f ft) :
    ∀ᵐ ω ∂P, ∀ τ ∈ Set.Icc 0 t,
      IntegrableOn (fun r => pair (empirical (X (Real.toNNReal r) ω))
          (fun x => ft r x + D.invβ * Torus.laplacian (f r) x
            - inner ℝ (Torus.grad D.V x) (Torus.grad (f r) x))
          + interactionPairing D (f r) (empirical (X (Real.toNNReal r) ω))
              (empirical (X (Real.toNNReal r) ω))) (Set.Icc 0 τ) ∧
      pair (empirical (X (Real.toNNReal τ) ω)) (f τ)
        = pair (empirical (X 0 ω)) (f 0)
          + (∫ r in (0:ℝ)..τ, (pair (empirical (X (Real.toNNReal r) ω))
              (fun x => ft r x + D.invβ * Torus.laplacian (f r) x
                - inner ℝ (Torus.grad D.V x) (Torus.grad (f r) x))
              + interactionPairing D (f r) (empirical (X (Real.toNNReal r) ω))
                  (empirical (X (Real.toNNReal r) ω))))
          + empiricalMartingale P ℱ W' D t f X (Real.toNNReal τ) ω := by
  obtain ⟨htL, htT⟩ := ht
  have hpos : 0 < N := hN
  have hTnn : 0 ≤ T := htL.trans htT
  have hI : ∀ᵐ ω ∂P, IntegrableOn (fun s : ℝ => driftProc D X (Real.toNNReal s) ω) (Set.Icc 0 T) :=
    hX.ae_integrableOn_drift hTnn le_rfl
  have hlift := hX.ae_lift_eq hF
  have hint : ∀ᵐ ω ∂P, ∀ τ : ℝ≥0, (τ : ℝ) ≤ T →
      intPart D X τ ω = ∫ s in Set.Icc 0 (τ : ℝ), driftProc D X (Real.toNNReal s) ω := by
    filter_upwards [hI] with ω hω τ hτ
    exact intPart_eq_integral ω τ (hω.mono_set (Set.Icc_subset_Icc le_rfl hτ))
  have hlift' : ∀ᵐ ω ∂P, ∀ τ : ℝ≥0, (τ : ℝ) ≤ T →
      X τ ω = fun i => Torus.mk (liftProcM D W' X τ ω i) := by
    filter_upwards [hlift, hint] with ω h1 h2 τ hτ
    rw [h1 τ hτ]
    funext i
    simp only [liftProcM, liftProc, h2 τ hτ]
  obtain ⟨N0, hN0m, hN0P, hN0⟩ := exists_null_of_ae (P := P) (p := fun ω => ∀ τ : ℝ≥0,
    (τ : ℝ) ≤ T → X τ ω = fun i => Torus.mk (liftProcM D W' X τ ω i)) hlift'
  have hZint : ∀ᵐ ω ∂P, ∀ τ : ℝ≥0, (τ : ℝ) ≤ t → liftProcM D W' X τ ω
      = liftProcM D W' X 0 ω + (∫ s in Set.Icc (0 : ℝ) τ, driftProc D X (Real.toNNReal s) ω)
        + ∑ k, (W' τ ω k - W' 0 ω k) • liftedNoise D k := by
    filter_upwards [hint] with ω hω τ hτ
    rw [liftProcM_zero ω]
    simp only [liftProcM]
    rw [hω τ (hτ.trans htT)]
  have hX₀ : ∀ s : ℝ, Measurable[ℱ s] (liftProcM D W' X 0) := by
    intro s
    have e : liftProcM D W' X 0 = fun ω => fun i => Torus.rep (X 0 ω i) :=
      funext fun ω => liftProcM_zero ω
    rw [e]
    have hg : Measurable (fun x : Config d N => fun i => Torus.rep (x i)) :=
      measurable_pi_iff.2 fun i => (measurable_torusRep d).comp (measurable_pi_apply i)
    exact hg.comp (hF.measurable_init s)
  have hbint : ∀ᵐ ω ∂P, IntegrableOn (fun s : ℝ => driftProc D X (Real.toNNReal s) ω)
      (Set.Icc 0 t) :=
    hI.mono fun ω hω => hω.mono_set (Set.Icc_subset_Icc le_rfl htT)
  have hito := ito_formula_additive (P := P) (ℱ := ℱ) hF.brownian (T := t) htL
    (empiricalLift N f) (isC12On_empiricalLift ht0 hf) (liftedNoise D) (liftProcM D W' X)
    (measurable_liftProcM hV hF) hX₀ (driftProc D X) (isProgressive_driftProc hV hF) hbint hZint
  have hΦ : IsProgressiveL2 P ℱ (empiricalNoiseIntegrand D t f X) :=
    isProgressiveL2_empiricalNoiseIntegrand (D := D) hF.progressive htL hf
  have hΨloc : IsProgressiveLocL2 P ℱ (empiricalNoiseIntegrand D t f X) := hΦ.locL2
  have hpt : ∀ s : ℝ, ∀ ω ∉ N0, itoIntegrand t Set.univ (empiricalLift N f)
      (ofNNRealTime (liftProcM D W' X)) (fun _ _ => liftedNoise D) s ω
        = empiricalNoiseIntegrand D t f X s ω := by
    intro s ω hω
    rw [empiricalNoiseIntegrand_eq_noiseG]
    by_cases hs : s ∈ Set.Icc 0 t
    · refine itoIntegrand_eq_noiseG hf (liftProcM D W' X) s ω ?_
      have hle : ((Real.toNNReal s : ℝ≥0) : ℝ) ≤ T := by
        rw [Real.coe_toNNReal _ hs.1]
        exact hs.2.trans htT
      intro i
      exact (congrFun (hN0 ω hω _ hle) i).symm
    · funext k
      rw [itoIntegrand_of_not_mem f hs]
      simp [noiseG, hs]
  have hcongr := localItoIntegral_congr_null hF.brownian hΨloc hN0m hN0P hpt
    (fun s hs ω => by
      funext k
      rw [itoIntegrand_of_not_mem f (fun h => absurd h.1 (not_le.2 hs))]
      rfl)
    (fun s hs ω => by
      funext k
      simp [empiricalNoiseIntegrand, not_le.2 hs])
  have hloc := localItoIntegral_eq_itoIntegral hF.brownian hΦ
  have hcol_ae : ∀ᵐ ω ∂P, ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.Icc 0 t →
      (X (Real.toNNReal s) ω ∉ collisionSet d N ∨ D.M = 0) := by
    rcases hocc with hM | hNull
    · exact Filter.Eventually.of_forall fun ω => Filter.Eventually.of_forall fun s _ => Or.inr hM
    · unfold NullContactOccupation at hNull
      filter_upwards [hNull] with ω hω
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 hω] with s hs hsI
      exact Or.inl fun hc => hs ⟨⟨hsI.1, hsI.2.trans htT⟩, hc⟩
  filter_upwards [hito, hloc, hcongr, hcol_ae, measure_eq_zero_iff_ae_notMem.1 hN0P]
    with ω hitoω hlocω hcongrω hcolω hωN0
  intro τ hτ
  obtain ⟨hτ0, hτt⟩ := hτ
  have hτc : ((Real.toNNReal τ : ℝ≥0) : ℝ) = τ := Real.coe_toNNReal τ hτ0
  have hYs : ∀ s ∈ Set.Icc 0 t, ∀ i, Torus.mk (liftProcM D W' X (Real.toNNReal s) ω i)
      = X (Real.toNNReal s) ω i := by
    intro s hs i
    have hle : ((Real.toNNReal s : ℝ≥0) : ℝ) ≤ T := by
      rw [Real.coe_toNNReal _ hs.1]
      exact hs.2.trans htT
    exact (congrFun (hN0 ω hωN0 _ hle) i).symm
  have hpt_ω : ∀ᵐ s ∂(volume : Measure ℝ), s ∈ Set.Icc 0 t →
      itoDrift t (empiricalLift N f) (ofNNRealTime (liftProcM D W' X))
        (ofNNRealTime (driftProc D X)) (fun _ _ => liftedNoise D) s ω
      = pair (empirical (X (Real.toNNReal s) ω))
          (fun x => ft s x + D.invβ * Torus.laplacian (f s) x
            - inner ℝ (Torus.grad D.V x) (Torus.grad (f s) x))
        + interactionPairing D (f s) (empirical (X (Real.toNNReal s) ω))
            (empirical (X (Real.toNNReal s) ω)) := by
    filter_upwards [hcolω] with s hs hsI
    exact S7PIF1_itoDrift_eq_rhs hN ht0 hf (liftProcM D W' X) ω hsI (hYs s hsI) (hs hsI)
  have hτle : ((Real.toNNReal τ : ℝ≥0) : ℝ) ≤ T := by
    rw [hτc]
    exact hτt.trans htT
  have hIntRHS : IntegrableOn (fun r => pair (empirical (X (Real.toNNReal r) ω))
      (fun x => ft r x + D.invβ * Torus.laplacian (f r) x
        - inner ℝ (Torus.grad D.V x) (Torus.grad (f r) x))
      + interactionPairing D (f r) (empirical (X (Real.toNNReal r) ω))
          (empirical (X (Real.toNNReal r) ω))) (Set.Icc 0 τ) := by
    have h1 := hitoω.1.mono_set (Set.Icc_subset_Icc le_rfl hτt)
    refine h1.congr_fun_ae ?_
    filter_upwards [ae_restrict_of_ae hpt_ω, ae_restrict_mem measurableSet_Icc] with s h1s hs
    exact h1s (Set.Icc_subset_Icc le_rfl hτt hs)
  have hτlet : ((Real.toNNReal τ : ℝ≥0) : ℝ) ≤ t := by
    rw [hτc]
    exact hτt
  have hidω := hitoω.2 (Real.toNNReal τ) hτlet
  rw [hτc] at hidω
  have hL : empiricalLift N f τ (liftProcM D W' X (Real.toNNReal τ) ω)
      = pair (empirical (X (Real.toNNReal τ) ω)) (f τ) :=
    empiricalLift_eq_pair hpos f τ _ _ (fun i => (congrFun (hN0 ω hωN0 _ hτle) i).symm)
  have hF0 : empiricalLift N f 0 (liftProcM D W' X 0 ω)
      = pair (empirical (X 0 ω)) (f 0) :=
    empiricalLift_eq_pair hpos f 0 _ _
      (fun i => (congrFun (hN0 ω hωN0 0 (by simpa using hTnn)) i).symm)
  have hIntEq : ∫ s in Set.Icc 0 (τ : ℝ), itoDrift t (empiricalLift N f)
      (ofNNRealTime (liftProcM D W' X)) (ofNNRealTime (driftProc D X))
      (fun _ _ => liftedNoise D) s ω
      = ∫ s in Set.Icc 0 τ, (pair (empirical (X (Real.toNNReal s) ω))
          (fun x => ft s x + D.invβ * Torus.laplacian (f s) x
            - inner ℝ (Torus.grad D.V x) (Torus.grad (f s) x))
          + interactionPairing D (f s) (empirical (X (Real.toNNReal s) ω))
              (empirical (X (Real.toNNReal s) ω))) :=
    setIntegral_congr_ae measurableSet_Icc
      (hpt_ω.mono fun s h hs => h (Set.Icc_subset_Icc le_rfl hτt hs))
  have hInt2 : ∫ s in Set.Icc 0 τ, (pair (empirical (X (Real.toNNReal s) ω))
          (fun x => ft s x + D.invβ * Torus.laplacian (f s) x
            - inner ℝ (Torus.grad D.V x) (Torus.grad (f s) x))
          + interactionPairing D (f s) (empirical (X (Real.toNNReal s) ω))
              (empirical (X (Real.toNNReal s) ω)))
      = ∫ r in (0:ℝ)..τ, (pair (empirical (X (Real.toNNReal r) ω))
          (fun x => ft r x + D.invβ * Torus.laplacian (f r) x
            - inner ℝ (Torus.grad D.V x) (Torus.grad (f r) x))
          + interactionPairing D (f r) (empirical (X (Real.toNNReal r) ω))
              (empirical (X (Real.toNNReal r) ω))) := by
    rw [intervalIntegral.integral_of_le hτ0, integral_Icc_eq_integral_Ioc]
  rw [hL, hF0, hIntEq, hInt2, hcongrω τ, hlocω τ] at hidω
  refine ⟨hIntRHS, ?_⟩
  unfold empiricalMartingale
  rw [hτc]
  exact hidω


end Assembly

/-- Lemma 3.6 for a contact-allowing flow (general form, with the integral parenthesised). -/
theorem S7PIF1_empirical_ito_of_contact {P : Measure Ω} {D : DynData d} {T : ℝ} {X₀ : Ω → Config d N}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N} {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} [IsProbabilityMeasure P]
    (hN : 0 < N) (hV : Torus.IsCk 2 D.V) (hX : IsContactStrongSolution P D T X₀ W X)
    (hF : IsFilteredSolution P ℱ W' W X) (hocc : D.M = 0 ∨ NullContactOccupation P T X)
    {t : ℝ} (ht : t ∈ Set.Icc 0 T) {f ft : ℝ → Torus d → ℝ} (hf : IsC12Test t f ft) :
    IsProgressiveL2 P ℱ (empiricalNoiseIntegrand D t f X) ∧
    ∀ᵐ ω ∂P, ∀ τ ∈ Set.Icc 0 t,
      IntegrableOn (fun r => pair (empirical (X (Real.toNNReal r) ω))
          (fun x => ft r x + D.invβ * Torus.laplacian (f r) x
            - inner ℝ (Torus.grad D.V x) (Torus.grad (f r) x))
          + interactionPairing D (f r) (empirical (X (Real.toNNReal r) ω))
              (empirical (X (Real.toNNReal r) ω))) (Set.Icc 0 τ) ∧
      pair (empirical (X (Real.toNNReal τ) ω)) (f τ)
        = pair (empirical (X 0 ω)) (f 0)
          + (∫ r in (0:ℝ)..τ, (pair (empirical (X (Real.toNNReal r) ω))
              (fun x => ft r x + D.invβ * Torus.laplacian (f r) x
                - inner ℝ (Torus.grad D.V x) (Torus.grad (f r) x))
              + interactionPairing D (f r) (empirical (X (Real.toNNReal r) ω))
                  (empirical (X (Real.toNNReal r) ω))))
          + empiricalMartingale P ℱ W' D t f X (Real.toNNReal τ) ω := by
  refine ⟨isProgressiveL2_empiricalNoiseIntegrand (D := D) hF.progressive ht.1 hf, ?_⟩
  rcases ht.1.eq_or_lt with h0 | hpos
  · subst h0
    filter_upwards with ω
    intro τ hτ
    have hτ0 : τ = 0 := le_antisymm hτ.2 hτ.1
    subst hτ0
    have hle : ((Real.toNNReal 0 : ℝ≥0) : ℝ) ≤ 0 := by simp
    have hM : empiricalMartingale P ℱ W' D 0 f X (Real.toNNReal 0) ω = 0 := by
      unfold empiricalMartingale
      exact itoIntegral_of_nonpos P ℱ W' _ hle ω
    refine ⟨?_, ?_⟩
    · rw [Set.Icc_self]
      exact (integrableOn_singleton_iff enorm_ne_top).2 (Or.inr (by simp))
    · rw [intervalIntegral.integral_same, hM]
      simp
  · exact S7PIF1_empirical_ito_pos hN hV hX hF hocc ht hpos hf

end HRS.MC.Sec7.S7PIF1

end
