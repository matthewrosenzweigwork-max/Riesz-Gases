import HRS.MS.R26T8AO06c

/-!
# S8.2 T8A O06 (part d): Itô's formula for `C^{1,2}` functions on the collision-free set (additive noise)
For a strong solution of the particle system with a.s. collision-free continuous paths on `[0,T]`, and
`f ∈ C^{1,2}([0,T] × U)`, `U = (eucCollisionSet d N)ᶜ`: a.s. for all `t ≤ T`,
`f t (X t) = f 0 (X 0) + ∫_0^t itoDrift + itoIntegral Φ t`, with `Φ = itoIntegrand T U f X σ` assumed progressive `L²`.
Proof: localise with exit times from the exhaustion `V m`, apply `ito_formula_localized` on `K m`, identify the
stopped local integral with the stopped Itô integral, and let `m → ∞` pathwise.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

open Classical in
theorem r26t8a_o06_itoIntegrand_apply {d N : ℕ} {Omega : Type*} (T : ℝ) (K : Set (EucConfig d N))
    (f : ℝ → EucConfig d N → ℝ) (X : ℝ → Omega → EucConfig d N) (Φ : ℝ → Omega → Fin N × Fin d → EucConfig d N)
    (s : ℝ) (w : Omega) (k : Fin N × Fin d) :
    itoIntegrand T K f X Φ s w k =
      if s ∈ Set.Icc 0 T ∧ X s w ∈ K then fderiv ℝ (f s) (X s w) (Φ s w k) else 0 := by
  classical
  unfold itoIntegrand
  by_cases hs : s ∈ Set.Icc 0 T <;> by_cases hK : X s w ∈ K <;> simp [Set.indicator, hs, hK]

open Classical in
theorem r26t8a_o06_stop_apply {Omega : Type*} {ι : Type*} (Φ : ℝ → Omega → ι → ℝ) (τ : Omega → WithTop ℝ)
    (s : ℝ) (w : Omega) :
    stopIntegrand Φ τ s w = if (s : WithTop ℝ) ≤ τ w then Φ s w else 0 := by
  classical
  unfold stopIntegrand
  by_cases h : (s : WithTop ℝ) ≤ τ w <;> simp [Set.indicator, h]

set_option maxHeartbeats 12800000 in
theorem r26t8a_o06_ito_coll {d N : ℕ} {Omega : Type*} [mOmega : MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P] {ℱ : Filtration ℝ mOmega}
    {W : ℝ≥0 → Omega → Fin N × Fin d → ℝ} (hW : IsBrownianFiltration P ℱ W) {T : ℝ} (hT : 0 ≤ T)
    (f : ℝ → EucConfig d N → ℝ) (hf : IsC12On T (eucCollisionSet d N)ᶜ f) (σ : Fin N × Fin d → EucConfig d N)
    (X : ℝ≥0 → Omega → EucConfig d N) (hXmeas : ∀ t, Measurable (X t))
    (hX₀ : ∀ t : ℝ, Measurable[ℱ t] (X 0)) (b : ℝ≥0 → Omega → EucConfig d N)
    (hb : IsProgressive ℱ (ofNNRealTime b))
    (hbint : ∀ᵐ w ∂P, IntegrableOn (fun s : ℝ => b (Real.toNNReal s) w) (Set.Icc 0 T))
    (hX : ∀ᵐ w ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      X t w = X 0 w + (∫ s in Set.Icc (0 : ℝ) t, b (Real.toNNReal s) w) +
        ∑ k, (W t w k - W 0 w k) • σ k)
    (hXU : ∀ᵐ w ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t w ∉ eucCollisionSet d N)
    (hΦ : IsProgressiveL2 P ℱ
      (itoIntegrand T (eucCollisionSet d N)ᶜ f (ofNNRealTime X) (fun _ _ => σ))) :
    ∀ᵐ w ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T,
      IntegrableOn (fun s => itoDrift T f (ofNNRealTime X) (ofNNRealTime b) (fun _ _ => σ) s w)
        (Set.Icc 0 t) ∧
      f t (X t.toNNReal w) = f 0 (X 0 w) +
        (∫ s in Set.Icc 0 t, itoDrift T f (ofNNRealTime X) (ofNNRealTime b) (fun _ _ => σ) s w) +
        itoIntegral P ℱ W (itoIntegrand T (eucCollisionSet d N)ᶜ f (ofNNRealTime X) (fun _ _ => σ)) t w := by
  classical
  set U : Set (EucConfig d N) := (eucCollisionSet d N)ᶜ with hU
  have hUo : IsOpen U := r26t8a_o03b_coll_closed.isOpen_compl
  set Φ : ℝ → Omega → Fin N × Fin d → ℝ := itoIntegrand T U f (ofNNRealTime X) (fun _ _ => σ) with hΦdef
  -- the drift process and the Itô process
  let b' : ℝ → Omega → EucConfig d N := fun s w => if s ≤ T then b (Real.toNNReal s) w else 0
  have hb'prog : IsProgressive ℱ b' := by
    intro i
    letI : MeasurableSpace (Set.Iic i × Omega) := Subtype.instMeasurableSpace.prod (ℱ i)
    have h1 := hb i
    have hs : MeasurableSet {p : Set.Iic i × Omega | (p.1 : ℝ) ≤ T} :=
      (measurable_subtype_coe.comp measurable_fst) measurableSet_Iic
    exact Measurable.ite hs h1 measurable_const
  have hb'int : ∀ T' : ℝ, ∀ᵐ w ∂P, IntegrableOn (fun s => b' s w) (Set.Icc 0 T') := by
    intro T'
    filter_upwards [hbint] with w hw
    have e : (fun s => b' s w) = Set.indicator (Set.Iic T) (fun s => b (Real.toNNReal s) w) := by
      funext s; simp [b', Set.indicator]
    rw [e, IntegrableOn, integrable_indicator_iff measurableSet_Iic, IntegrableOn,
      Measure.restrict_restrict measurableSet_Iic]
    refine hw.mono_set ?_
    intro s hs
    exact ⟨hs.2.1, hs.1⟩
  have hb' : IsProgressiveLocL1 P ℱ b' := ⟨hb'prog, hb'int⟩
  have hΦ0 : IsProgressiveLocL2E P ℱ (fun (_ : ℝ) (_ : Omega) => σ) := by
    refine ⟨isProgressive_const ℱ σ, fun T => ae_of_all _ fun w => ?_⟩
    rw [lintegral_const]
    exact ENNReal.mul_lt_top (by simp) (by simp)
  set Z : ℝ → Omega → EucConfig d N := itoProcess P ℱ W (X 0) b' (fun _ _ => σ) with hZ
  have hXt : ∀ᵐ w ∂P, ∀ s ∈ Set.Icc (0 : ℝ) T, ofNNRealTime X s w = Z s w := by
    filter_upwards [hX, localItoIntegralE_const hW σ] with w h1 h2 s hs
    have h3 := h1 (Real.toNNReal s) (by rw [Real.coe_toNNReal _ hs.1]; exact hs.2)
    have h4 : (∫ r in Set.Icc (0 : ℝ) (Real.toNNReal s : ℝ), b (Real.toNNReal r) w) =
        ∫ r in Set.Icc (0 : ℝ) s, b' r w := by
      rw [Real.coe_toNNReal _ hs.1]
      refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
      simp [b', hr.2.trans hs.2]
    simp only [ofNNRealTime_apply, hZ, itoProcess]
    rw [h3, h4, h2 s, hW.zero]
    simp
  -- a null set off which everything is good
  have hZc : ∀ᵐ w ∂P, Continuous fun t => Z t w := continuous_itoProcess (X 0) b' hb' (fun _ _ => σ)
  obtain ⟨N0, hN0m, hN00, hN0⟩ : ∃ N0 : Set Omega, MeasurableSet N0 ∧ P N0 = 0 ∧ ∀ w ∉ N0,
      (∀ s ∈ Set.Icc (0 : ℝ) T, ofNNRealTime X s w = Z s w) ∧ Continuous (fun t => Z t w) ∧
      (∀ t : ℝ≥0, (t : ℝ) ≤ T → X t w ∉ eucCollisionSet d N) := by
    have h : ∀ᵐ w ∂P, (∀ s ∈ Set.Icc (0 : ℝ) T, ofNNRealTime X s w = Z s w) ∧ Continuous (fun t => Z t w) ∧
        (∀ t : ℝ≥0, (t : ℝ) ≤ T → X t w ∉ eucCollisionSet d N) := by
      filter_upwards [hXt, hZc, hXU] with w a b c using ⟨a, b, c⟩
    refine ⟨toMeasurable P {w | ¬ ((∀ s ∈ Set.Icc (0 : ℝ) T, ofNNRealTime X s w = Z s w) ∧
      Continuous (fun t => Z t w) ∧ (∀ t : ℝ≥0, (t : ℝ) ≤ T → X t w ∉ eucCollisionSet d N))},
      measurableSet_toMeasurable _ _, ?_, ?_⟩
    · rw [measure_toMeasurable]; exact ae_iff.1 h
    · intro w hw; by_contra hc; exact hw (subset_toMeasurable _ _ hc)
  have hN0F : ∀ i, MeasurableSet[ℱ i] N0ᶜ := fun i =>
    @MeasurableSet.compl _ _ (ℱ i) (hW.complete i N0 hN0m hN00)
  -- the everywhere continuous modification
  let Y : ℝ → Omega → EucConfig d N := fun t w => if w ∈ N0 then 0 else Z (min t T) w
  have hYc : ∀ w, Continuous fun t => Y t w := by
    intro w
    by_cases hw : w ∈ N0
    · simp only [Y, hw, if_true]; exact continuous_const
    · simp only [Y, hw, if_false]
      exact (hN0 w hw).2.1.comp (continuous_id.min continuous_const)
  have hZad : Adapted ℱ Z := adapted_itoProcess (X 0) hX₀ b' hb'prog _
  have hYad : Adapted ℱ Y := by
    intro t
    have h1 : Measurable[ℱ t] (fun w => Z (min t T) w) :=
      (hZad (min t T)).mono (ℱ.mono (min_le_left t T)) le_rfl
    have hN : MeasurableSet[ℱ t] N0 := hW.complete t N0 hN0m hN00
    have hc : Measurable[ℱ t] (fun _ : Omega => (0 : EucConfig d N)) := by
      letI : MeasurableSpace Omega := ℱ t
      exact measurable_const
    exact Measurable.ite hN hc h1
  have hYZ : ∀ w ∉ N0, ∀ t ∈ Set.Icc (0 : ℝ) T, Y t w = Z t w := fun w hw t ht => by
    simp only [Y, hw, if_false, min_eq_left ht.2]
  -- the localisation events and stopping times
  let A : ℕ → Set Omega := fun m => N0ᶜ ∩ {w | X 0 w ∈ r26t8a_o06_V d N m}
  have hAF : ∀ m i, MeasurableSet[ℱ i] (A m) := fun m i =>
    @MeasurableSet.inter _ (ℱ i) _ _ (hN0F i)
      ((r26t8a_o06_V_open (d := d) (N := N) m).measurableSet.preimage (hX₀ i))
  let τ : ℕ → Omega → WithTop ℝ := fun m => r26t8a_o06_tau Y (r26t8a_o06_V d N m) (A m)
  have hτ : ∀ m, IsStoppingTime ℱ (τ m) := fun m =>
    r26t8a_o06_tau_stopping ℱ Y hYad hYc (r26t8a_o06_V_open m) (hAF m)
  have hY0 : ∀ w ∉ N0, Y 0 w = X 0 w := fun w hw => by
    rw [hYZ w hw 0 ⟨le_rfl, hT⟩]
    have := (hN0 w hw).1 0 ⟨le_rfl, hT⟩
    simpa using this.symm
  have hZK : ∀ m, ∀ w ∉ N0, ∀ t ∈ Set.Icc (0 : ℝ) T, (t : WithTop ℝ) ≤ τ m w → Z t w ∈ r26t8a_o06_K d N m := by
    intro m w hw t ht hle
    have hwA : w ∈ A m := by
      by_contra hc
      exact r26t8a_o06_tau_neg Y (r26t8a_o06_V d N m) hc ht.1 hle
    have h0 : Y 0 w ∈ r26t8a_o06_V d N m := by rw [hY0 w hw]; exact hwA.2
    have hcl := r26t8a_o06_tau_mem Y (r26t8a_o06_V_open m) hwA h0 (hYc w) ht.1 hle
    rw [hYZ w hw t ht] at hcl
    exact closure_minimal (r26t8a_o06_V_sub_K m) (r26t8a_o06_K_compact m).isClosed hcl
  -- Itô's formula up to each `τ m`
  have hmain : ∀ m : ℕ, ∀ᵐ w ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, (t : WithTop ℝ) ≤ τ m w →
      IntegrableOn (fun s => itoDrift T f Z b' (fun _ _ => σ) s w) (Set.Icc 0 t) ∧
      f t (Z t w) = f 0 (X 0 w) + (∫ s in Set.Icc 0 t, itoDrift T f Z b' (fun _ _ => σ) s w) +
        localItoIntegral P ℱ W (stopIntegrand (itoIntegrand T (r26t8a_o06_K d N m) f Z (fun _ _ => σ)) (τ m)) t w := by
    intro m
    have := ito_formula_localized hW hT U hUo (r26t8a_o06_K d N m) (r26t8a_o06_K_compact m)
      (r26t8a_o06_K_sub m) f hf (X 0) hX₀ b' hb' (fun _ _ => σ) hΦ0 (τ m) (hτ m)
      (by filter_upwards [measure_eq_zero_iff_ae_notMem.1 hN00] with w hw t ht hle
          exact hZK m w hw t ht hle)
    exact this
  -- identification of the stopped local integrals with the stopped Itô integral
  have hΦτ : ∀ m, IsProgressiveL2 P ℱ (stopIntegrand Φ (τ m)) := fun m => hΦ.stopIntegrand (hτ m)
  have hcong : ∀ m, ∀ᵐ w ∂P, ∀ t,
      localItoIntegral P ℱ W (stopIntegrand (itoIntegrand T (r26t8a_o06_K d N m) f Z (fun _ _ => σ)) (τ m)) t w =
        localItoIntegral P ℱ W (stopIntegrand Φ (τ m)) t w := by
    intro m
    refine localItoIntegral_congr_null hW (hΦτ m).locL2 hN0m hN00 ?_ ?_ ?_
    · intro s w hw
      rw [r26t8a_o06_stop_apply, r26t8a_o06_stop_apply]
      by_cases hle : (s : WithTop ℝ) ≤ τ m w
      · simp only [hle, if_true]
        funext k
        rw [hΦdef, r26t8a_o06_itoIntegrand_apply, r26t8a_o06_itoIntegrand_apply]
        by_cases hs : s ∈ Set.Icc (0 : ℝ) T
        · have hK := hZK m w hw s hs hle
          have hXZ := (hN0 w hw).1 s hs
          have hKU : ofNNRealTime X s w ∈ U := by
            rw [hXZ]; exact r26t8a_o06_K_sub m hK
          rw [if_pos ⟨hs, hK⟩, if_pos ⟨hs, hKU⟩, hXZ]
        · rw [if_neg (fun h => hs h.1), if_neg (fun h => hs h.1)]
      · simp only [hle, if_false]
    · intro s hs w
      rw [r26t8a_o06_stop_apply]
      split_ifs
      · funext k
        have hs' : s ∉ Set.Icc (0 : ℝ) T := fun h => absurd h.1 (not_le.2 hs)
        rw [r26t8a_o06_itoIntegrand_apply, if_neg (fun h => hs' h.1)]
        rfl
      · rfl
    · intro s hs w
      rw [r26t8a_o06_stop_apply]
      split_ifs
      · funext k
        have hs' : s ∉ Set.Icc (0 : ℝ) T := fun h => absurd h.1 (not_le.2 hs)
        rw [hΦdef, r26t8a_o06_itoIntegrand_apply, if_neg (fun h => hs' h.1)]
        rfl
      · rfl
  have hloc : ∀ m, ∀ᵐ w ∂P, ∀ t, localItoIntegral P ℱ W (stopIntegrand Φ (τ m)) t w =
      itoIntegral P ℱ W (stopIntegrand Φ (τ m)) t w := fun m => localItoIntegral_eq_itoIntegral hW (hΦτ m)
  have hst : ∀ m, ∀ᵐ w ∂P, ∀ t, stoppedProcess (itoIntegral P ℱ W Φ) (τ m) t w =
      itoIntegral P ℱ W (stopIntegrand Φ (τ m)) t w := fun m =>
    (isLocalItoIntegral_itoIntegral hW hΦ).stopped (τ m) (hτ m) (hΦτ m)
  filter_upwards [ae_all_iff.2 hmain, ae_all_iff.2 hcong, ae_all_iff.2 hloc, ae_all_iff.2 hst,
    measure_eq_zero_iff_ae_notMem.1 hN00] with w h1 h2 h3 h4 hw
  have hC : IsCompact ((fun t => Y t w) '' Set.Icc (0 : ℝ) T) := isCompact_Icc.image (hYc w)
  have hCU : (fun t => Y t w) '' Set.Icc (0 : ℝ) T ⊆ U := by
    rintro _ ⟨t, ht, rfl⟩
    show Y t w ∈ U
    rw [hYZ w hw t ht, ← (hN0 w hw).1 t ht]
    have := (hN0 w hw).2.2 t.toNNReal (by rw [Real.coe_toNNReal _ ht.1]; exact ht.2)
    exact this
  obtain ⟨m, hm⟩ := r26t8a_o06_exists_V hC hCU
  have hwA : w ∈ A m := ⟨hw, by
    have : Y 0 w ∈ r26t8a_o06_V d N m := hm ⟨0, ⟨le_rfl, hT⟩, rfl⟩
    rwa [hY0 w hw] at this⟩
  have hgt : (T : WithTop ℝ) ≤ τ m w :=
    r26t8a_o06_tau_gt Y (r26t8a_o06_V_open m) hwA (hYc w) (fun t ht => hm ⟨t, ht, rfl⟩)
  have hd : ∀ s ∈ Set.Icc (0 : ℝ) T,
      itoDrift T f Z b' (fun _ _ => σ) s w =
        itoDrift T f (ofNNRealTime X) (ofNNRealTime b) (fun _ _ => σ) s w := by
    intro s hs
    have e2 : b' s w = ofNNRealTime b s w := by simp [b', hs.2]
    unfold itoDrift
    rw [← (hN0 w hw).1 s hs, e2]
  intro t ht
  have hle : (t : WithTop ℝ) ≤ τ m w := le_trans (WithTop.coe_le_coe.2 ht.2) hgt
  obtain ⟨hI, hE⟩ := h1 m t ht hle
  have hZt : Z t w = X t.toNNReal w := ((hN0 w hw).1 t ht).symm
  have hIc : ∀ s ∈ Set.Icc (0 : ℝ) t, itoDrift T f Z b' (fun _ _ => σ) s w =
      itoDrift T f (ofNNRealTime X) (ofNNRealTime b) (fun _ _ => σ) s w :=
    fun s hs => hd s ⟨hs.1, hs.2.trans ht.2⟩
  refine ⟨hI.congr_fun hIc measurableSet_Icc, ?_⟩
  rw [hZt] at hE
  rw [hE, h2 m t, h3 m t, ← h4 m t, stoppedProcess_eq_of_le hle]
  congr 2
  exact setIntegral_congr_fun measurableSet_Icc hIc

end HRS.MS.R26T8A

end
