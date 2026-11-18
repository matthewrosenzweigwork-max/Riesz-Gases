import HRS.MD.EQInterpWin

/-!
# EQ-INTERP packet, part 8: the `𝒳_{q,T}` second moments of the windows from the rational-time moments of `eq_strong_moment`

* `qSq_le_ratSup`: for a continuous path, `sup_{t∈[0,T]} ce q ≤ sup_{t∈ratTimes u T} ce q` (lower semicontinuity of the energy, `T > 0`);
* `flow_moment_pos`, `flow_moment_zero`: `∫ qSq q d(law windowZeta) ≤ C`; the case `T = 0` (where `ratTimes u 0` may be empty) is read off from
  stationarity and a flow on the horizon `0` (`eq_flow_exists`);
* `gauss_moment`: the same for the window of the stationary Gaussian field.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MD.EQInterp

variable {d : ℕ} {N : ℕ}

theorem ce_zero (q m : ℝ) : ce q (0 : NegSobolev d m) = 0 := by
  simp only [ce, HRS.MD.EQ29.coordEnergy]
  refine ENNReal.tsum_eq_zero.2 fun k => ?_
  have : NegSobolev.fourierCoeff (0 : NegSobolev d m) k = 0 := by
    simp only [NegSobolev.fourierCoeff]
    have : NegSobolev.coord (0 : NegSobolev d m) k = 0 := rfl
    rw [this]; simp
  simp [this]

theorem qSq_zero (q m T : ℝ) : qSq q (0 : PathSpace d m T) = 0 := by
  simp only [qSq]
  refine ENNReal.iSup_eq_zero.2 fun t => ?_
  have : (0 : PathSpace d m T).at' t = 0 := rfl
  rw [this, ce_zero]

theorem qSq_le_ratSup {m T : ℝ} (hT : 0 < T) (q u : ℝ) (w : PathSpace d m T) (Zf : ℝ → NegSobolev d m)
    (hZ : ∀ τ : Set.Icc (0 : ℝ) T, w.at' τ = Zf (u + τ)) :
    qSq q w ≤ ⨆ r ∈ HRS.LZ.ratTimes u T, ce q (Zf r) := by
  refine iSup_le fun τ₀ => le_of_forall_lt fun c hc => ?_
  let g : ℝ → ℝ≥0∞ := fun r => ce q (w.at' (Set.projIcc 0 T hT.le (r - u)))
  have hgl : LowerSemicontinuous g := by
    refine (ce_lsc (d := d) q m).comp ?_
    have h1 : Continuous fun t : Set.Icc (0 : ℝ) T => w.at' t :=
      (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from w).continuous
    exact h1.comp (continuous_projIcc.comp (continuous_id.sub continuous_const))
  have hopen : IsOpen {r : ℝ | c < g r} := hgl.isOpen_preimage c
  have hτ : (u + (τ₀ : ℝ)) ∈ {r : ℝ | c < g r} := by
    show c < g (u + τ₀)
    simp only [g, add_sub_cancel_left, Set.projIcc_val]
    exact hc
  have hcl : (u + (τ₀ : ℝ)) ∈ closure (Set.Ioo u (u + T)) := by
    rw [closure_Ioo (by linarith : u ≠ u + T)]
    exact ⟨by linarith [τ₀.2.1], by linarith [τ₀.2.2]⟩
  obtain ⟨r₁, hr₁g, hr₁⟩ := mem_closure_iff.1 hcl _ hopen hτ
  have hne : ({r : ℝ | c < g r} ∩ Set.Ioo u (u + T)).Nonempty := ⟨r₁, hr₁g, hr₁⟩
  obtain ⟨qq, hq⟩ := Rat.denseRange_cast.exists_mem_open (hopen.inter isOpen_Ioo) hne
  have hqI : (qq : ℝ) - u ∈ Set.Icc (0 : ℝ) T := ⟨by linarith [hq.2.1], by linarith [hq.2.2]⟩
  have hqmem : (qq : ℝ) ∈ HRS.LZ.ratTimes u T :=
    ⟨⟨hq.2.1.le, by linarith [hq.2.2]⟩, qq, rfl⟩
  have hqg : c < ce q (Zf qq) := by
    have h := hq.1
    simp only [Set.mem_setOf_eq, g, Set.projIcc_of_mem _ hqI] at h
    rw [hZ ⟨_, hqI⟩] at h
    simpa using h
  exact lt_of_lt_of_le hqg (le_iSup₂_of_le (qq : ℝ) hqmem le_rfl)

theorem windowZeta_eq_zero_of_not {m T u : ℝ} {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → Config d N) (ω : Ω)
    (hc : ¬ Continuous fun τ : Set.Icc (0 : ℝ) T =>
      zetaE m (P.map (X (Real.toNNReal (u + τ)))) (X (Real.toNNReal (u + τ)) ω)) :
    Main.windowZeta m T u P X ω = 0 := by
  unfold Main.windowZeta
  exact dif_neg hc

theorem flow_moment_pos (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) (hN : 2 ≤ N) {u T : ℝ} (hu : 0 ≤ u) (hT : 0 < T)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : HRS.LZ.IsStationaryGibbsFlow P s hs0 hsd V β hβ (u + T) X₀ W X) {m q : ℝ}
    (hm : (d : ℝ) < 2 * m) (C : ℝ)
    (hmom : ∫⁻ ω, ⨆ t ∈ HRS.LZ.ratTimes u T, HRS.MD.EQ29.coordEnergy q (fun k =>
      NegSobolev.fourierCoeff (zetaE m (P.map (X t.toNNReal)) (X t.toNNReal ω)) k) ∂P ≤
        ENNReal.ofReal C) :
    ∫⁻ w, qSq q w ∂(P.map (Main.windowZeta m T u P X)) ≤ ENNReal.ofReal C := by
  have hAE := windowZeta_aemeasurable hd hs0 hsd V hV hβ hN hu hT.le P hX hm
  rw [lintegral_map' (qSq_measurable q m T).aemeasurable hAE]
  refine le_trans (lintegral_mono fun ω => ?_) hmom
  by_cases hc : Continuous fun τ : Set.Icc (0 : ℝ) T =>
      zetaE m (P.map (X (Real.toNNReal (u + τ)))) (X (Real.toNNReal (u + τ)) ω)
  · exact qSq_le_ratSup hT q u _ (fun r => zetaE m (P.map (X r.toNNReal)) (X r.toNNReal ω))
      (fun τ => windowZeta_at' P X ω hc τ)
  · rw [windowZeta_eq_zero_of_not P X ω hc, qSq_zero]; exact bot_le

theorem flow_moment_zero (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ)
    (hV : Torus.IsSmooth V) {β : ℝ} (hβ : 0 < β) (hN : 2 ≤ N) {u : ℝ} (hu : 0 ≤ u)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : HRS.LZ.IsStationaryGibbsFlow P s hs0 hsd V β hβ (u + 0) X₀ W X) {m q : ℝ}
    (hm : (d : ℝ) < 2 * m) (C : ℝ)
    (hone : ∀ (Ω' : Type) [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (X₀' : Ω' → Config d N) (W' : ℝ≥0 → Ω' → (Fin N → Euc d)) (X' : ℝ≥0 → Ω' → Config d N),
      HRS.LZ.IsStationaryGibbsFlow P' s hs0 hsd V β hβ (0 + 0) X₀' W' X' →
      ∫⁻ ω, ⨆ t ∈ HRS.LZ.ratTimes 0 0, HRS.MD.EQ29.coordEnergy q (fun k =>
        NegSobolev.fourierCoeff (zetaE m (P'.map (X' t.toNNReal)) (X' t.toNNReal ω)) k) ∂P' ≤
          ENNReal.ofReal C)
    (hex : ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
      (X₀' : Ω' → Config d N) (W' : ℝ≥0 → Ω' → (Fin N → Euc d)) (X' : ℝ≥0 → Ω' → Config d N),
      HRS.LZ.IsStationaryGibbsFlow P' s hs0 hsd V β hβ (0 + 0) X₀' W' X') :
    ∫⁻ w, qSq q w ∂(P.map (Main.windowZeta m 0 u P X)) ≤ ENNReal.ofReal C := by
  have hAE := windowZeta_aemeasurable hd hs0 hsd V hV hβ hN hu le_rfl P hX hm
  obtain ⟨hstat, hmeas, -⟩ := flow_facts hd hs0 hsd V hV hβ hN P hX
  haveI hGp : IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V N β) := by
    rw [← hstat 0 (by simp; positivity)]
    exact (Measure.isProbabilityMeasure_map_iff (hmeas 0).aemeasurable).2 inferInstance
  set G := canonicalGibbs (periodicRiesz d s) V N β with hG
  set f : Config d N → ℝ≥0∞ := fun x => ce q (zetaE m G x) with hf
  have hfm : Measurable f :=
    (ce_lsc q m).measurable.comp (EQLawPath.eqlaw_continuous_zetaE hm (by omega) G).measurable
  rw [lintegral_map' (qSq_measurable q m 0).aemeasurable hAE]
  have hu' : P.map (X u.toNNReal) = G := hstat _ (by rw [Real.coe_toNNReal _ hu]; linarith)
  calc ∫⁻ ω, qSq q (Main.windowZeta m 0 u P X ω) ∂P
      ≤ ∫⁻ ω, f (X u.toNNReal ω) ∂P := by
        refine lintegral_mono fun ω => ?_
        by_cases hc : Continuous fun τ : Set.Icc (0 : ℝ) 0 =>
            zetaE m (P.map (X (Real.toNNReal (u + τ)))) (X (Real.toNNReal (u + τ)) ω)
        · refine iSup_le fun τ => ?_
          have hτ : (τ : ℝ) = 0 := le_antisymm τ.2.2 τ.2.1
          rw [windowZeta_at' P X ω hc τ]
          simp only [hτ, add_zero, hf, hu']
          exact le_rfl
        · rw [windowZeta_eq_zero_of_not P X ω hc, qSq_zero]; exact bot_le
    _ = ∫⁻ x, f x ∂G := by
        rw [← hu', lintegral_map hfm (hmeas _)]
    _ ≤ ENNReal.ofReal C := by
        obtain ⟨Ω', mΩ', P', hP', X₀', W', X', hX'⟩ := hex
        obtain ⟨hstat', hmeas', -⟩ := flow_facts hd hs0 hsd V hV hβ hN P' hX'
        have h0 : P'.map (X' (0 : ℝ).toNNReal) = G := hstat' _ (by simp)
        calc ∫⁻ x, f x ∂G = ∫⁻ ω, f (X' (0 : ℝ).toNNReal ω) ∂P' := by
              rw [← h0, lintegral_map hfm (hmeas' _)]
          _ ≤ ∫⁻ ω, ⨆ t ∈ HRS.LZ.ratTimes 0 0, HRS.MD.EQ29.coordEnergy q (fun k =>
              NegSobolev.fourierCoeff (zetaE m (P'.map (X' t.toNNReal)) (X' t.toNNReal ω)) k) ∂P' := by
              refine lintegral_mono fun ω => ?_
              refine le_iSup₂_of_le (0 : ℝ) ⟨⟨le_rfl, by simp⟩, 0, by simp⟩ ?_
              simp only [hf, h0, ce, HRS.MD.EQ29.coordEnergy]
              exact le_rfl
          _ ≤ ENNReal.ofReal C := hone Ω' P' X₀' W' X' hX'

theorem gauss_moment {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (V : Torus d → ℝ) {β : ℝ}
    (hβ : 0 < β) (ρβ : Torus d → ℝ) {m q T : ℝ} (hT : 0 ≤ T)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : ℝ → Ω' → NegSobolev d m) (hZ : IsStationaryGaussianField P' s β hs0 hsd hβ V ρβ m Z)
    (C : ℝ)
    (hmom : ∫⁻ ω, ⨆ t ∈ HRS.LZ.ratTimes 0 T, HRS.MD.EQ29.coordEnergy q (fun k =>
      NegSobolev.fourierCoeff (Z t ω) k) ∂P' ≤ ENNReal.ofReal C) :
    ∫⁻ w, qSq q w ∂(P'.map (Main.windowPath m T 0 Z)) ≤ ENNReal.ofReal C := by
  have hAE := (EQGaussWindow.eqgw_fidi hd hs0 hsd V hβ ρβ m T P' Z hZ 0 le_rfl).1
  rw [lintegral_map' (qSq_measurable q m T).aemeasurable hAE]
  refine le_trans (lintegral_mono_ae ?_) hmom
  filter_upwards [hZ.cont] with ω hω
  rcases hT.eq_or_lt with h0 | hpos
  · subst h0
    refine iSup_le fun τ => ?_
    have hτ : (τ : ℝ) = 0 := le_antisymm τ.2.2 τ.2.1
    rw [windowPath_at' Z ω hω τ, hτ, zero_add]
    exact le_iSup₂_of_le (0 : ℝ) ⟨⟨le_rfl, by simp⟩, 0, by simp⟩ le_rfl
  · exact qSq_le_ratSup hpos q 0 _ (fun r => Z r ω) (fun τ => windowPath_at' Z ω hω τ)

end HRS.MD.EQInterp
