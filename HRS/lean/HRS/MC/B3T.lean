import HRS.Stochastic.SelectedLawFKE

/-!
# Packet B3T: Proposition B.3 at intermediate times

The distributional forward Kolmogorov identity of `HRS.selected_law_fke_FKE` (proved there only at
the horizon `T`) is extended to every time `t ∈ [0, T)`:
`∫ Φ t dP^t − ∫ Φ 0 dP^0 = ∫_0^t ∫ (generator + interaction) dP^r dr`.

The generator `fkeGenerator D T Φ` contains the time derivative `∂_r Φ` (as
`derivWithin (configLift Φ · Y) (Icc 0 T)`), exactly as in `selected_law_fke_FKE`.
The proof re-runs that argument with the Itô evaluation time `t` in place of `T`:
`ito_formula_additive` (horizon `T`) already concludes at every time `≤ T`, so only the terminal
evaluation, the martingale time and the time-integration domain change.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.B3T

variable {d N : ℕ}

/-- Proposition B.3 at an intermediate time `t ∈ [0, T)`: the distributional forward Kolmogorov
identity on `[0, t]`, with the terminal term `Φ t` no longer zero. -/
theorem selected_law_fke_all_times {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {D : DynData d} (hN : 2 ≤ N) (hV : Torus.IsCk 2 D.V) {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : SelectedFlow P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X)
    (Φ : ℝ → Config d N → ℝ) (hΦ : IsFKETest T Φ)
    (t : ℝ) (ht0 : 0 ≤ t) (htT : t < T) :
    ∫ x, Φ t x ∂(selectedLaw P X t) - ∫ x, Φ 0 x ∂(selectedLaw P X 0)
      = ∫ r in (0:ℝ)..t, ∫ x, (fkeGenerator D T Φ r x + fkeInteraction D Φ r x)
          ∂(selectedLaw P X r) := by
  have hT0 : 0 ≤ T := hT.le
  have htT' : t ≤ T := htT.le
  have hN0 : 0 < N := by omega
  have hsd : D.s < d := D.hsd
  have hC := selectedFlow_toContact hX
  obtain ⟨K, hK, hdisj, hsupp⟩ := hΦ.space_support
  have hΦc := hΦ.c12
  obtain ⟨C0, hC0⟩ := bounded_of_periodic (T := T) (fun s Y => configLift Φ s Y) hΦc.cont
    (fun s Y v hv => configLift_add_lattice Φ s hv Y)
  obtain ⟨Cf, hCf⟩ := fkeIto_bound hT0 D hN0 hV Φ hΦc hK hdisj hsupp
  obtain ⟨C1, hC1⟩ := bounded_of_periodic (T := T) (fun s Y => fderiv ℝ (configLift Φ s) Y)
    hΦc.cont_fderiv (fun s Y v hv => fderiv_configLift_add_lattice Φ s hv Y)
  -- almost sure lift facts
  have hlift := hC.ae_lift_eq hF
  have hI0 : ∀ᵐ ω ∂P, IntegrableOn (fun s : ℝ => driftProc D X (Real.toNNReal s) ω) (Set.Icc 0 T) :=
    hC.ae_integrableOn_drift hT0 le_rfl
  have hint : ∀ᵐ ω ∂P, ∀ τ : ℝ≥0, (τ : ℝ) ≤ T →
      intPart D X τ ω = ∫ s in Set.Icc (0 : ℝ) (τ : ℝ), driftProc D X (Real.toNNReal s) ω := by
    filter_upwards [hI0] with ω hω τ hτ
    exact intPart_eq_integral ω τ (hω.mono_set (Set.Icc_subset_Icc le_rfl hτ))
  have hlift' : ∀ᵐ ω ∂P, ∀ τ : ℝ≥0, (τ : ℝ) ≤ T →
      X τ ω = fun i => Torus.mk (liftProcM D W' X τ ω i) := by
    filter_upwards [hlift, hint] with ω h1 h2 τ hτ
    rw [h1 τ hτ]
    funext i
    simp only [liftProcM, liftProc, h2 τ hτ]
  have hZint : ∀ᵐ ω ∂P, ∀ τ : ℝ≥0, (τ : ℝ) ≤ T →
      liftProcM D W' X τ ω = liftProcM D W' X 0 ω
        + (∫ s in Set.Icc (0 : ℝ) τ, driftProc D X (Real.toNNReal s) ω)
        + ∑ k, (W' τ ω k - W' 0 ω k) • liftedNoise D k := by
    filter_upwards [hint] with ω hω τ hτ
    rw [liftProcM_zero ω]
    simp only [liftProcM]
    rw [hω τ hτ]
  have hX₀ : ∀ s : ℝ, Measurable[ℱ s] (liftProcM D W' X 0) := by
    intro s
    have e : liftProcM D W' X 0 = fun ω => fun i => Torus.rep (X 0 ω i) :=
      funext fun ω => liftProcM_zero ω
    rw [e]
    have hg : Measurable (fun x : Config d N => fun i => Torus.rep (x i)) :=
      measurable_pi_iff.2 fun i => (measurable_torusRep d).comp (measurable_pi_apply i)
    exact hg.comp (hF.measurable_init s)
  -- Itô's formula for `configLift Φ` along the lift (horizon `T`; valid at every time `≤ T`)
  have hito := ito_formula_additive (P := P) (ℱ := ℱ) hF.brownian (T := T) hT0 (configLift Φ) hΦc
    (liftedNoise D) (liftProcM D W' X) (measurable_liftProcM hV hF) hX₀ (driftProc D X)
    (isProgressive_driftProc hV hF) hI0 hZint
  have hτ : ((Real.toNNReal t : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht0
  have hτT : ((Real.toNNReal t : ℝ≥0) : ℝ) ≤ T := by
    rw [hτ]
    exact htT'
  -- pathwise identity at the Itô time `t`
  have hcore : ∀ᵐ ω ∂P, Φ t (X (Real.toNNReal t) ω) - Φ 0 (X 0 ω)
      = (∫ s in Set.Icc (0:ℝ) t, fkeSample D T Φ X s ω)
        + localItoIntegral P ℱ W' (itoIntegrand T Set.univ (configLift Φ)
            (ofNNRealTime (liftProcM D W' X)) (fun _ _ => liftedNoise D)) t ω := by
    filter_upwards [hito, hlift'] with ω hωito hω
    have h := hωito.2 (Real.toNNReal t) hτT
    rw [hτ] at h
    have hL : configLift Φ t (liftProcM D W' X (Real.toNNReal t) ω)
        = Φ t (X (Real.toNNReal t) ω) := by
      show Φ t (fun i => Torus.mk (liftProcM D W' X (Real.toNNReal t) ω i)) = _
      rw [← hω (Real.toNNReal t) hτT]
    have hcol0 : configLift Φ 0 (liftProcM D W' X 0 ω) = Φ 0 (X 0 ω) := by
      have h0 := hω 0 (by simpa using hT0)
      show Φ 0 (fun i => Torus.mk (liftProcM D W' X 0 ω i)) = Φ 0 (X 0 ω)
      rw [h0]
    have hint2 : ∫ s in Set.Icc (0:ℝ) t, itoDrift T (configLift Φ)
        (ofNNRealTime (liftProcM D W' X)) (ofNNRealTime (driftProc D X))
        (fun _ _ => liftedNoise D) s ω = ∫ s in Set.Icc (0:ℝ) t, fkeSample D T Φ X s ω := by
      refine setIntegral_congr_fun measurableSet_Icc fun s hs => ?_
      have hsT : s ∈ Set.Icc (0:ℝ) T := ⟨hs.1, hs.2.trans htT'⟩
      have hsτ : ((Real.toNNReal s : ℝ≥0) : ℝ) ≤ T := by
        rw [Real.coe_toNNReal _ hs.1]
        exact hsT.2
      have hx := hω _ hsτ
      rw [itoDrift_eq_fkeIto D T Φ (liftProcM D W' X) X ω s hx]
      unfold fkeSample
      rw [clampTI_of_mem hsT]
      have hmk : ∀ i, Torus.mk (repC (X (Real.toNNReal s) ω) i)
          = Torus.mk (liftProcM D W' X (Real.toNNReal s) ω i) := by
        intro i
        show Torus.mk (Torus.rep (X (Real.toNNReal s) ω i)) = _
        rw [Torus.mk_rep]
        exact congrFun hx i
      exact (fkeIto_eq_of_mk D T Φ s hmk).symm
    rw [hL, hcol0, hint2] at h
    linarith
  -- the reference integrand and the martingale term
  have hΨprog := isProgressive_fkeRef hF.progressive hT0 D Φ hΦc
  have hΨL2 : IsProgressiveL2 P ℱ (fun s ω k => fkeRef D T Φ X s ω k) :=
    IsProgressiveL2.of_bounded P hΨprog (max C1 0 * ∑ j : Fin N × Fin d, ‖liftedNoise D j‖)
      (fun s ω k => fkeRef_bound hT0 D Φ hC1 s ω k)
  obtain ⟨N0, hN0m, hN0P, hN0⟩ := exists_null_of_ae (P := P)
    (p := fun ω => ∀ τ : ℝ≥0, (τ : ℝ) ≤ T → X τ ω = fun i => Torus.mk (liftProcM D W' X τ ω i)) hlift'
  have hMart : ∀ᵐ ω ∂P, localItoIntegral P ℱ W' (itoIntegrand T Set.univ (configLift Φ)
          (ofNNRealTime (liftProcM D W' X)) (fun _ _ => liftedNoise D)) t ω
        = itoIntegral P ℱ W' (fun s ω k => fkeRef D T Φ X s ω k) t ω := by
    have hcongr := localItoIntegral_congr_null hF.brownian hΨL2.locL2 hN0m hN0P
      (Ψ := itoIntegrand T Set.univ (configLift Φ) (ofNNRealTime (liftProcM D W' X))
        (fun _ _ => liftedNoise D))
      (fun s ω hω => by
        funext k
        exact itoIntegrand_eq_fkeRef D Φ W' X ω (hN0 ω hω) s k)
      (fun s hs ω => by
        have hn : s ∉ Set.Icc (0:ℝ) T := fun h => absurd h.1 (not_le.2 hs)
        funext k
        simp [itoIntegrand, hn])
      (fun s hs ω => by
        have hn : s ∉ Set.Icc (0:ℝ) T := fun h => absurd h.1 (not_le.2 hs)
        funext k
        simp [fkeRef, hn])
    have hloc := localItoIntegral_eq_itoIntegral hF.brownian hΨL2
    filter_upwards [hcongr, hloc] with ω h1 h2
    rw [h1 t, h2 t]
  have hMLp : MemLp (itoIntegral P ℱ W' (fun s ω k => fkeRef D T Φ X s ω k) t) 2 P :=
    memLp_two_itoIntegral hF.brownian hΨL2 t
  have hMint : ∫ ω, itoIntegral P ℱ W' (fun s ω k => fkeRef D T Φ X s ω k) t ω ∂P = 0 :=
    integral_itoIntegral hF.brownian hΨL2 t
  have hsum : ∀ᵐ ω ∂P, Φ t (X (Real.toNNReal t) ω) - Φ 0 (X 0 ω)
      = (∫ s in Set.Icc (0:ℝ) t, fkeSample D T Φ X s ω)
        + itoIntegral P ℱ W' (fun s ω k => fkeRef D T Φ X s ω k) t ω := by
    filter_upwards [hcore, hMart] with ω h1 h2
    rw [h2] at h1
    exact h1
  -- integrability
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc (0:ℝ) t)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Icc_lt_top⟩
  have hprodm : Measurable (fun p : ℝ × Ω => fkeSample D T Φ X p.1 p.2) :=
    measurable_fkeIto_sample hF.progressive hT0 D hV Φ hΦc
  have hprodint : Integrable (fun p : ℝ × Ω => fkeSample D T Φ X p.1 p.2)
      ((volume.restrict (Set.Icc (0:ℝ) t)).prod P) :=
    Integrable.of_bound hprodm.aestronglyMeasurable Cf
      (ae_of_all _ fun p => hCf _ (clampTI_mem hT0 p.1) (repC (X (Real.toNNReal p.1) p.2)))
  have hIint : Integrable (fun ω => ∫ s in Set.Icc (0:ℝ) t, fkeSample D T Φ X s ω) P :=
    hprodint.integral_prod_right
  have hm0 : Measurable (fun x : Config d N => Φ 0 x) := by
    have e : (fun x : Config d N => Φ 0 x) = fun x => configLift Φ 0 (repC x) := by
      funext x
      show Φ 0 x = Φ 0 (fun i => Torus.mk (repC x i))
      rw [mk_repC]
    have hcont0 : Continuous (configLift Φ 0) :=
      hΦc.cont.comp_continuous (continuous_const.prodMk continuous_id)
        (fun Y => ⟨⟨le_refl (0:ℝ), hT0⟩, Set.mem_univ Y⟩)
    rw [e]
    exact hcont0.measurable.comp measurable_repC
  have hmt : Measurable (fun x : Config d N => Φ t x) := by
    have e : (fun x : Config d N => Φ t x) = fun x => configLift Φ t (repC x) := by
      funext x
      show Φ t x = Φ t (fun i => Torus.mk (repC x i))
      rw [mk_repC]
    have hcont : Continuous (configLift Φ t) :=
      hΦc.cont.comp_continuous (continuous_const.prodMk continuous_id)
        (fun Y => ⟨⟨ht0, htT'⟩, Set.mem_univ Y⟩)
    rw [e]
    exact hcont.measurable.comp measurable_repC
  have hΦ0int : Integrable (fun ω => Φ 0 (X 0 ω)) P := by
    have hb : ∀ x : Config d N, ‖Φ 0 x‖ ≤ C0 := fun x => by
      have e : Φ 0 x = configLift Φ 0 (repC x) := by
        show Φ 0 x = Φ 0 (fun i => Torus.mk (repC x i))
        rw [mk_repC]
      rw [e]
      exact hC0 0 ⟨le_refl (0:ℝ), hT0⟩ (repC x)
    exact Integrable.of_bound ((hm0.comp (hC.adapted 0)).aestronglyMeasurable) C0
      (ae_of_all _ fun ω => hb _)
  have hΦtint : Integrable (fun ω => Φ t (X (Real.toNNReal t) ω)) P := by
    have hb : ∀ x : Config d N, ‖Φ t x‖ ≤ C0 := fun x => by
      have e : Φ t x = configLift Φ t (repC x) := by
        show Φ t x = Φ t (fun i => Torus.mk (repC x i))
        rw [mk_repC]
      rw [e]
      exact hC0 t ⟨ht0, htT'⟩ (repC x)
    exact Integrable.of_bound ((hmt.comp (hC.adapted (Real.toNNReal t))).aestronglyMeasurable) C0
      (ae_of_all _ fun ω => hb _)
  have hMi : Integrable (fun ω => itoIntegral P ℱ W' (fun s ω k => fkeRef D T Φ X s ω k) t ω) P :=
    hMLp.integrable one_le_two
  -- Fubini and the identification with the selected law on `[0, t]`
  have hIeq : ∫ ω, (∫ s in Set.Icc (0:ℝ) t, fkeSample D T Φ X s ω) ∂P
      = ∫ r in Set.Icc (0:ℝ) t, ∫ x, (fkeGenerator D T Φ r x + fkeInteraction D Φ r x)
          ∂(selectedLaw P X r) := by
    have hswap := integral_integral_swap (μ := volume.restrict (Set.Icc (0:ℝ) t)) (ν := P)
      (f := fun s ω => fkeSample D T Φ X s ω) hprodint
    rw [← hswap]
    refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    have hrT : r ∈ Set.Icc (0:ℝ) T := ⟨hr.1, hr.2.trans htT'⟩
    have hg : Measurable (fun x : Config d N => fkeIto D T Φ (clampTI T r) (repC x)) :=
      (measurable_fkeIto_lift hT0 D hV Φ hΦc).comp (measurable_const.prodMk measurable_repC)
    have e : ∀ x : Config d N, fkeGenerator D T Φ r x + fkeInteraction D Φ r x
        = fkeIto D T Φ (clampTI T r) (repC x) := by
      intro x
      rw [clampTI_of_mem hrT]
      exact fkeGI_eq_fkeIto D hsd T Φ r x
    simp only [e]
    exact (integral_selectedLaw_eq hC r hg).symm
  have hLHSt : ∫ x, Φ t x ∂(selectedLaw P X t) = ∫ ω, Φ t (X (Real.toNNReal t) ω) ∂P :=
    integral_selectedLaw_eq hC t hmt
  have hLHS : ∫ x, Φ 0 x ∂(selectedLaw P X 0) = ∫ ω, Φ 0 (X 0 ω) ∂P := by
    rw [integral_selectedLaw_eq hC 0 hm0, Real.toNNReal_zero]
  have hdiff : ∫ ω, (Φ t (X (Real.toNNReal t) ω) - Φ 0 (X 0 ω)) ∂P
      = ∫ ω, ((∫ s in Set.Icc (0:ℝ) t, fkeSample D T Φ X s ω)
        + itoIntegral P ℱ W' (fun s ω k => fkeRef D T Φ X s ω k) t ω) ∂P :=
    integral_congr_ae hsum
  rw [integral_sub hΦtint hΦ0int, integral_add hIint hMi, hMint, add_zero] at hdiff
  rw [hLHSt, hLHS, intervalIntegral.integral_of_le ht0, ← integral_Icc_eq_integral_Ioc, ← hIeq]
  exact hdiff

/-- Proposition B.3 at every time of `[0, T)`, in pointwise form. -/
theorem selected_law_fke_all_times_Ico {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {D : DynData d} (hN : 2 ≤ N) (hV : Torus.IsCk 2 D.V) {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : SelectedFlow P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X)
    (Φ : ℝ → Config d N → ℝ) (hΦ : IsFKETest T Φ) :
    ∀ t ∈ Set.Ico (0:ℝ) T,
      ∫ x, Φ t x ∂(selectedLaw P X t) - ∫ x, Φ 0 x ∂(selectedLaw P X 0)
        = ∫ r in (0:ℝ)..t, ∫ x, (fkeGenerator D T Φ r x + fkeInteraction D Φ r x)
            ∂(selectedLaw P X r) :=
  fun t ht => selected_law_fke_all_times hN hV hT hX hF Φ hΦ t ht.1 ht.2

end HRS.MC.B3T
