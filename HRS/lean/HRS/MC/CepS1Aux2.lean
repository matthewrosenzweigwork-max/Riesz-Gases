import HRS.MC.CepS1Aux1

/-!
# Packet CEPS1 (auxiliary 2): barrier chain under a `C^{1,1}` potential

Mechanical copy-adaptation of theorems of `HRS/Stochastic/Particle.lean` (line ranges L3337-3522, L3643-3734) with
`Torus.IsCk 2 D.V` replaced by `cep_IsC11 D.V`; the hypothesis enters only through the Lipschitz
constant of `∇V` and the local Lipschitz continuity of the drift (`HRS.MC.CepC0.cepc0_locLipschitz`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepS1

open HRS HRS.ClusterBarrier HRS.MC.CepC0

variable {d N : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}

theorem stopped_estimate [IsProbabilityMeasure P] (D : DynData d) (hK : KernelLocal d D.s)
    (hV : cep_IsC11 D.V) (hW' : IsBrownianFiltration P ℱ W')
    {Y₀ : Ω → (Fin N → Euc d)} {τ : Ω → WithTop ℝ} {Y : ℝ → Ω → (Fin N → Euc d)}
    (hsol : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y) {T : ℝ} (hT : 0 ≤ T)
    {U : Set (Fin N → Euc d)} (hU : IsOpen U) (Kc : Set (Fin N → Euc d)) (hKc : IsCompact Kc)
    (hKU : Kc ⊆ U) (hKfree : Kc ⊆ liftedFree d N) {g : (Fin N → Euc d) → ℝ}
    (hg : ContDiffOn ℝ 2 g U) {G : Set (Fin N → Euc d)} (hG : IsClosed G) (hGK : Gᶜ ⊆ Kc)
    {C' : ℝ} (hC' : 0 ≤ C') (hgen : ∀ Z ∈ Kc, diffGen D g Z ≤ C')
    {A : Set Ω} (hA : ∀ t : ℝ, MeasurableSet[ℱ t] A) (hAK : ∀ ω ∈ A, Y₀ ω ∈ Kc) :
    ∃ Z : Ω → (Fin N → Euc d), Measurable Z ∧ (∀ ω ∈ A, Z ω ∈ Kc) ∧
      (∀ ω ∈ A, ∀ t : ℝ, 0 ≤ t → t ≤ T → solHit τ Y G ω = (t : WithTop ℝ) → Z ω = Y t ω) ∧
      IntegrableOn (fun ω => g (Z ω)) A P ∧ IntegrableOn (fun ω => g (Y₀ ω)) A P ∧
      ∫ ω in A, g (Z ω) ∂P ≤ ∫ ω in A, g (Y₀ ω) ∂P + C' * T * (P A).toReal := by
  classical
  have hY0 : ∀ t : ℝ, Measurable[ℱ t] (Y 0) := by
    have : Y 0 = Y₀ := funext hsol.sol.init
    rw [this]; exact hsol.init_meas
  have hcontY := hsol.sol.cont
  have hexit : ∀ ω, τ ω < ⊤ → ∃ r : ℝ, 0 ≤ r ∧ (r : WithTop ℝ) < τ ω ∧ Y r ω ∈ G := by
    intro ω hω
    obtain ⟨t, ht0, htτ, htK⟩ := hsol.exit ω hω Kc hKc hKfree 0 (by simpa using hsol.pos ω)
    exact ⟨t, ht0.le, htτ, by_contra fun h => htK (hGK h)⟩
  have hρ₀ : IsStoppingTime ℱ (solHit τ Y G) :=
    isStoppingTime_solHit ℱ hsol.stopping hsol.sol.adapted hcontY hG hexit
  have hcontP : ∀ ω (t : ℝ), 0 ≤ t → (t : WithTop ℝ) < τ ω →
      ContinuousOn (fun s => Y s ω) (Set.Icc 0 t) := hcontY
  have hρ₀nn : ∀ ω, (0 : WithTop ℝ) ≤ solHit τ Y G ω := fun ω =>
    pathHit_nonneg hG (hcontP ω)
  -- the stopping time
  set ρ' : Ω → WithTop ℝ := fun ω =>
    if ω ∈ A then min (solHit τ Y G ω) (T : WithTop ℝ) else (((-1 : ℝ)) : WithTop ℝ) with hρ'def
  have hρ'A : ∀ ω ∈ A, ρ' ω = min (solHit τ Y G ω) (T : WithTop ℝ) := fun ω hω => by
    simp [hρ'def, hω]
  have hρ'nA : ∀ ω, ω ∉ A → ρ' ω = (((-1 : ℝ)) : WithTop ℝ) := fun ω hω => by
    simp [hρ'def, hω]
  have hρ' : IsStoppingTime ℱ ρ' := by
    intro t
    have : {ω | ρ' ω ≤ (t : WithTop ℝ)} =
        (A ∩ {ω | min (solHit τ Y G ω) (T : WithTop ℝ) ≤ (t : WithTop ℝ)}) ∪
          (Aᶜ ∩ {_ω | (((-1 : ℝ)) : WithTop ℝ) ≤ (t : WithTop ℝ)}) := by
      ext ω
      by_cases hω : ω ∈ A
      · simp [hρ'A ω hω, hω]
      · simp [hρ'nA ω hω, hω]
    rw [this]
    exact ((hA t).inter ((hρ₀.min_const T) t)).union ((hA t).compl.inter (MeasurableSet.const _))
  have hρ'T : ∀ ω, ρ' ω ≤ (T : WithTop ℝ) := by
    intro ω
    by_cases hω : ω ∈ A
    · rw [hρ'A ω hω]; exact min_le_right _ _
    · rw [hρ'nA ω hω]; exact_mod_cast (by linarith : (-1 : ℝ) ≤ T)
  have hρ'τ : ∀ ω, ρ' ω < τ ω := by
    intro ω
    by_cases hω : ω ∈ A
    · rw [hρ'A ω hω]
      by_cases hτ : τ ω = ⊤
      · rw [hτ]; exact lt_of_le_of_lt (min_le_right _ _) (WithTop.coe_lt_top T)
      · have hlt : τ ω < ⊤ := lt_top_iff_ne_top.2 hτ
        obtain ⟨r, hr0, hrτ, hrG⟩ := hexit ω hlt
        have := (pathHit_le_iff hG (hcontP ω) r).2 ⟨r, hr0, le_rfl, hrτ, hrG⟩
        exact lt_of_le_of_lt (min_le_left _ _) (lt_of_le_of_lt this hrτ)
    · rw [hρ'nA ω hω]
      exact lt_of_lt_of_le (by exact_mod_cast (by norm_num : (-1 : ℝ) < 0)) (hsol.pos ω).le
  have hρ'nn : ∀ ω ∈ A, (0 : WithTop ℝ) ≤ ρ' ω := fun ω hω => by
    rw [hρ'A ω hω]; exact le_min (hρ₀nn ω) (by exact_mod_cast hT)
  have hYK : ∀ ω, ∀ t ∈ Set.Icc (0 : ℝ) T, (t : WithTop ℝ) ≤ ρ' ω → Y t ω ∈ Kc := by
    intro ω t ht htρ
    by_cases hω : ω ∈ A
    · have htτ : (t : WithTop ℝ) < τ ω := lt_of_le_of_lt htρ (hρ'τ ω)
      rw [hρ'A ω hω] at htρ
      have h0 : (fun s => Y s ω) 0 ∈ Kc := by
        simp only [hsol.sol.init ω]; exact hAK ω hω
      exact pathHit_mem_of_le hG hKc.isClosed hGK (hcontP ω) h0 ht.1
        htτ (htρ.trans (min_le_left _ _))
    · rw [hρ'nA ω hω] at htρ
      exfalso
      have : t ≤ -1 := by exact_mod_cast htρ
      linarith [ht.1]
  obtain ⟨Ψ, hΨ, -, hmain⟩ := ito_along_solution D hK hV hW' hsol hT ρ' hρ' hρ'τ hU Kc hKc hKU
    hKfree hg hYK
  have hprog := isProgressive_stoppedPath ℱ Y hsol.sol.adapted hY0 hρ'
    (fun ω t ht htρ => hcontP ω t ht (lt_of_le_of_lt htρ (hρ'τ ω)))
  set Wp : ℝ → Ω → (Fin N → Euc d) := fun s ω =>
    Set.indicator {ω | (s : WithTop ℝ) ≤ ρ' ω} (fun ω => Y (max s 0) ω) ω with hWp
  have hZmeasT : StronglyMeasurable[ℱ T] (stoppedValue Wp ρ') :=
    stronglyMeasurable_stoppedValue_of_le hprog.isStronglyProgressive hρ' hρ'T
  have hZm : Measurable (stoppedValue Wp ρ') := hZmeasT.measurable.mono (ℱ.le T) le_rfl
  have hZ : ∀ ω ∈ A, ∃ r : ℝ, ρ' ω = (r : WithTop ℝ) ∧ 0 ≤ r ∧ r ≤ T ∧
      stoppedValue Wp ρ' ω = Y r ω := by
    intro ω hω
    have hne : ρ' ω ≠ ⊤ := ne_top_of_le_ne_top (WithTop.coe_ne_top) (hρ'T ω)
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hne
    have hr' : ρ' ω = (r : WithTop ℝ) := hr.symm
    have hr0 : 0 ≤ r := by have := hρ'nn ω hω; rw [hr'] at this; exact_mod_cast this
    have hrT : r ≤ T := by have := hρ'T ω; rw [hr'] at this; exact_mod_cast this
    refine ⟨r, hr', hr0, hrT, ?_⟩
    simp only [stoppedValue, hr', hWp, untopA_coe']
    rw [Set.indicator_of_mem (show ω ∈ {ω | ((r : ℝ) : WithTop ℝ) ≤ ρ' ω} from by
      simp [hr']), max_eq_left hr0]
  have hZK : ∀ ω ∈ A, stoppedValue Wp ρ' ω ∈ Kc := by
    intro ω hω
    obtain ⟨r, hr, hr0, hrT, hZr⟩ := hZ ω hω
    rw [hZr]; exact hYK ω r ⟨hr0, hrT⟩ (by rw [hr])
  refine ⟨stoppedValue Wp ρ', hZm, hZK, ?_, ?_⟩
  · intro ω hω t ht0 htT hhit
    obtain ⟨r, hr, hr0, hrT, hZr⟩ := hZ ω hω
    rw [hρ'A ω hω, hhit, min_eq_left (by exact_mod_cast htT)] at hr
    have : t = r := by exact_mod_cast hr
    rw [hZr, this]
  have hAm : MeasurableSet A := ℱ.le 0 _ (hA 0)
  set u := itoIntegral P ℱ W' Ψ with hu
  have hmart := martingale_stoppedProcess_itoIntegral hW' hΨ hρ'
  have hΨs : IsProgressiveL2 P ℱ (stopIntegrand Ψ ρ') := hΨ.stopIntegrand hρ'
  have hloc := localItoIntegral_eq_itoIntegral hW' hΨs
  have hst := itoIntegral_stopIntegrand hW' hΨ hρ'
  have hae : ∀ᵐ ω ∂P, ω ∈ A → g (stoppedValue Wp ρ' ω) ≤
      g (Y₀ ω) + C' * T + stoppedProcess u ρ' T ω := by
    filter_upwards [hmain, hloc, hst] with ω h1 h2 h3 hω
    obtain ⟨r, hr, hr0, hrT, hZr⟩ := hZ ω hω
    obtain ⟨hint, heq⟩ := h1 r ⟨hr0, hrT⟩ (by rw [hr])
    have hM : localItoIntegral P ℱ W' (stopIntegrand Ψ ρ') r ω = stoppedProcess u ρ' T ω := by
      rw [h2 r, h3 r]
      simp only [stoppedProcess, hr, min_self]
      rw [min_eq_right (by exact_mod_cast hrT : (r : WithTop ℝ) ≤ T)]
    have hbd : ∫ s in Set.Icc 0 r, diffGen D g (Y s ω) ≤ C' * r := by
      have := setIntegral_mono_on hint (integrableOn_const (by simp)) measurableSet_Icc
        (fun s hs => hgen _ (hYK ω s ⟨hs.1, hs.2.trans hrT⟩ (by rw [hr]; exact_mod_cast hs.2)))
      simpa [Measure.real, hr0, mul_comm] using this
    rw [hZr, heq, hM]
    have : C' * r ≤ C' * T := mul_le_mul_of_nonneg_left hrT hC'
    linarith
  have hgc : ContinuousOn g Kc := hg.continuousOn.mono hKU
  set gm : (Fin N → Euc d) → ℝ := Kc.piecewise g (fun _ => 0) with hgm
  have hgm_meas : Measurable gm :=
    ContinuousOn.measurable_piecewise hgc continuousOn_const hKc.isClosed.measurableSet
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn hgc
  have hgm_bd : ∀ x, ‖gm x‖ ≤ max B 0 := by
    intro x
    by_cases hx : x ∈ Kc
    · rw [hgm, Set.piecewise_eq_of_mem _ _ _ hx]; exact (hB x hx).trans (le_max_left _ _)
    · rw [hgm, Set.piecewise_eq_of_notMem _ _ _ hx]; simp
  have hY₀m : Measurable Y₀ := (hsol.init_meas 0).mono (ℱ.le 0) le_rfl
  have hint1 : Integrable (fun ω => gm (stoppedValue Wp ρ' ω)) P :=
    Integrable.of_bound (hgm_meas.comp hZm).aestronglyMeasurable (max B 0)
      (ae_of_all _ fun ω => hgm_bd _)
  have hint0 : Integrable (fun ω => gm (Y₀ ω)) P :=
    Integrable.of_bound (hgm_meas.comp hY₀m).aestronglyMeasurable (max B 0)
      (ae_of_all _ fun ω => hgm_bd _)
  have hintM : Integrable (stoppedProcess u ρ' T) P := hmart.integrable T
  have h1 : ∫ ω in A, g (stoppedValue Wp ρ' ω) ∂P = ∫ ω in A, gm (stoppedValue Wp ρ' ω) ∂P :=
    setIntegral_congr_fun hAm fun ω hω => by
      simp only [hgm, Set.piecewise_eq_of_mem _ _ _ (hZK ω hω)]
  have h2 : ∫ ω in A, g (Y₀ ω) ∂P = ∫ ω in A, gm (Y₀ ω) ∂P :=
    setIntegral_congr_fun hAm fun ω hω => by
      simp only [hgm, Set.piecewise_eq_of_mem _ _ _ (hAK ω hω)]
  have hM0 : ∫ ω in A, stoppedProcess u ρ' T ω ∂P = 0 := by
    rw [← hmart.setIntegral_eq hT (hA 0)]
    have : ∀ ω ∈ A, stoppedProcess u ρ' 0 ω = 0 := by
      intro ω hω
      simp only [stoppedProcess]
      rw [min_eq_left (by simpa using hρ'nn ω hω)]
      simpa [hu] using itoIntegral_of_nonpos P ℱ W' Ψ (le_refl (0 : ℝ)) ω
    rw [setIntegral_congr_fun hAm this]; simp
  have hae' : ∀ᵐ ω ∂P.restrict A, gm (stoppedValue Wp ρ' ω) ≤
      gm (Y₀ ω) + C' * T + stoppedProcess u ρ' T ω := by
    rw [ae_restrict_iff' hAm]
    filter_upwards [hae] with ω hω hωA
    have := hω hωA
    simpa only [hgm, Set.piecewise_eq_of_mem _ _ _ (hZK ω hωA),
      Set.piecewise_eq_of_mem _ _ _ (hAK ω hωA)] using this
  have e1 : Integrable (fun ω => gm (Y₀ ω) + C' * T) P := hint0.add (integrable_const _)
  have e2 : Integrable (fun ω => gm (Y₀ ω) + C' * T + stoppedProcess u ρ' T ω) P := e1.add hintM
  refine ⟨hint1.integrableOn.congr_fun (fun ω hω => (by
      simp only [hgm, Set.piecewise_eq_of_mem _ _ _ (hZK ω hω)] : gm _ = g _)) hAm,
    hint0.integrableOn.congr_fun (fun ω hω => (by
      simp only [hgm, Set.piecewise_eq_of_mem _ _ _ (hAK ω hω)] : gm _ = g _)) hAm, ?_⟩
  rw [h1, h2]
  calc ∫ ω in A, gm (stoppedValue Wp ρ' ω) ∂P
      ≤ ∫ ω in A, (gm (Y₀ ω) + C' * T + stoppedProcess u ρ' T ω) ∂P :=
        setIntegral_mono_ae_restrict hint1.integrableOn
          e2.integrableOn hae'
    _ = ∫ ω in A, gm (Y₀ ω) ∂P + C' * T * (P A).toReal := by
        rw [integral_add e1.integrableOn hintM.integrableOn,
          integral_add hint0.integrableOn (integrable_const (C' * T)).integrableOn, hM0,
          setIntegral_const]
        simp [Measure.real, mul_comm]

theorem barrier_level_estimate [IsProbabilityMeasure P] (D : DynData d) (hK : KernelLocal d D.s)
    (hV : cep_IsC11 D.V) (hW' : IsBrownianFiltration P ℱ W')
    {Y₀ : Ω → (Fin N → Euc d)} {τ : Ω → WithTop ℝ} {Y : ℝ → Ω → (Fin N → Euc d)}
    (hsol : IsMaximalParticleSolution P ℱ W' D Y₀ τ Y) (I : Finset (Fin N)) (hI : 2 ≤ I.card)
    {q C' : ℝ} (hq : 0 < q) (hC' : 0 ≤ C') {δ : ℝ}
    (hgen : ∀ Z : Fin N → Euc d, (∀ j, j ∉ I → δ ≤ clusterDispersionLift (insert j I) Z) →
      Z ∈ liftedFree d N → diffGen D (barrierPhi q ∘ clusterDispersionLift I) Z ≤ C')
    {T : ℝ} (hT : 0 ≤ T) {a q₁ : ℝ} (ha : 0 < a) (hq₁ : 0 < q₁) (n : ℕ) :
    ∃ B : Set Ω, MeasurableSet B ∧
      (∀ ω, Y₀ ω ∈ barrierK I a δ n → q₁ ≤ clusterDispersionLift I (Y₀ ω) →
        (∃ r : ℝ, 0 ≤ r ∧ r ≤ T ∧ solHit τ Y (barrierG I a δ n) ω = (r : WithTop ℝ) ∧
          clusterDispersionLift I (Y r ω) ≤ a) → ω ∈ B) ∧
      (barrierPhi q a + Real.log (q / 2)) * (P B).toReal ≤
        barrierPhi q (min q₁ (q / 2)) + Real.log (q / 2) + C' * T := by
  classical
  set Kc := barrierK (d := d) I a δ n with hKc_def
  set G := barrierG (d := d) I a δ n with hG_def
  have hKc : IsCompact Kc := isCompact_barrierK I a δ n
  have hG : IsClosed G := isClosed_barrierG I a δ n
  have hGK : Gᶜ ⊆ Kc := barrierG_compl_subset I a δ n
  have hKfree : Kc ⊆ liftedFree d N := barrierK_subset_free I a δ n
  set Φ := barrierPhi q with hΦdef
  set Q := clusterDispersionLift (d := d) (N := N) I with hQdef
  have hQc : Continuous Q := continuous_clusterDispersionLift I
  have hU : IsOpen {Z : Fin N → Euc d | 0 < Q Z} := isOpen_lt continuous_const hQc
  have hKU : Kc ⊆ {Z | 0 < Q Z} := barrierK_subset_pos I ha δ n
  have hg : ContDiffOn ℝ 2 (Φ ∘ Q) {Z | 0 < Q Z} :=
    (barrierPhi_contDiffOn hq).comp (contDiff_two_clusterDispersionLift I).contDiffOn
      (fun Z hZ => hZ)
  have hgenK : ∀ Z ∈ Kc, diffGen D (Φ ∘ Q) Z ≤ C' := fun Z hZ => hgen Z hZ.2 (hKfree hZ)
  set A : Set Ω := Y₀ ⁻¹' (Kc ∩ {Z | q₁ ≤ Q Z}) with hAdef
  have hA : ∀ t : ℝ, MeasurableSet[ℱ t] A := fun t =>
    (hsol.init_meas t) ((hKc.isClosed.inter (isClosed_le continuous_const hQc)).measurableSet)
  have hAK : ∀ ω ∈ A, Y₀ ω ∈ Kc := fun ω hω => hω.1
  obtain ⟨Z, hZm, hZK, hZhit, hintZ, hint0, hineq⟩ := stopped_estimate D hK hV hW' hsol hT hU Kc hKc
    hKU hKfree hg hG hGK hC' hgenK hA hAK
  have hAm : MeasurableSet A := ℱ.le 0 _ (hA 0)
  set R : Set Ω := Z ⁻¹' {W | Q W ≤ a} with hR
  have hRm : MeasurableSet R := hZm (isClosed_le hQc continuous_const).measurableSet
  refine ⟨A ∩ R, hAm.inter hRm, ?_, ?_⟩
  · intro ω h1 h2 ⟨r, hr0, hrT, hhit, hQ⟩
    have hωA : ω ∈ A := ⟨h1, h2⟩
    refine ⟨hωA, ?_⟩
    show Q (Z ω) ≤ a
    rw [hZhit ω hωA r hr0 hrT hhit]; exact hQ
  set m : ℝ := -Real.log (q / 2) with hm
  have hmle : ∀ x, 0 < x → m ≤ Φ x := fun x hx => barrierPhi_ge hq hx
  set c := Φ a - m with hc
  have hc0 : 0 ≤ c := by have := hmle a ha; linarith
  have hanti := barrierPhi_antitoneOn hq
  have hQZpos : ∀ ω ∈ A, 0 < Q (Z ω) := fun ω hω => hKU (hZK ω hω)
  -- lower bound
  have hfint : Integrable (fun ω => m + R.indicator (fun _ => c) ω) P :=
    (integrable_const m).add ((integrable_const c).indicator hRm)
  have hlow : ∫ ω in A, (m + R.indicator (fun _ => c) ω) ∂P ≤ ∫ ω in A, (Φ ∘ Q) (Z ω) ∂P := by
    refine setIntegral_mono_on hfint.integrableOn hintZ hAm fun ω hω => ?_
    by_cases hωR : ω ∈ R
    · rw [Set.indicator_of_mem hωR]
      have : Φ a ≤ Φ (Q (Z ω)) := hanti (show Q (Z ω) ∈ Set.Ioi 0 from hQZpos ω hω)
        (show a ∈ Set.Ioi 0 from ha) hωR
      simp only [hc, Function.comp]; linarith
    · rw [Set.indicator_of_notMem hωR]
      simpa using hmle _ (hQZpos ω hω)
  have hlow' : ∫ ω in A, (m + R.indicator (fun _ => c) ω) ∂P =
      m * (P A).toReal + c * (P (A ∩ R)).toReal := by
    rw [integral_add (integrable_const m).integrableOn
      ((integrable_const c).indicator hRm).integrableOn, setIntegral_const,
      setIntegral_indicator hRm, setIntegral_const]
    simp [Measure.real, mul_comm]
  -- upper bound on the initial value
  set c₁ := Φ (min q₁ (q / 2)) with hc₁
  have hmin0 : 0 < min q₁ (q / 2) := lt_min hq₁ (by linarith)
  have hupp : ∫ ω in A, (Φ ∘ Q) (Y₀ ω) ∂P ≤ c₁ * (P A).toReal := by
    have : ∫ ω in A, (Φ ∘ Q) (Y₀ ω) ∂P ≤ ∫ ω in A, c₁ ∂P := by
      refine setIntegral_mono_on hint0 (integrableOn_const (by simp)) hAm fun ω hω => ?_
      have hQ : min q₁ (q / 2) ≤ Q (Y₀ ω) := (min_le_left _ _).trans hω.2
      exact hanti (show min q₁ (q / 2) ∈ Set.Ioi 0 from hmin0)
        (show Q (Y₀ ω) ∈ Set.Ioi 0 from lt_of_lt_of_le hmin0 hQ) hQ
    simpa [Measure.real, mul_comm] using this
  have hc₁m : m ≤ c₁ := hmle _ hmin0
  have hX1 : (P A).toReal ≤ 1 := measureReal_le_one
  have hX0 : 0 ≤ (P A).toReal := ENNReal.toReal_nonneg
  have hK0 : 0 ≤ c₁ - m + C' * T := by have := mul_nonneg hC' hT; linarith
  have hfin : c * (P (A ∩ R)).toReal ≤ (c₁ - m + C' * T) * (P A).toReal := by
    have h1 := hlow.trans hineq
    rw [hlow'] at h1
    have : C' * T * (P A).toReal = C' * T * (P A).toReal := rfl
    nlinarith [hupp]
  have : (c₁ - m + C' * T) * (P A).toReal ≤ c₁ - m + C' * T :=
    mul_le_of_le_one_right hK0 hX1
  simp only [hc, hm, hc₁] at hfin this ⊢
  linarith

end HRS.MC.CepS1
