import HRS.Main.MeanPartShiftB
import HRS.Main.MeanPartShiftC
import HRS.Main.MeanPartMetricB
import HRS.Main.MeanPartPrep
import HRS.Main.MeanPartFlow

/-!
# Corollary 5.17 (`mean_particles`), parts (a) and (b): helpers and the core lemma

(packet `mpfinal`, plan `docs/MAIN_A_PLAN_mean_particles.md`, "Assembly A".)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

/-- Transport of the stationary Gaussian field predicate along equalities of the parameters. -/
theorem mpfin_transport_field {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {s' s β' β : ℝ}
    {hs0' : 0 ≤ s'} {hsd' : s' < d} {hβ' : 0 < β'} {hs0 : 0 ≤ s} {hsd : s < d} {hβ : 0 < β}
    {V' V ρβ : Torus d → ℝ} {m : ℝ} {Z : ℝ → Ω → NegSobolev d m}
    (e1 : s' = s) (e2 : β' = β) (e3 : V' = V)
    (h : IsStationaryGaussianField P s' β' hs0' hsd' hβ' V' ρβ m Z) :
    IsStationaryGaussianField P s β hs0 hsd hβ V ρβ m Z := by
  subst e1 e2 e3
  exact h

/-- Transport of the dynamics along equalities of the parameters. -/
theorem mpfin_dyn_eq {s' s β' β : ℝ} {hs0' : 0 ≤ s'} {hsd' : s' < d} {hβ' : 0 < β'}
    {hs0 : 0 ≤ s} {hsd : s < d} {hβ : 0 < β} {V' V : Torus d → ℝ}
    (e1 : s' = s) (e2 : β' = β) (e3 : V' = V) :
    PDE.mfData d s' hs0' hsd' V' β' hβ' = PDE.mfData d s hs0 hsd V β hβ := by
  subst e1 e2 e3
  rfl

theorem mpfin_prob_map {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → E} (hf : AEMeasurable f P) : IsProbabilityMeasure (law P f) :=
  (Measure.isProbabilityMeasure_map_iff hf).2 inferInstance

/-- The `η`-window is a.e. measurable. -/
theorem mpfin_eta_aem (S : PreparedData d) {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (hN : 1 ≤ N) (P : Measure Ω) (X : ℝ≥0 → Ω → Config d N) (hXm : ∀ t, Measurable (X t))
    (hXc : ∀ᵐ ω ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ω i) {m : ℝ} (hm2 : (d : ℝ) < 2 * m)
    {a : ℝ} (ha : 0 ≤ a) {T : ℝ} (hT : 0 ≤ T) :
    AEMeasurable (windowFluc m T a (Real.sqrt N) X S.ρ) P := by
  have hW : AEMeasurable (windowFluc m T a (Real.sqrt N) X (fun _ _ => (1 : ℝ))) P :=
    mp_window_aemeasurable hN P X hXm hXc hm2 ha hT (Real.sqrt N) mp_isProbDensity_one
  have hae : ∀ᵐ ω ∂P, windowFluc m T a (Real.sqrt N) X (fun _ _ => (1 : ℝ)) ω =
      windowFluc m T a (Real.sqrt N) X S.ρ ω + mp_Dp S hm2 T a ha (Real.sqrt N) := by
    filter_upwards [hXc] with ω hω
    exact therm_window_eq S T a hm2 hN ha (Real.sqrt N) mp_isProbDensity_one X ω hω
  refine (hW.sub_const (mp_Dp S hm2 T a ha (Real.sqrt N))).congr ?_
  filter_upwards [hae] with ω hω
  simp [hω]

theorem mpfin_etaLaw_prob (S : PreparedData d) {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    (hN : 1 ≤ N) (P : Measure Ω) (X : ℝ≥0 → Ω → Config d N) (hXm : ∀ t, Measurable (X t))
    (hXc : ∀ᵐ ω ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ω i) {m : ℝ} (hm2 : (d : ℝ) < 2 * m)
    {a : ℝ} (ha : 0 ≤ a) {T : ℝ} (hT : 0 ≤ T) [IsProbabilityMeasure P] :
    IsProbabilityMeasure (S.etaLaw m T a P X) := by
  unfold PreparedData.etaLaw law
  exact mpfin_prob_map (mpfin_eta_aem S hN P X hXm hXc hm2 ha hT)

theorem mpfin_windowPath_zero (m T : ℝ) {Ω : Type*} (Z : ℝ → Ω → NegSobolev d m) :
    windowPath m T 0 Z = toPath m T Z := by
  funext ω
  simp [windowPath]

/-- The path `0` as a shift path. -/
theorem mpfin_shiftPath_zero (m T : ℝ) (h : ContinuousOn (fun _ : ℝ => (0 : NegSobolev d m)) (Set.Icc 0 T)) :
    mp_shiftPath m T (fun _ => (0 : NegSobolev d m)) h = 0 := by
  refine ContinuousMap.ext fun t => ?_
  rfl

/-- The Wasserstein convergence `W₁(η-window law, window of Z) → 0` for the prepared data. -/
theorem mpfin_W1 {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (hs : s < 2 * (d : ℝ) / 3) (hβ : 0 < β) (k : Lattice d) (ε : ℝ)
    (ρ : ℝ → Torus d → ℝ) (hρ0 : ρ 0 = fun x => 1 + ε * PDE.cosTest k x) (β₀ : ℝ)
    (hβ₀ : 0 ≤ β₀) (PS : ParticleSeq d)
    (hS : ∀ T' : ℝ, 0 ≤ T' → PS.IsSolutionOn (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) T')
    (hSF : ∀ n, ∃ (ℱ : MeasureTheory.Filtration ℝ (PS.mΩ n))
      (W' : ℝ≥0 → PS.Ω n → (Fin (n + 2) × Fin d) → ℝ),
      IsFilteredSolution (PS.P n) ℱ W' (PS.W n) (PS.X n))
    (hinit : ∀ n, (PS.P n).map (PS.X₀ n) =
      modulatedGibbs (periodicRiesz d s) (n + 2) β₀ (withDensityReal (ρ 0)))
    (S : PreparedData d) (hSs : S.s = s) (hSβ : S.β = β) (hSV : S.V = fun _ => 0)
    (hSρ0 : S.ρ0 = fun x => 1 + ε * PDE.cosTest k x)
    (T : ℝ) (hT : 0 < T) (m : ℝ) (hm : (d : ℝ) + 2 < m) (u : ℕ → ℝ) (hu0 : ∀ n, 0 ≤ u n)
    (hu : Tendsto u atTop atTop)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : ℝ → Ω' → NegSobolev d m)
    (hZ : IsStationaryGaussianField P' s β hs0 hsd hβ (fun _ => 0) (fun _ => 1) m Z) :
    Tendsto (fun n : ℕ => wassersteinE 1 (S.etaLaw m T (u n) (PS.P n) (PS.X n))
        (law P' (windowPath m T 0 Z))) atTop (𝓝 0) := by
  have hdyn : S.dyn = PDE.mfData d s hs0 hsd (fun _ => 0) β hβ :=
    mpfin_dyn_eq hSs hSβ hSV
  have hZ' : IsStationaryGaussianField P' S.s S.β S.hs0 S.hsd S.hβ S.V (fun _ => 1) m Z :=
    mpfin_transport_field P' hSs.symm hSβ.symm hSV.symm hZ
  have hρβ : IsThermalDensity (periodicRiesz d S.s) S.V S.β (fun _ => (1 : ℝ)) := by
    rw [hSV]; exact mp_thermalDensity_one _ _
  have hρ0S : S.ρ0 = ρ 0 := by rw [hSρ0, hρ0]
  exact mp_therm_seq hs0 hsd hβ ρ S hdyn hρ0S hs m hm T hT (fun _ => 1)
    hρβ β₀ hβ₀ u hu0 hu PS hS hSF hinit P' Z hZ'

/-- **Core of parts (a), (b)**: convergence in distribution to the stationary field plus a
deterministic continuous shift, given convergence of the deterministic part of the window. -/
theorem mpfin_ab_core (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (hs : s < 2 * (d : ℝ) / 3) (hβ : 0 < β) (k : Lattice d) (ε : ℝ)
    (ρ : ℝ → Torus d → ℝ) (hρ0 : ρ 0 = fun x => 1 + ε * PDE.cosTest k x) (β₀ : ℝ)
    (hβ₀ : 0 ≤ β₀) (PS : ParticleSeq d)
    (hS : ∀ T' : ℝ, 0 ≤ T' → PS.IsSolutionOn (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) T')
    (hSF : ∀ n, ∃ (ℱ : MeasureTheory.Filtration ℝ (PS.mΩ n))
      (W' : ℝ≥0 → PS.Ω n → (Fin (n + 2) × Fin d) → ℝ),
      IsFilteredSolution (PS.P n) ℱ W' (PS.W n) (PS.X n))
    (hinit : ∀ n, (PS.P n).map (PS.X₀ n) =
      modulatedGibbs (periodicRiesz d s) (n + 2) β₀ (withDensityReal (ρ 0)))
    (S : PreparedData d) (hSs : S.s = s) (hSβ : S.β = β) (hSV : S.V = fun _ => 0)
    (hSρ0 : S.ρ0 = fun x => 1 + ε * PDE.cosTest k x)
    (T : ℝ) (hT : 0 ≤ T) (m : ℝ) (hm : (d : ℝ) + 2 < m) (u : ℕ → ℝ) (hu0 : ∀ n, 0 ≤ u n)
    (hu : Tendsto u atTop atTop)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : ℝ → Ω' → NegSobolev d m)
    (hZ : IsStationaryGaussianField P' s β hs0 hsd hβ (fun _ => 0) (fun _ => 1) m Z)
    (sh : ℝ → NegSobolev d m) (hsh : Continuous sh)
    (hDp : Tendsto (fun n : ℕ =>
      ‖mp_Dp S (show (d : ℝ) < 2 * m by
          have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
          linarith) (T + 1) (u n) (hu0 n) (Real.sqrt ((n + 2 : ℕ) : ℝ)) -
        mp_shiftPath m (T + 1) sh hsh.continuousOn‖) atTop (𝓝 0)) :
    TendstoInDistribution
      (fun n ω => flucPath m T (Real.sqrt ((n + 2 : ℕ) : ℝ))
        (fun t ω' => PS.X n ((u n).toNNReal + t) ω') (fun _ _ => (1 : ℝ)) ω) atTop
      (toPath m T (fun t ω' => Z t ω' + sh t)) PS.P P' := by
  have hm2 : (d : ℝ) < 2 * m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hsol : ∀ n, IsStrongSolution (PS.P n) (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) 0
      (PS.X₀ n) (PS.W n) (PS.X n) := fun n => (hS 0 le_rfl n).sol
  have hXm : ∀ n t, Measurable (PS.X n t) := fun n t => (hsol n).adapted t
  have hXc : ∀ n, ∀ᵐ ω ∂(PS.P n), ∀ i, Continuous fun t : ℝ≥0 => PS.X n t ω i :=
    fun n => (hsol n).cont
  set X' : ∀ n, ℝ≥0 → PS.Ω n → Config d (n + 2) :=
    fun n t ω' => PS.X n ((u n).toNNReal + t) ω' with hX'
  have hXc' : ∀ n, ∀ᵐ ω ∂(PS.P n), ∀ i, Continuous fun t : ℝ≥0 => X' n t ω i := fun n =>
    (hXc n).mono fun ω h i => (h i).comp (continuous_const.add continuous_id)
  have hW := mpfin_W1 hs0 hsd hs hβ k ε ρ hρ0 β₀ hβ₀ PS hS hSF hinit S hSs hSβ hSV hSρ0
    (T + 1) (by linarith) m hm u hu0 hu P' Z hZ
  have hZc : ∀ᵐ ω ∂P', ContinuousOn (fun t => Z t ω) (Set.Icc 0 (T + 1)) :=
    hZ.cont.mono fun ω h => h.mono Set.Icc_subset_Ici_self
  have hYc : ∀ᵐ ω ∂P', ContinuousOn (fun t => Z t ω + sh t) (Set.Icc 0 (T + 1)) :=
    hZc.mono fun ω h => h.add hsh.continuousOn
  have key : TendstoInDistribution
      (fun n ω => flucPath m (T + 1) (Real.sqrt ((n + 2 : ℕ) : ℝ)) (X' n) (fun _ _ => (1 : ℝ)) ω)
      atTop (toPath m (T + 1) (fun t ω' => Z t ω' + sh t)) PS.P P' := by
    refine mp_tendstoInDistribution_of_wE1 _ _ PS.P P' (fun n => ?_)
      (mp_toPath_add_const_aemeasurable P' m (T + 1) Z hZ.meas hZc sh hsh.continuousOn) ?_
    · exact mp_window_aemeasurable (by omega) (PS.P n) (PS.X n) (hXm n) (hXc n) hm2 (hu0 n)
        (by linarith) (Real.sqrt ((n + 2 : ℕ) : ℝ)) mp_isProbDensity_one
    · -- the Wasserstein estimate
      have hQprob : IsProbabilityMeasure (law P' (windowPath m (T + 1) 0 Z)) := by
        rw [mpfin_windowPath_zero]
        have := mp_toPath_add_const_aemeasurable P' m (T + 1) Z hZ.meas hZc (fun _ => 0)
          continuousOn_const
        exact mpfin_prob_map (by simpa using this)
      have hle : ∀ n : ℕ, wassersteinE 1
          (law (PS.P n) (fun ω => flucPath m (T + 1) (Real.sqrt ((n + 2 : ℕ) : ℝ)) (X' n)
            (fun _ _ => (1 : ℝ)) ω))
          (law P' (toPath m (T + 1) (fun t ω' => Z t ω' + sh t))) ≤
          wassersteinE 1 (S.etaLaw m (T + 1) (u n) (PS.P n) (PS.X n))
            (law P' (windowPath m (T + 1) 0 Z)) +
          ENNReal.ofReal ‖mp_Dp S hm2 (T + 1) (u n) (hu0 n) (Real.sqrt ((n + 2 : ℕ) : ℝ)) -
            mp_shiftPath m (T + 1) sh hsh.continuousOn‖ := by
        intro n
        haveI := mpfin_etaLaw_prob S (N := n + 2) (by omega) (PS.P n) (PS.X n) (hXm n) (hXc n)
          hm2 (hu0 n) (show (0 : ℝ) ≤ T + 1 by linarith)
        have e1 := mp_window_eq_map S (N := n + 2) (by omega) (PS.P n) (PS.X n) (hXm n) (hXc n) hm2
          (hu0 n) (show (0 : ℝ) ≤ T + 1 by linarith)
        have e2 := mp_law_toPath_add_const P' m (T + 1) Z hZ.meas hZc sh hsh.continuousOn
        rw [mpfin_windowPath_zero]
        have e3 : law P' (toPath m (T + 1) Z) = law P' (toPath m (T + 1) Z) := rfl
        refine le_trans (le_of_eq ?_) (mp_wE_translate2 (S.etaLaw m (T + 1) (u n) (PS.P n) (PS.X n))
          (law P' (toPath m (T + 1) Z)) (mp_Dp S hm2 (T + 1) (u n) (hu0 n)
            (Real.sqrt ((n + 2 : ℕ) : ℝ))) (mp_shiftPath m (T + 1) sh hsh.continuousOn) 1 le_rfl)
        rw [e2]
        exact congrArg₂ _ e1 rfl
      have hup : Tendsto (fun n : ℕ => wassersteinE 1 (S.etaLaw m (T + 1) (u n) (PS.P n) (PS.X n))
            (law P' (windowPath m (T + 1) 0 Z)) +
          ENNReal.ofReal ‖mp_Dp S hm2 (T + 1) (u n) (hu0 n) (Real.sqrt ((n + 2 : ℕ) : ℝ)) -
            mp_shiftPath m (T + 1) sh hsh.continuousOn‖) atTop (𝓝 0) := by
        have h2 := (ENNReal.tendsto_ofReal hDp)
        rw [ENNReal.ofReal_zero] at h2
        simpa using hW.add h2
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
        (fun _ => zero_le) hle
  exact mp_restrict_T hm2 (show T ≤ T + 1 by linarith) PS.P X' hXc' P' (fun t ω' => Z t ω' + sh t)
    hYc key

end Main

end HRS
