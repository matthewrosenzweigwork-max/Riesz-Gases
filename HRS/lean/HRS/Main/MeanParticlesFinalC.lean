import HRS.Main.MeanParticlesFinalA
import HRS.Main.MeanPartMetricEval

/-!
# Corollary 5.17 (`mean_particles`), part (c): the early windows

(packet `mpfinal`, plan `docs/MAIN_A_PLAN_mean_particles.md`, "Assembly C".)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

/-- Evaluation against `ψ_k` as a linear functional on `E_m`. -/
def mpfin_ell0 (m : ℝ) (k : Lattice d) (hk : k ≠ 0) : NegSobolev d m →ₗ[ℝ] ℝ where
  toFun F := NegSobolev.eval F (PDE.cosTest k)
  map_add' F G := by
    obtain ⟨K, -, hK⟩ := mp_eval_cosTest_eq (m := m) k hk
    rw [hK, hK, hK]
    unfold NegSobolev.fourierCoeff
    have : NegSobolev.coord (F + G) K = NegSobolev.coord F K + NegSobolev.coord G K := rfl
    rw [this]; ring
  map_smul' c F := by
    rw [mp_eval_smul]
    rfl

/-- The observation `w ↦ w^0(ψ_k)` on the path space, as a continuous linear functional. -/
def mpfin_ell (m T : ℝ) (hT : 0 ≤ T) (k : Lattice d) (hk : k ≠ 0) : PathSpace d m T →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun w => mpfin_ell0 m k hk (PathSpace.at' w ⟨0, le_rfl, hT⟩)
      map_add' := fun w w' => by
        rw [← map_add]; rfl
      map_smul' := fun c w => by
        rw [← map_smul]; rfl }
    (Lattice.jp k ^ m) (fun w => by
      show |NegSobolev.eval (PathSpace.at' w ⟨0, le_rfl, hT⟩) (PDE.cosTest k)| ≤ _
      refine (mp_abs_eval_cosTest_le k hk _).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_pos_of_pos (Torus.jp_pos k) m).le
      exact ContinuousMap.norm_coe_le_norm (show C(Set.Icc (0 : ℝ) T, NegSobolev d m) from w)
        ⟨0, le_rfl, hT⟩)

theorem mpfin_ell_apply (m T : ℝ) (hT : 0 ≤ T) (k : Lattice d) (hk : k ≠ 0) (w : PathSpace d m T) :
    mpfin_ell m T hT k hk w = NegSobolev.eval (PathSpace.at' w ⟨0, le_rfl, hT⟩) (PDE.cosTest k) :=
  rfl

/-- At time `0` the `η`-window is the scaled fluctuation around `ρ^a`. -/
theorem mpfin_window_zero (S : PreparedData d) {Ω : Type*} {N : ℕ} (hN : 1 ≤ N)
    {m : ℝ} (hm2 : (d : ℝ) < 2 * m) {a : ℝ} (ha : 0 ≤ a) {T : ℝ} (hT : 0 ≤ T) (σ : ℝ)
    (X : ℝ≥0 → Ω → Config d N) (ω : Ω) (hc : ∀ i, Continuous fun t : ℝ≥0 => X t ω i) :
    PathSpace.at' (windowFluc m T a σ X S.ρ ω) ⟨0, le_rfl, hT⟩ =
      NegSobolev.scaledFluc m σ (X (Real.toNNReal a) ω) (withDensityReal (S.ρ a)) := by
  haveI : ∀ t : Set.Icc (0 : ℝ) T, IsProbabilityMeasure (withDensityReal (S.ρ (a + t))) :=
    therm_prob_rho S T a ha
  have hXp : Continuous fun t : Set.Icc (0 : ℝ) T => X (Real.toNNReal a + Real.toNNReal t) ω :=
    continuous_pi fun i => (hc i).comp
      (continuous_const.add (continuous_real_toNNReal.comp continuous_subtype_val))
  have hE := therm_cont_emp T hm2 hN σ
    (fun t => X (Real.toNNReal a + Real.toNNReal t) ω) hXp
    (fun t => withDensityReal (S.ρ (a + t))) (therm_coeff_cont S T a ha)
  have e1 : windowFluc m T a σ X S.ρ ω = (show PathSpace d m T from
      (⟨fun t : Set.Icc (0 : ℝ) T => σ • NegSobolev.ofMeasureDiff m
          (empirical (X (Real.toNNReal a + Real.toNNReal t) ω)) (withDensityReal (S.ρ (a + t))), hE⟩ :
        C(Set.Icc (0 : ℝ) T, NegSobolev d m))) := by
    unfold windowFluc flucPath
    exact dif_pos hE
  rw [e1]
  show σ • NegSobolev.ofMeasureDiff m (empirical (X (Real.toNNReal a + Real.toNNReal 0) ω))
      (withDensityReal (S.ρ (a + 0))) = _
  simp [NegSobolev.scaledFluc]

/-- The integral identity `∫ ρ ψ = ∫ ψ (ρ - 1)`. -/
theorem mpfin_int_eq (k : Lattice d) (hk : k ≠ 0) {ρu : Torus d → ℝ} (hρu : Continuous ρu) :
    ∫ x, ρu x * PDE.cosTest k x = ∫ x, PDE.cosTest k x * (ρu x - 1) := by
  have hψ : Continuous (PDE.cosTest k : Torus d → ℝ) := mp_cosTest_continuous k
  have h1 : Integrable (fun x : Torus d => ρu x * PDE.cosTest k x) :=
    (hρu.mul hψ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h2 : Integrable (fun x : Torus d => PDE.cosTest k x) :=
    hψ.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have : (fun x : Torus d => PDE.cosTest k x * (ρu x - 1)) =
      fun x => ρu x * PDE.cosTest k x - PDE.cosTest k x := by
    funext x; ring
  rw [this, integral_sub h1 h2, mp_integral_cosTest k hk, sub_zero]

/-- **Core of part (c)**. -/
theorem mpfin_c_core (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (hs : s < 2 * (d : ℝ) / 3) (hβ : 0 < β) (k : Lattice d) (hk : k ≠ 0) (ε : ℝ)
    (ρ : ℝ → Torus d → ℝ) (hρ0 : ρ 0 = fun x => 1 + ε * PDE.cosTest k x)
    (hρsm : ∀ t : ℝ, 0 ≤ t → Torus.IsSmooth (ρ t)) (β₀ : ℝ)
    (hβ₀ : 0 ≤ β₀) (PS : ParticleSeq d)
    (hS : ∀ T' : ℝ, 0 ≤ T' → PS.IsSolutionOn (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) T')
    (hSF : ∀ n, ∃ (ℱ : MeasureTheory.Filtration ℝ (PS.mΩ n))
      (W' : ℝ≥0 → PS.Ω n → (Fin (n + 2) × Fin d) → ℝ),
      IsFilteredSolution (PS.P n) ℱ W' (PS.W n) (PS.X n))
    (hinit : ∀ n, (PS.P n).map (PS.X₀ n) =
      modulatedGibbs (periodicRiesz d s) (n + 2) β₀ (withDensityReal (ρ 0)))
    (S : PreparedData d) (hSs : S.s = s) (hSβ : S.β = β) (hSV : S.V = fun _ => 0)
    (hSρ0 : S.ρ0 = fun x => 1 + ε * PDE.cosTest k x) (hSρ : ∀ t, 0 ≤ t → S.ρ t = ρ t)
    (m : ℝ) (hm : (d : ℝ) + 2 < m) (u : ℕ → ℝ) (hu0 : ∀ n, 0 ≤ u n)
    (hu : Tendsto u atTop atTop)
    (hδ : Tendsto (fun n : ℕ => Real.sqrt ((n + 2 : ℕ) : ℝ) *
      ∫ x, PDE.cosTest k x * (ρ (u n) x - 1)) atTop atTop)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : ℝ → Ω' → NegSobolev d m)
    (hZ : IsStationaryGaussianField P' s β hs0 hsd hβ (fun _ => 0) (fun _ => 1) m Z) (M : ℝ) :
    Tendsto (fun n : ℕ => PS.P n {ω | linCoord (volume : Measure (Torus d))
          (PDE.cosTest k) (PS.X n (u n).toNNReal ω) ≤ M}) atTop (𝓝 0) := by
  have hm2 : (d : ℝ) < 2 * m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hsol : ∀ n, IsStrongSolution (PS.P n) (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) 0
      (PS.X₀ n) (PS.W n) (PS.X n) := fun n => (hS 0 le_rfl n).sol
  have hXm : ∀ n t, Measurable (PS.X n t) := fun n t => (hsol n).adapted t
  have hXc : ∀ n, ∀ᵐ ω ∂(PS.P n), ∀ i, Continuous fun t : ℝ≥0 => PS.X n t ω i :=
    fun n => (hsol n).cont
  have hW := mpfin_W1 hs0 hsd hs hβ k ε ρ hρ0 β₀ hβ₀ PS hS hSF hinit S hSs hSβ hSV hSρ0
    1 one_pos m hm u hu0 hu P' Z hZ
  have hZc : ∀ᵐ ω ∂P', ContinuousOn (fun t => Z t ω) (Set.Icc 0 1) :=
    hZ.cont.mono fun ω h => h.mono Set.Icc_subset_Ici_self
  have hQm : AEMeasurable (windowPath m 1 0 Z) P' := by
    rw [mpfin_windowPath_zero]
    have := mp_toPath_add_const_aemeasurable P' m 1 Z hZ.meas hZc (fun _ => 0)
      continuousOn_const
    simpa using this
  have hQprob : IsProbabilityMeasure (law P' (windowPath m 1 0 Z)) :=
    mpfin_prob_map hQm
  have hT1 : (0 : ℝ) ≤ 1 := zero_le_one
  set ℓ := mpfin_ell m 1 hT1 k hk with hℓ
  have hηm : ∀ n, AEMeasurable (windowFluc m 1 (u n) (Real.sqrt ((n + 2 : ℕ) : ℝ)) (PS.X n) S.ρ)
      (PS.P n) := fun n =>
    mpfin_eta_aem S (N := n + 2) (by omega) (PS.P n) (PS.X n) (hXm n) (hXc n) hm2 (hu0 n) hT1
  have hprob : ∀ n, IsProbabilityMeasure (S.etaLaw m 1 (u n) (PS.P n) (PS.X n)) := fun n =>
    mpfin_etaLaw_prob S (N := n + 2) (by omega) (PS.P n) (PS.X n) (hXm n) (hXc n) hm2 (hu0 n) hT1
  set ξ : ∀ n, PS.Ω n → ℝ := fun n ω =>
    ℓ (windowFluc m 1 (u n) (Real.sqrt ((n + 2 : ℕ) : ℝ)) (PS.X n) S.ρ ω) with hξ
  set ζ : Ω' → ℝ := fun ω => ℓ (windowPath m 1 0 Z ω) with hζ
  set δ : ℕ → ℝ := fun n => Real.sqrt ((n + 2 : ℕ) : ℝ) *
      ∫ x, PDE.cosTest k x * (ρ (u n) x - 1) with hδdef
  have hW' : Tendsto (fun n => wassersteinE 1 (law (PS.P n) (ξ n)) (law P' ζ)) atTop (𝓝 0) := by
    have hle : ∀ n, wassersteinE 1 (law (PS.P n) (ξ n)) (law P' ζ) ≤
        ENNReal.ofReal ‖ℓ‖ * wassersteinE 1 (S.etaLaw m 1 (u n) (PS.P n) (PS.X n))
          (law P' (windowPath m 1 0 Z)) := fun n => by
      haveI := hprob n
      have e1 : law (PS.P n) (ξ n) = (S.etaLaw m 1 (u n) (PS.P n) (PS.X n)).map ℓ := by
        unfold PreparedData.etaLaw law
        exact (AEMeasurable.map_map_of_aemeasurable ℓ.continuous.aemeasurable (hηm n)).symm
      have e2 : law P' ζ = (law P' (windowPath m 1 0 Z)).map ℓ := by
        unfold law
        exact (AEMeasurable.map_map_of_aemeasurable ℓ.continuous.aemeasurable hQm).symm
      rw [e1, e2]
      exact mp_wE_map_clm ℓ _ _ 1 one_pos
    have hup : Tendsto (fun n => ENNReal.ofReal ‖ℓ‖ * wassersteinE 1
        (S.etaLaw m 1 (u n) (PS.P n) (PS.X n)) (law P' (windowPath m 1 0 Z))) atTop (𝓝 0) := by
      have h := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal ‖ℓ‖) hW (Or.inr ENNReal.ofReal_ne_top)
      rwa [mul_zero] at h
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
      (fun _ => zero_le) hle
  have hlow := mp_lowerTail PS.P P' ξ ζ (fun n => ℓ.continuous.measurable.comp_aemeasurable (hηm n))
    (ℓ.continuous.measurable.comp_aemeasurable hQm) δ hW' hδ M
  refine hlow.congr fun n => ?_
  refine measure_congr ?_
  -- the two events agree a.e.
  have hρd : IsProbDensity (S.ρ (u n)) := therm_density S (hu0 n)
  have hρc : Continuous (S.ρ (u n)) := by
    rw [hSρ _ (hu0 n)]
    exact StaticLimitAux.continuous_of_smooth (hρsm _ (hu0 n))
  filter_upwards [hXc n] with ω hω
  haveI : IsProbabilityMeasure (withDensityReal (S.ρ (u n))) := HRS.isProb_withDensityReal hρd
  have e := mp_linCoord_cosTest (m := m) hm2 (N := n + 2) (by omega) k hk (S.ρ (u n))
    hρd.measurable hρd.nonneg (PS.X n (u n).toNNReal ω)
  have e0 := mpfin_window_zero S (N := n + 2) (by omega) hm2 (hu0 n) hT1
    (Real.sqrt ((n + 2 : ℕ) : ℝ)) (PS.X n) ω hω
  have eξ : ξ n ω = NegSobolev.eval (NegSobolev.scaledFluc m (Real.sqrt ((n + 2 : ℕ) : ℝ))
      (PS.X n (u n).toNNReal ω) (withDensityReal (S.ρ (u n)))) (PDE.cosTest k) := by
    simp only [hξ, hℓ, mpfin_ell_apply, e0]
  have eδ : δ n = Real.sqrt ((n + 2 : ℕ) : ℝ) * ∫ x, S.ρ (u n) x * PDE.cosTest k x := by
    simp only [hδdef]
    rw [mpfin_int_eq k hk hρc, hSρ _ (hu0 n)]
  have hlin : linCoord (volume : Measure (Torus d)) (PDE.cosTest k)
      (PS.X n (u n).toNNReal ω) = ξ n ω + δ n := by rw [e, eξ, eδ]
  show (ξ n ω + δ n ≤ M) = (linCoord (volume : Measure (Torus d)) (PDE.cosTest k)
      (PS.X n (u n).toNNReal ω) ≤ M)
  rw [hlin]

end Main

end HRS
