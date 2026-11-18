import HRS.Main.MeanPartFlowA

/-!
# MEANPART (flow): L2 `mp_selectedFlow` and L3 `mp_therm_seq`

(packet `mpflow`, plan `docs/MAIN_A_PLAN_mean_particles.md`, section 4.)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

theorem mp_symNonpos_neg_one : Torus.SymNonpos (-1 : Matrix (Fin d) (Fin d) ℝ) := by
  unfold Torus.SymNonpos Torus.symPart
  have : (1 / 2 : ℝ) • ((-1 : Matrix (Fin d) (Fin d) ℝ) + (-1 : Matrix (Fin d) (Fin d) ℝ).transpose)
      = -1 := by
    rw [Matrix.transpose_neg, Matrix.transpose_one,
      ← two_smul ℝ (-1 : Matrix (Fin d) (Fin d) ℝ), smul_smul]
    norm_num
  rw [this, neg_neg]
  exact Matrix.PosSemidef.one

/-- Re-initialising a strong solution at `X 0` is harmless (the initial datum only enters through
the field `init`, which is then trivial). -/
theorem mp_isStrongSolution_reinit {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {D : DynData d}
    {T : ℝ} {N : ℕ} {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Config d N} (h : IsStrongSolution P D T X₀ W X) :
    IsStrongSolution P D T (X 0) W X :=
  ⟨h.lift, Filter.Eventually.of_forall fun _ => rfl, h.cont, h.adapted, h.no_collision⟩

/-- **L2** (general dynamics): for a particle system on `[0,T']`, `T' > 0`, with `N = n + 2 ≥ 2`
particles, `d ≥ 2`, `Sym M ≤ 0`, `V ∈ C²`, the process `X` is a selected flow for the
(measurable) initial datum `X 0`. -/
theorem mp_selectedFlow_gen (hd : 2 ≤ d) (D : DynData d) (hM : Torus.SymNonpos D.M)
    (hV : Torus.IsCk 2 D.V) (PS : ParticleSeq d) (T' : ℝ) (hT' : 0 < T')
    (hS : PS.IsSolutionOn D T') (n : ℕ) :
    SelectedFlow (PS.P n) D T' (PS.X n 0) (PS.W n) (PS.X n) := by
  have h := hS n
  have hsol := h.sol
  have hmeas : Measurable (PS.X n 0) := hsol.adapted 0
  have hdist : ∀ᵐ ω ∂(PS.P n), PS.X n 0 ω ∉ collisionSet d (n + 2) := by
    filter_upwards [hsol.no_collision] with ω hω
    exact hω 0 (by simpa using hT'.le)
  have hind : IndepFun (PS.X n 0) (fun ω => fun t : ℝ≥0 => PS.W n t ω) (PS.P n) :=
    h.indep.congr (by filter_upwards [hsol.init] with ω hω using hω.symm) (Filter.EventuallyEq.refl _ _)
  refine ⟨hmeas, hdist, h.brownian, hind, Or.inl ⟨mp_isStrongSolution_reinit hsol, ?_⟩⟩
  exact (particle_wellposed_proof (PS.P n) D hd (by omega) hM hV (PS.X n 0) hmeas hdist (PS.W n)
    h.brownian hind T' hT').2

/-- The initial law is unchanged when `X₀` is replaced by `X 0`. -/
theorem mp_law_X0 (D : DynData d) (PS : ParticleSeq d) (T' : ℝ) (hS : PS.IsSolutionOn D T')
    (n : ℕ) : (PS.P n).map (PS.X n 0) = (PS.P n).map (PS.X₀ n) := by
  have hsol := (hS n).sol
  exact Measure.map_congr hsol.init

/-- **L2** for the mean-field dynamics `PDE.mfData` with `V = 0`: from the hypotheses `hS` of
`mean_particles` to `SelectedFlow` for the dynamics of an abstract `S : PreparedData d` whose
`dyn` is `PDE.mfData d s hs0 hsd (fun _ => 0) β hβ`. -/
theorem mp_selectedFlow (hd : 2 ≤ d) {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (S : PreparedData d)
    (hdyn : S.dyn = PDE.mfData d s hs0 hsd (fun _ => 0) β hβ)
    (PS : ParticleSeq d) (T' : ℝ) (hT' : 0 < T')
    (hS : PS.IsSolutionOn (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) T') (n : ℕ) :
    SelectedFlow (PS.P n) S.dyn T' (PS.X n 0) (PS.W n) (PS.X n) := by
  rw [hdyn]
  refine mp_selectedFlow_gen hd _ ?_ ?_ PS T' hT' hS n
  · exact mp_symNonpos_neg_one
  · exact mova_isCk_const 2 0

/-- **L3 (core)**: the `ParticleSeq`-indexed `W₁` part of `thermalization_limit_proof`
(`N := n + 2`, `a := u`), with the flow hypotheses given in the `SelectedFlow` form. -/
theorem mp_therm_seq_core (S : PreparedData d) (hs : S.s < 2 * (d : ℝ) / 3) (m : ℝ)
    (hm : (d : ℝ) + 2 < m) (T : ℝ) (hT : 0 < T) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (β₀ : ℝ) (hβ₀ : 0 ≤ β₀)
    (u : ℕ → ℝ) (hu0 : ∀ n, 0 ≤ u n) (hu : Tendsto u atTop atTop) (PS : ParticleSeq d)
    (hflow : ∀ n, SelectedFlow (PS.P n) S.dyn (u n + T) (PS.X n 0) (PS.W n) (PS.X n))
    (hfilt : ∀ n, ∃ (ℱ : MeasureTheory.Filtration ℝ (PS.mΩ n))
      (W' : ℝ≥0 → PS.Ω n → (Fin (n + 2) × Fin d) → ℝ), IsFilteredSolution (PS.P n) ℱ W' (PS.W n) (PS.X n))
    (hinit : ∀ n, law (PS.P n) (PS.X n 0) =
      modulatedGibbs (periodicRiesz d S.s) (n + 2) β₀ S.μ0)
    {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
    (Z : ℝ → Ω'' → NegSobolev d m)
    (hZ : IsStationaryGaussianField P'' S.s S.β S.hs0 S.hsd S.hβ S.V ρβ m Z) :
    Tendsto (fun n : ℕ => wassersteinE 1 (S.etaLaw m T (u n) (PS.P n) (PS.X n))
        (law P'' (windowPath m T 0 Z))) atTop (𝓝 0) := by
  classical
  have hd1 : 1 ≤ d := by have := S.hd; omega
  obtain ⟨C, c, hC, hc, hth⟩ := thermalization_proof S m hm T hT ρβ hρβ
  obtain ⟨C₀, h0⟩ := standard_preparation_norms_proof S hs m hm β₀ hβ₀
  obtain ⟨⟨Cb, hCb⟩, -⟩ := prepared_scales_proof S β₀ hβ₀
  have hs_t : Tendsto (fun n : ℕ => Real.sqrt ((n + 2 : ℕ) : ℝ) * deltaN d S.s (n + 2)) atTop (𝓝 0) :=
    ((deltaN_errors_tendsto hd1 S.hs0 hs).1).comp (tendsto_add_atTop_nat 2)
  have hδ_t : Tendsto (fun n : ℕ => deltaN d S.s (n + 2)) atTop (𝓝 0) :=
    (therm_delta_tendsto S hs).comp (tendsto_add_atTop_nat 2)
  have hη : ∀ n : ℕ, Measurable (fun X : Config d (n + 2) => etaE m X S.μ0) := fun n => by
    haveI : IsProbabilityMeasure S.μ0 := HRS.isProb_withDensityReal S.hρ0.density
    have hm2 : (d : ℝ) < 2 * m := by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      linarith
    have := measurable_ofMeasureDiff_empirical (N := n + 2) hm2 S.μ0 (by omega)
    unfold etaE flucE
    exact this.const_smul (Real.sqrt ((n + 2 : ℕ) : ℝ))
  have hmom1 : ∀ n : ℕ, ∫⁻ ω, ‖etaE m (PS.X n 0 ω) S.μ0‖ₑ ∂(PS.P n) ≤ ENNReal.ofReal C₀ :=
    fun n => by
    have := (h0 (n + 2) (by omega)).1
    rw [← hinit n, law, lintegral_map (hη n).enorm (hflow n).init_meas] at this
    exact this
  have hB : ∀ n : ℕ, relEntropy (law (PS.P n) (PS.X n 0)) (S.refMeasure (n + 2) 0) < ⊤ ∧
      S.B (n + 2) (law (PS.P n) (PS.X n 0)) ≤ Cb * (((n + 2 : ℕ) : ℝ) * deltaN d S.s (n + 2)) :=
    fun n => by
    rw [hinit n]; exact hCb (n + 2) (by omega)
  have hB1 : ∀ n : ℕ, 0 < S.B (n + 2) (law (PS.P n) (PS.X n 0)) := fun n => by
    have h1 := (deltaN_basic hd1 S.hs0 S.hsd (n + 2) (by omega)).1
    unfold PreparedData.B
    have := ENNReal.toReal_nonneg
      (a := relEntropy (law (PS.P n) (PS.X n 0)) (S.refMeasure (n + 2) 0))
    linarith
  have hδpos : ∀ n : ℕ, 0 < deltaN d S.s (n + 2) := fun n =>
    therm_deltaN_pos S.hd S.hs0 S.hsd (n + 2) (by omega)
  have hu2 : Tendsto (fun n : ℕ => C * (Cb * (Real.sqrt ((n + 2 : ℕ) : ℝ) * deltaN d S.s (n + 2)) +
      (Cb * deltaN d S.s (n + 2)) ^ ((1 : ℝ) / 4))) atTop (𝓝 0) := by
    have h1 := hs_t.const_mul Cb
    have h2 : Tendsto (fun n : ℕ => (Cb * deltaN d S.s (n + 2)) ^ ((1 : ℝ) / 4)) atTop (𝓝 0) := by
      have := (hδ_t.const_mul Cb).rpow_const (p := (1 : ℝ) / 4) (Or.inr (by norm_num))
      simpa [Real.zero_rpow (by norm_num : (1 / 4 : ℝ) ≠ 0)] using this
    have := (h1.add h2).const_mul C
    simpa using this
  have hK1 : ENNReal.ofReal C₀ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hR2 := therm_tendsto_rhs _ hu2 C c hc u hu (ENNReal.ofReal C₀) hK1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hR2
    (Eventually.of_forall fun _ => zero_le) (Eventually.of_forall fun n => ?_)
  obtain ⟨-, h2⟩ := hth (u n) (hu0 n) (n + 2) (by omega) (PS.P n) (PS.X n 0) (PS.W n) (PS.X n)
    (hflow n) (hfilt n) (hB n).1 P'' Z hZ
  have hr := therm_ratio_bounds (N := n + 2) (by omega) (hδpos n) (hB1 n) (hB n).2
  have hmono : ENNReal.ofReal (C * Real.exp (-c * u n)) *
      (1 + ∫⁻ ω, ‖etaE m (PS.X n 0 ω) S.μ0‖ₑ ∂(PS.P n)) ≤
      ENNReal.ofReal (C * Real.exp (-c * u n)) * (1 + ENNReal.ofReal C₀) := by
    gcongr
    exact hmom1 n
  refine h2.trans (add_le_add (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hC.le))
    hmono)
  have := Real.rpow_le_rpow (div_nonneg (hB1 n).le (Nat.cast_nonneg (n + 2))) hr.2
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
  linarith [hr.1]

/-- **L3**: the `ParticleSeq`-indexed `W₁` part of `thermalization_limit_proof`, with the
hypotheses of `mean_particles` (`hS`, `hSF`, `hinit`) for the dynamics `PDE.mfData` (`V = 0`) of an
abstract `S : PreparedData d`; `hρ0` links the initial datum of `S` with `ρ 0`. -/
theorem mp_therm_seq {s β : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β) (ρ : ℝ → Torus d → ℝ)
    (S : PreparedData d)
    (hdyn : S.dyn = PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) (hρ0 : S.ρ0 = ρ 0)
    (hs : s < 2 * (d : ℝ) / 3) (m : ℝ) (hm : (d : ℝ) + 2 < m) (T : ℝ) (hT : 0 < T)
    (ρβ : Torus d → ℝ) (hρβ : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ)
    (β₀ : ℝ) (hβ₀ : 0 ≤ β₀) (u : ℕ → ℝ) (hu0 : ∀ n, 0 ≤ u n) (hu : Tendsto u atTop atTop)
    (PS : ParticleSeq d)
    (hS : ∀ T' : ℝ, 0 ≤ T' → PS.IsSolutionOn (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) T')
    (hSF : ∀ n, ∃ (ℱ : MeasureTheory.Filtration ℝ (PS.mΩ n))
      (W' : ℝ≥0 → PS.Ω n → (Fin (n + 2) × Fin d) → ℝ),
      IsFilteredSolution (PS.P n) ℱ W' (PS.W n) (PS.X n))
    (hinit : ∀ n, (PS.P n).map (PS.X₀ n) =
      modulatedGibbs (periodicRiesz d s) (n + 2) β₀ (withDensityReal (ρ 0)))
    {Ω'' : Type} [MeasurableSpace Ω''] (P'' : Measure Ω'') [IsProbabilityMeasure P'']
    (Z : ℝ → Ω'' → NegSobolev d m)
    (hZ : IsStationaryGaussianField P'' S.s S.β S.hs0 S.hsd S.hβ S.V ρβ m Z) :
    Tendsto (fun n : ℕ => wassersteinE 1 (S.etaLaw m T (u n) (PS.P n) (PS.X n))
        (law P'' (windowPath m T 0 Z))) atTop (𝓝 0) := by
  have hse : S.s = s := congrArg DynData.s hdyn
  have hs' : S.s < 2 * (d : ℝ) / 3 := hse ▸ hs
  refine mp_therm_seq_core S hs' m hm T hT ρβ hρβ β₀ hβ₀ u hu0 hu PS
    (fun n => mp_selectedFlow S.hd hs0 hsd hβ S hdyn PS (u n + T) (by linarith [hu0 n])
      (hS _ (by linarith [hu0 n])) n) hSF (fun n => ?_) P'' Z hZ
  have h1 := mp_law_X0 (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) PS 0 (hS 0 le_rfl) n
  rw [law, h1, hinit n, hse, PreparedData.μ0, hρ0]

end Main

end HRS
