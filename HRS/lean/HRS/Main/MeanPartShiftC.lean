import HRS.Main.MeanPartShift

/-!
# MEANPART (shift, part C): L11 `mp_restrict_T`

(packet `mpshift`, plan `docs/MAIN_A_PLAN_mean_particles.md`, section 4.)

Convergence in distribution in `𝒳_{m,T₁}` implies convergence in distribution of the restrictions
in `𝒳_{m,T}`, `T ≤ T₁`.  This handles the degenerate horizon `T = 0` of `mean_particles` by running
the argument at `T₁ = T + 1` (or any `T₁ > 0`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ}

/-- Restriction `𝒳_{m,T₁} → 𝒳_{m,T}` of a path on `[0,T₁]` to `[0,T]`. -/
def mp_restrict {m T T₁ : ℝ} (hTT : T ≤ T₁) (w : PathSpace d m T₁) : PathSpace d m T :=
  (show C(Set.Icc (0 : ℝ) T₁, NegSobolev d m) from w).comp
    ⟨Set.inclusion (Set.Icc_subset_Icc_right hTT), continuous_inclusion (Set.Icc_subset_Icc_right hTT)⟩

theorem mp_restrict_apply {m T T₁ : ℝ} (hTT : T ≤ T₁) (w : PathSpace d m T₁)
    (t : Set.Icc (0 : ℝ) T) :
    PathSpace.at' (mp_restrict hTT w) t =
      PathSpace.at' w (Set.inclusion (Set.Icc_subset_Icc_right hTT) t) := rfl

theorem mp_norm_restrict_le {m T T₁ : ℝ} (hTT : T ≤ T₁) (w : PathSpace d m T₁) :
    ‖mp_restrict hTT w‖ ≤ ‖w‖ := by
  refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun t => ?_
  exact ContinuousMap.norm_coe_le_norm (show C(Set.Icc (0 : ℝ) T₁, NegSobolev d m) from w)
    (Set.inclusion (Set.Icc_subset_Icc_right hTT) t)

theorem mp_restrict_sub {m T T₁ : ℝ} (hTT : T ≤ T₁) (w w' : PathSpace d m T₁) :
    mp_restrict hTT (w - w') = mp_restrict hTT w - mp_restrict hTT w' := rfl

theorem mp_continuous_restrict {m T T₁ : ℝ} (hTT : T ≤ T₁) :
    Continuous (mp_restrict (d := d) (m := m) hTT) := by
  refine (LipschitzWith.of_dist_le_mul (K := 1) fun w w' => ?_).continuous
  rw [dist_eq_norm, dist_eq_norm, ← mp_restrict_sub, NNReal.coe_one, one_mul]
  exact mp_norm_restrict_le hTT _

/-- `flucPath` at horizon `T` is the restriction of `flucPath` at horizon `T₁` when the
underlying field is continuous on `[0,T₁]`. -/
theorem mp_flucPath_restrict {Ω : Type*} {N : ℕ} (γ T T₁ σ : ℝ) (hTT : T ≤ T₁)
    (X : ℝ≥0 → Ω → Config d N) (ρ : ℝ → Torus d → ℝ) (ω : Ω)
    (hc : Continuous fun t : Set.Icc (0 : ℝ) T₁ =>
      σ • NegSobolev.ofMeasureDiff γ (empirical (X (Real.toNNReal t) ω)) (withDensityReal (ρ t))) :
    flucPath γ T σ X ρ ω = mp_restrict hTT (flucPath γ T₁ σ X ρ ω) := by
  set F : Set.Icc (0 : ℝ) T₁ → NegSobolev d γ := fun t =>
    σ • NegSobolev.ofMeasureDiff γ (empirical (X (Real.toNNReal t) ω)) (withDensityReal (ρ t))
    with hF
  have hc2 : Continuous (F ∘ Set.inclusion (Set.Icc_subset_Icc_right hTT)) :=
    hc.comp (continuous_inclusion (Set.Icc_subset_Icc_right hTT))
  have hc' : Continuous fun t : Set.Icc (0 : ℝ) T =>
      σ • NegSobolev.ofMeasureDiff γ (empirical (X (Real.toNNReal t) ω)) (withDensityReal (ρ t)) :=
    hc2
  have e1 : flucPath γ T₁ σ X ρ ω =
      (⟨_, hc⟩ : C(Set.Icc (0 : ℝ) T₁, NegSobolev d γ)) := dif_pos hc
  have e2 : flucPath γ T σ X ρ ω =
      (⟨_, hc'⟩ : C(Set.Icc (0 : ℝ) T, NegSobolev d γ)) := dif_pos hc'
  rw [e1, e2]
  refine ContinuousMap.ext fun t => ?_
  rfl

/-- `toPath` at horizon `T` is the restriction of `toPath` at horizon `T₁` when the process is
continuous on `[0,T₁]`. -/
theorem mp_toPath_restrict {Ω : Type*} (γ T T₁ : ℝ) (hTT : T ≤ T₁) (Y : ℝ → Ω → NegSobolev d γ)
    (ω : Ω) (hc : ContinuousOn (fun t => Y t ω) (Set.Icc 0 T₁)) :
    toPath γ T Y ω = mp_restrict hTT (toPath γ T₁ Y ω) := by
  have h1 : Continuous fun t : Set.Icc (0 : ℝ) T₁ => Y t ω :=
    continuousOn_iff_continuous_restrict.mp hc
  have h2 : Continuous fun t : Set.Icc (0 : ℝ) T => Y t ω := h1.comp (continuous_inclusion (Set.Icc_subset_Icc_right hTT))
  have e1 : toPath γ T₁ Y ω = (⟨_, h1⟩ : C(Set.Icc (0 : ℝ) T₁, NegSobolev d γ)) := dif_pos h1
  have e2 : toPath γ T Y ω = (⟨_, h2⟩ : C(Set.Icc (0 : ℝ) T, NegSobolev d γ)) := dif_pos h2
  rw [e1, e2]
  refine ContinuousMap.ext fun t => ?_
  rfl

/-- Almost surely, `flucPath` with the Haar centring at horizon `T` is the restriction of the one
at horizon `T₁`. -/
theorem mp_flucPath_const_ae {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (hN : 1 ≤ N) (P : Measure Ω)
    (X : ℝ≥0 → Ω → Config d N) (hXc : ∀ᵐ ω ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ω i)
    {m : ℝ} (hm2 : (d : ℝ) < 2 * m) {T T₁ : ℝ} (hTT : T ≤ T₁) (σ : ℝ) :
    ∀ᵐ ω ∂P, flucPath m T σ X (fun _ _ => (1 : ℝ)) ω =
      mp_restrict hTT (flucPath m T₁ σ X (fun _ _ => (1 : ℝ)) ω) := by
  haveI : IsProbabilityMeasure (withDensityReal (fun _ : Torus d => (1 : ℝ))) :=
    HRS.isProb_withDensityReal mp_isProbDensity_one
  filter_upwards [hXc] with ω hω
  have hXp : Continuous fun t : Set.Icc (0 : ℝ) T₁ => X (Real.toNNReal t) ω :=
    continuous_pi fun i => (hω i).comp (continuous_real_toNNReal.comp continuous_subtype_val)
  have := therm_cont_emp T₁ hm2 hN σ (fun t => X (Real.toNNReal t) ω) hXp
    (fun _ => withDensityReal (fun _ : Torus d => (1 : ℝ))) (fun k => continuous_const)
  exact mp_flucPath_restrict m T T₁ σ hTT X _ ω this

/-- **L11**: restriction of convergence in distribution from horizon `T₁` to horizon `T ≤ T₁`. -/
theorem mp_restrict_T {m : ℝ} (hm2 : (d : ℝ) < 2 * m) {T T₁ : ℝ} (hTT : T ≤ T₁)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] (X : ∀ n, ℝ≥0 → Ω n → Config d (n + 2))
    (hXc : ∀ n, ∀ᵐ ω ∂(P n), ∀ i, Continuous fun t : ℝ≥0 => X n t ω i)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : ℝ → Ω' → NegSobolev d m) (hY : ∀ᵐ ω ∂P', ContinuousOn (fun t => Y t ω) (Set.Icc 0 T₁))
    (h : TendstoInDistribution
      (fun n ω => flucPath m T₁ (Real.sqrt ((n + 2 : ℕ) : ℝ)) (X n) (fun _ _ => (1 : ℝ)) ω)
      atTop (toPath m T₁ Y) P P') :
    TendstoInDistribution
      (fun n ω => flucPath m T (Real.sqrt ((n + 2 : ℕ) : ℝ)) (X n) (fun _ _ => (1 : ℝ)) ω)
      atTop (toPath m T Y) P P' := by
  have hc := h.continuous_comp (mp_continuous_restrict (d := d) (m := m) hTT)
  refine hc.congr (fun n => ?_) ?_
  · exact (mp_flucPath_const_ae (by omega) (P n) (X n) (hXc n) hm2 hTT _).mono fun ω hω => hω.symm
  · filter_upwards [hY] with ω hω
    exact (mp_toPath_restrict m T T₁ hTT Y ω hω).symm

end Main

end HRS
