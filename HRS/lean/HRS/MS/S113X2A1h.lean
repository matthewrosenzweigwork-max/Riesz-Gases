import HRS.MS.S113X2A1g

/-!
# S11.3 X2 part A1h: the stopped weak Fokker-Planck equation, space-time subsolution inequality
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113X2

open HRS HRS.Whole

variable {d N : ℕ}

theorem s113a_setup {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {s q β : ℝ} {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → EucConfig d N} (hX : MovParticleSetup P d s q β N X₀ W X)
    (D : Set (EucConfig d N)) (hD : IsOpen D) :
    ∃ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
      IsWholeFilteredSolution P ℱ W' W X ∧ ∃ τ : Ω → WithTop ℝ, IsStoppingTime ℱ τ ∧
        ∀ᵐ ζ ∂P, (∀ t : ℝ≥0, ζ ∈ s113a_survives D X t ↔ ((t : ℝ) : WithTop ℝ) < τ ζ) ∧
          ∀ c : ℝ, τ ζ = (c : WithTop ℝ) → 0 ≤ c ∧ X c.toNNReal ζ ∉ D := by
  obtain ⟨ℱ, W', hF⟩ := hX.filtered
  obtain ⟨τ, hτ, hτg⟩ := s113a_exit_data (hX.sol 0).cont hF D hD
  exact ⟨ℱ, W', hF, τ, hτ, hτg⟩

/-- Support lemma: a compactly supported smooth `Φ` with `tsupport Φ ⊆ U ×ˢ D` vanishes off `snd '' tsupport Φ`. -/
theorem s113a_supp_of_tsupport {Phi : ℝ × EucConfig d N → ℝ} :
    ∀ r x, x ∉ Prod.snd '' tsupport Phi → Phi (r, x) = 0 := by
  intro r x hx
  by_contra h
  exact hx ⟨(r, x), subset_tsupport _ (Function.mem_support.2 h), rfl⟩

open Classical in
/-- **Stopped weak Fokker-Planck equation** (Pro `killed_weak_fpe`, statement of the S113.D01 contract with the
generator `s113a_gen`). -/
theorem s113a_killed_weak_fpe {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {s q β : ℝ} (hβ : 0 < β) {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hX : MovParticleSetup P d s q β N X₀ W X)
    (D : Set (EucConfig d N)) (hD : IsOpen D) (hfree : D ⊆ (eucCollisionSet d N)ᶜ)
    (chi : EucConfig d N → ℝ) (hchi : Measurable chi)
    (hchi0 : ∀ z, 0 ≤ chi z) (hchi1 : ∀ z, chi z ≤ 1) :
    AEMeasurable (fun z : ℝ × Ω =>
      if z.2 ∈ s113a_survives D X z.1.toNNReal then ENNReal.ofReal (chi (X₀ z.2)) else 0)
      ((volume.restrict (Set.Ioo 0 T)).prod P) ∧
    IsFiniteMeasure (s113a_killedSpacetime P D X₀ X chi T) ∧
    ∀ Phi : ℝ × EucConfig d N → ℝ, ContDiff ℝ ∞ Phi → HasCompactSupport Phi →
      tsupport Phi ⊆ Set.Ioo 0 T ×ˢ D →
      Integrable (s113a_gen d s q β N Phi) (s113a_killedSpacetime P D X₀ X chi T) ∧
      ∫ z, s113a_gen d s q β N Phi z ∂(s113a_killedSpacetime P D X₀ X chi T) = 0 := by
  classical
  obtain ⟨ℱ, W', hF, τ, hτ, hτg⟩ := s113a_setup hX D hD
  have hsol := hX.sol T
  have hXm : Measurable fun z : ℝ × Ω => X z.1.toNNReal z.2 := measurable_of_progressive hF.progressive
  have hbasic := s113a_killed_integral P X₀ X (hsol.adapted 0) hsol.init hXm D chi hchi hchi0 hchi1 T τ
    (s113a_measurableSet_lt_stopping hτ) (hτg.mono fun ζ h => h.1) (fun _ => 0) measurable_const 0
    (fun p _ => by simp)
  refine ⟨hbasic.1, hbasic.2.1, fun Phi hPhi hc hts => ?_⟩
  set K := Prod.snd '' tsupport Phi with hK
  have hKc : IsCompact K := hc.isCompact.image continuous_snd
  have hKD : K ⊆ D := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hts hp).2
  have hKfree : ∀ x ∈ K, x ∉ eucCollisionSet d N := fun x hx => hfree (hKD hx)
  have hsupp := s113a_supp_of_tsupport (Phi := Phi)
  obtain ⟨hGc, hG0⟩ := s113a_gen_continuous (N := N) s q β hPhi hKc.isClosed hKfree hsupp
  obtain ⟨C, hC0, hC⟩ := s113a_bound_on_strip hKc hGc hG0 T
  have hint := s113a_killed_integral P X₀ X (hsol.adapted 0) hsol.init hXm D chi hchi hchi0 hchi1 T τ
    (s113a_measurableSet_lt_stopping hτ) (hτg.mono fun ζ h => h.1)
    (s113a_gen d s q β N Phi) hGc.measurable C (fun p hp => by
      have := hC p.1 ⟨hp.1.le, hp.2.le⟩ p.2
      simpa using this)
  refine ⟨hint.2.2.1, ?_⟩
  obtain ⟨Z, -, hZint, hZae⟩ := s113a_core hβ hT hX hF D chi hchi hchi0 hchi1 hτ hτg Phi hPhi hKc hKfree hsupp
  have hPhi0 : ∀ x, Phi (0, x) = 0 := fun x => by
    by_contra h
    have := (hts (subset_tsupport _ (Function.mem_support.2 h))).1
    simp at this
  have hZ0 : ∀ᵐ ζ ∂P, Z ζ = 0 := by
    filter_upwards [hZae, hτg] with ζ h1 hg
    by_cases hlt : ((T : ℝ) : WithTop ℝ) < τ ζ
    · rw [h1.1 hlt]
      have : Phi (T, X T.toNNReal ζ) = 0 := by
        by_contra h
        have := (hts (subset_tsupport _ (Function.mem_support.2 h))).1
        simp at this
      rw [this, mul_zero]
    · rw [not_lt] at hlt
      cases hc : τ ζ with
      | top => rw [hc] at hlt; exact absurd hlt (by simp)
      | coe c =>
        rw [hc] at hlt
        have hcT : c ≤ T := by exact_mod_cast hlt
        rw [h1.2 c hc hcT]
        have hout := (hg.2 c hc).2
        have : Phi (c, X c.toNNReal ζ) = 0 := by
          by_contra h
          exact hout ((hts (subset_tsupport _ (Function.mem_support.2 h))).2)
        rw [this, mul_zero]
  have hZint0 : ∫ ζ, Z ζ ∂P = 0 := by
    rw [integral_congr_ae hZ0]; simp
  rw [hZint] at hZint0
  simpa [hPhi0] using hZint0

/-- **Space-time subsolution inequality** for nonnegative test functions (no condition at the boundary of `D`):
`0 ≤ E[χ(X₀)Φ(0,X₀)] + ∫ 𝓛Φ d(killed space-time measure)`. -/
theorem s113a_killed_subsolution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {s q β : ℝ} (hβ : 0 < β) {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hX : MovParticleSetup P d s q β N X₀ W X)
    (D : Set (EucConfig d N)) (hD : IsOpen D)
    (chi : EucConfig d N → ℝ) (hchi : Measurable chi)
    (hchi0 : ∀ z, 0 ≤ chi z) (hchi1 : ∀ z, chi z ≤ 1)
    (Phi : ℝ × EucConfig d N → ℝ) (hPhi : ContDiff ℝ ∞ Phi) (hPhi0 : ∀ p, 0 ≤ Phi p)
    {K : Set (EucConfig d N)} (hKc : IsCompact K) (hKfree : ∀ x ∈ K, x ∉ eucCollisionSet d N)
    (hsupp : ∀ r x, x ∉ K → Phi (r, x) = 0) :
    Integrable (s113a_gen d s q β N Phi) (s113a_killedSpacetime P D X₀ X chi T) ∧
    0 ≤ ∫ ζ, chi (X₀ ζ) * Phi (0, X₀ ζ) ∂P +
      ∫ z, s113a_gen d s q β N Phi z ∂(s113a_killedSpacetime P D X₀ X chi T) := by
  classical
  obtain ⟨ℱ, W', hF, τ, hτ, hτg⟩ := s113a_setup hX D hD
  have hsol := hX.sol T
  have hXm : Measurable fun z : ℝ × Ω => X z.1.toNNReal z.2 := measurable_of_progressive hF.progressive
  obtain ⟨hGc, hG0⟩ := s113a_gen_continuous (N := N) s q β hPhi hKc.isClosed hKfree hsupp
  obtain ⟨C, hC0, hC⟩ := s113a_bound_on_strip hKc hGc hG0 T
  have hint := s113a_killed_integral P X₀ X (hsol.adapted 0) hsol.init hXm D chi hchi hchi0 hchi1 T τ
    (s113a_measurableSet_lt_stopping hτ) (hτg.mono fun ζ h => h.1)
    (s113a_gen d s q β N Phi) hGc.measurable C (fun p hp => by
      have := hC p.1 ⟨hp.1.le, hp.2.le⟩ p.2
      simpa using this)
  refine ⟨hint.2.2.1, ?_⟩
  obtain ⟨Z, -, hZint, hZae⟩ := s113a_core hβ hT hX hF D chi hchi hchi0 hchi1 hτ hτg Phi hPhi hKc hKfree hsupp
  have hZ0 : 0 ≤ᵐ[P] Z := by
    filter_upwards [hZae, hτg] with ζ h1 hg
    by_cases hlt : ((T : ℝ) : WithTop ℝ) < τ ζ
    · rw [h1.1 hlt]; exact mul_nonneg (hchi0 _) (hPhi0 _)
    · rw [not_lt] at hlt
      cases hc : τ ζ with
      | top => rw [hc] at hlt; exact absurd hlt (by simp)
      | coe c =>
        rw [hc] at hlt
        have hcT : c ≤ T := by exact_mod_cast hlt
        rw [h1.2 c hc hcT]; exact mul_nonneg (hchi0 _) (hPhi0 _)
  have h0 : 0 ≤ ∫ ζ, Z ζ ∂P := integral_nonneg_of_ae hZ0
  rw [hZint] at h0
  have hinit : ∫ ζ, chi (X 0 ζ) * Phi (0, X 0 ζ) ∂P = ∫ ζ, chi (X₀ ζ) * Phi (0, X₀ ζ) ∂P := by
    refine integral_congr_ae ?_
    filter_upwards [hsol.init] with ζ hζ
    rw [hζ]
  rwa [hinit] at h0

end HRS.MS.S113X2

end
