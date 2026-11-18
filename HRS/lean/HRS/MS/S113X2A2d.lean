import HRS.MS.S113X2A2c

/-!
# S11.3 X2 part A2d: identification of the Weyl density with the killed law, in time-integrated form
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113X2

open HRS HRS.Whole

variable {d N : ℕ}

open Classical in
/-- The extension by zero of a function continuous on an open set is measurable. -/
theorem s113a_measurable_ext {α : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
    {O : Set α} (hO : IsOpen O) {f : α → ℝ} (hf : ContinuousOn f O) :
    Measurable (O.indicator f) := by
  have := hf.measurable_piecewise (g := fun _ => (0 : ℝ)) continuousOn_const hO.measurableSet
  convert this using 1
  funext x
  by_cases hx : x ∈ O <;> simp [Set.piecewise, hx]

open Classical in
/-- Time-integrated identification: for `θ ∈ C_c(0,T)` and `ψ ∈ C_c(D)`,
`∫ θ(t) ν_t(ψ) dt = ∫ θ(t) ∫ ψ(x) F(t,x) dx dt`. -/
theorem s113a_pairing_identity {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {s q β : ℝ} (hβ : 0 < β) {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hX : MovParticleSetup P d s q β N X₀ W X)
    (D : Set (EucConfig d N)) (hD : IsOpen D)
    (chi : EucConfig d N → ℝ) (hchi : Measurable chi)
    (hchi0 : ∀ z, 0 ≤ chi z) (hchi1 : ∀ z, chi z ≤ 1)
    {F : ℝ × EucConfig d N → ℝ} (hFm : Measurable F) (hFc : ContinuousOn F (Set.Ioo 0 T ×ˢ D))
    (hF0 : ∀ p, p ∉ Set.Ioo 0 T ×ˢ D → F p = 0) (hFnn : ∀ p, 0 ≤ F p)
    (hρ : (s113a_killedSpacetime P D X₀ X chi T).restrict (Set.Ioo 0 T ×ˢ D) =
      (volume.restrict (Set.Ioo 0 T ×ˢ D)).withDensity (fun p => ENNReal.ofReal (F p)))
    {θ : ℝ → ℝ} (hθ : Continuous θ) (hθc : HasCompactSupport θ) (hθs : tsupport θ ⊆ Set.Ioo 0 T)
    {ψ : EucConfig d N → ℝ} (hψ : Continuous ψ) (hψc : HasCompactSupport ψ) (hψs : tsupport ψ ⊆ D) :
    ∫ t, θ t * ∫ x, ψ x ∂(s113a_killedLaw P D X₀ X chi t.toNNReal) =
      ∫ t, θ t * ∫ x, ψ x * F (t, x) := by
  classical
  obtain ⟨ℱ, W', hF, τ, hτ, hτg⟩ := s113a_setup hX D hD
  have hsol := hX.sol T
  have hXm : Measurable fun z : ℝ × Ω => X z.1.toNNReal z.2 := measurable_of_progressive hF.progressive
  set O : Set (ℝ × EucConfig d N) := Set.Ioo 0 T ×ˢ D with hOdef
  have hO : IsOpen O := isOpen_Ioo.prod hD
  set Θ : ℝ × EucConfig d N → ℝ := fun p => θ p.1 * ψ p.2 with hΘ
  have hΘc : Continuous Θ := (hθ.comp continuous_fst).mul (hψ.comp continuous_snd)
  obtain ⟨Cθ, hCθ⟩ := hθc.exists_bound_of_continuous hθ
  obtain ⟨Cψ, hCψ⟩ := hψc.exists_bound_of_continuous hψ
  have hΘb : ∀ p, |Θ p| ≤ Cθ * Cψ := fun p => by
    simp only [hΘ, abs_mul]
    exact mul_le_mul (by simpa using hCθ p.1) (by simpa using hCψ p.2) (abs_nonneg _)
      ((norm_nonneg _).trans (hCθ 0))
  have hΘ0 : ∀ p, p ∉ O → Θ p = 0 := by
    intro p hp
    simp only [hΘ]
    by_cases h1 : p.1 ∈ Set.Ioo 0 T
    · have h2 : p.2 ∉ D := fun h2 => hp ⟨h1, h2⟩
      have : ψ p.2 = 0 := image_eq_zero_of_notMem_tsupport (fun h => h2 (hψs h))
      rw [this, mul_zero]
    · have : θ p.1 = 0 := image_eq_zero_of_notMem_tsupport (fun h => h1 (hθs h))
      rw [this, zero_mul]
  -- (1) the left side
  have hL : ∫ p, Θ p ∂(s113a_killedSpacetime P D X₀ X chi T) =
      ∫ r in Set.Ioo 0 T, θ r * ∫ x, ψ x ∂(s113a_killedLaw P D X₀ X chi r.toNNReal) := by
    obtain ⟨-, -, -, -, -, hslice, -⟩ := s113a_killed_integral P X₀ X (hsol.adapted 0) hsol.init hXm D chi
      hchi hchi0 hchi1 T τ (s113a_measurableSet_lt_stopping hτ) (hτg.mono fun ζ h => h.1) Θ
      hΘc.measurable (Cθ * Cψ) (fun p _ => hΘb p)
    rw [hslice]
    refine setIntegral_congr_fun measurableSet_Ioo fun r _ => ?_
    simp only [hΘ]
    rw [integral_const_mul]
  -- (2) the right side
  have hK0 : IsCompact (tsupport θ ×ˢ tsupport ψ) := hθc.isCompact.prod hψc.isCompact
  have hK0O : tsupport θ ×ˢ tsupport ψ ⊆ O := Set.prod_mono hθs hψs
  have hFΘ0 : ∀ p, p ∉ tsupport θ ×ˢ tsupport ψ → F p * Θ p = 0 := by
    intro p hp
    have : Θ p = 0 := by
      simp only [hΘ]
      by_cases h1 : p.1 ∈ tsupport θ
      · have h2 : p.2 ∉ tsupport ψ := fun h2 => hp ⟨h1, h2⟩
        rw [image_eq_zero_of_notMem_tsupport h2, mul_zero]
      · rw [image_eq_zero_of_notMem_tsupport h1, zero_mul]
    rw [this, mul_zero]
  have hFΘint : Integrable (fun p => F p * Θ p) := by
    have hcont : ContinuousOn (fun p => F p * Θ p) (tsupport θ ×ˢ tsupport ψ) :=
      (hFc.mono hK0O).mul hΘc.continuousOn
    have hon : IntegrableOn (fun p => F p * Θ p) (tsupport θ ×ˢ tsupport ψ) := hcont.integrableOn_compact hK0
    refine (integrableOn_iff_integrable_of_support_subset ?_).1 hon
    intro p hp
    by_contra h
    exact hp (hFΘ0 p h)
  have hR : ∫ p, Θ p ∂(s113a_killedSpacetime P D X₀ X chi T) =
      ∫ t, ∫ x, F (t, x) * Θ (t, x) := by
    have e1 : ∫ p, Θ p ∂(s113a_killedSpacetime P D X₀ X chi T) =
        ∫ p in O, Θ p ∂(s113a_killedSpacetime P D X₀ X chi T) :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero hΘ0).symm
    rw [e1, hρ, integral_withDensity_eq_integral_toReal_smul₀ (f := fun p => ENNReal.ofReal (F p))
      (ENNReal.measurable_ofReal.comp hFm).aemeasurable (ae_of_all _ fun p => ENNReal.ofReal_lt_top)]
    have e2 : ∫ p in O, (ENNReal.ofReal (F p)).toReal • Θ p = ∫ p in O, F p * Θ p := by
      refine integral_congr_ae (ae_of_all _ fun p => ?_)
      simp only [ENNReal.toReal_ofReal (hFnn p), smul_eq_mul]
    rw [e2, setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => by
      rw [hΘ0 p hp, mul_zero])]
    rw [Measure.volume_eq_prod, integral_prod _ (by simpa [Measure.volume_eq_prod] using hFΘint)]
  -- (3) combine
  have hcomb : ∫ r in Set.Ioo 0 T, θ r * ∫ x, ψ x ∂(s113a_killedLaw P D X₀ X chi r.toNNReal) =
      ∫ t, ∫ x, F (t, x) * Θ (t, x) := by rw [← hL, hR]
  have e3 : ∫ t, θ t * ∫ x, ψ x ∂(s113a_killedLaw P D X₀ X chi t.toNNReal) =
      ∫ r in Set.Ioo 0 T, θ r * ∫ x, ψ x ∂(s113a_killedLaw P D X₀ X chi r.toNNReal) := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun t ht => ?_).symm
    rw [image_eq_zero_of_notMem_tsupport (fun h => ht (hθs h)), zero_mul]
  rw [e3, hcomb]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  simp only [hΘ]
  rw [← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  ring

end HRS.MS.S113X2

end
