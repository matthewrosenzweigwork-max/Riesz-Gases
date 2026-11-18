import HRS.MS.S113X2A2i

/-!
# S11.3 X2 part A2f: **interior density of the killed law** (Pro `killed_interior_density`, without the pointwise equation)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113X2

open HRS HRS.Whole

variable {d N : ℕ}

open Classical in
/-- **Interior density.**  There is one jointly measurable nonnegative `f`, smooth on `(0,T) × D`, vanishing outside `D`,
such that for every `t ∈ (0,T)` the killed law is `f(t,·) dx`. -/
theorem s113a_killed_interior_density {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {s q β : ℝ} (hβ : 0 < β) {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hX : MovParticleSetup P d s q β N X₀ W X)
    (D : Set (EucConfig d N)) (hD : IsOpen D) (hfree : D ⊆ (eucCollisionSet d N)ᶜ)
    (chi : EucConfig d N → ℝ) (hchi : Measurable chi)
    (hchi0 : ∀ z, 0 ≤ chi z) (hchi1 : ∀ z, chi z ≤ 1) :
    ∃ f : ℝ → EucConfig d N → ℝ, Measurable (Function.uncurry f) ∧
      ContDiffOn ℝ ∞ (Function.uncurry f) (Set.Ioo 0 T ×ˢ D) ∧
      (∀ t z, 0 ≤ f t z) ∧ (∀ t z, z ∉ D → f t z = 0) ∧
      (∀ t ∈ Set.Ioo 0 T, s113a_killedLaw P D X₀ X chi t.toNNReal =
        volume.withDensity (fun z => ENNReal.ofReal (f t z))) ∧
      ∀ t ∈ Set.Ioo 0 T, ∀ z ∈ D,
        HasDerivAt (fun r => f r z) (movFP d s q β N (f t) z) t := by
  obtain ⟨f', hf'sm, hf'nn, hf'eq⟩ := s113a_weyl_density hβ hT hX D hD hfree chi hchi hchi0 hchi1
  set O : Set (ℝ × EucConfig d N) := Set.Ioo 0 T ×ˢ D with hOdef
  have hO : IsOpen O := isOpen_Ioo.prod hD
  set F : ℝ × EucConfig d N → ℝ := O.indicator f' with hFdef
  have hFm : Measurable F := s113a_measurable_ext hO hf'sm.continuousOn
  have hFO : ∀ p ∈ O, F p = f' p := fun p hp => Set.indicator_of_mem hp _
  have hF0 : ∀ p, p ∉ O → F p = 0 := fun p hp => Set.indicator_of_notMem hp _
  have hFc : ContinuousOn F O := hf'sm.continuousOn.congr hFO
  have hFnn : ∀ p, 0 ≤ F p := fun p => by
    by_cases hp : p ∈ O
    · rw [hFO p hp]; exact hf'nn p hp
    · rw [hF0 p hp]
  have hρ : (s113a_killedSpacetime P D X₀ X chi T).restrict O =
      (volume.restrict O).withDensity (fun p => ENNReal.ofReal (F p)) := by
    rw [hf'eq]
    refine withDensity_congr_ae ?_
    filter_upwards [ae_restrict_mem hO.measurableSet] with p hp
    rw [hFO p hp]
  obtain ⟨ℱ, W', hF, τ, hτ, hτg⟩ := s113a_setup hX D hD
  have hsol := hX.sol 0
  -- the key identity on test functions
  have hkey : ∀ t ∈ Set.Ioo 0 T, ∀ ψ : EucConfig d N → ℝ, Continuous ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ D → ∫ x, ψ x ∂(s113a_killedLaw P D X₀ X chi t.toNNReal) = ∫ x, ψ x * F (t, x) := by
    intro t ht ψ hψ hψc hψs
    obtain ⟨C0, hC0⟩ := hψc.exists_bound_of_continuous hψ
    have hψ0 : ∀ x, x ∉ D → ψ x = 0 := fun x hx =>
      image_eq_zero_of_notMem_tsupport (fun h => hx (hψs h))
    have ha := s113a_killed_pairing_continuousOn hX D chi hchi hchi0 hchi1 hτ hτg ψ hψ hψ0
      (C0 := C0) (fun x => by simpa using hC0 x)
    have hb := s113a_density_pairing_continuousOn hD hFc hψ hψc hψs
    have haI : ContinuousOn (fun t : ℝ => ∫ x, ψ x ∂(s113a_killedLaw P D X₀ X chi t.toNNReal))
        (Set.Ioo 0 T) := ha.mono fun t ht => le_of_lt ht.1
    have hloc : LocallyIntegrableOn (fun t : ℝ => (∫ x, ψ x ∂(s113a_killedLaw P D X₀ X chi t.toNNReal)) -
        ∫ x, ψ x * F (t, x)) (Set.Ioo 0 T) volume :=
      (haI.sub hb).locallyIntegrableOn measurableSet_Ioo
    have hI : ∀ θ : ℝ → ℝ, ContDiff ℝ ∞ θ → HasCompactSupport θ → tsupport θ ⊆ Set.Ioo 0 T →
        ∫ t, θ t • ((∫ x, ψ x ∂(s113a_killedLaw P D X₀ X chi t.toNNReal)) - ∫ x, ψ x * F (t, x)) = 0 := by
      intro θ hθ hθc hθs
      have hθ0 : Continuous θ := hθ.continuous
      have i1 := s113a_integrable_smul_cont hθ0 hθc hθs haI
      have i2 := s113a_integrable_smul_cont hθ0 hθc hθs hb
      have := s113a_pairing_identity hβ hT hX D hD chi hchi hchi0 hchi1 hFm hFc hF0 hFnn hρ hθ0 hθc hθs
        hψ hψc hψs
      simp only [smul_eq_mul, mul_sub]
      rw [integral_sub i1 i2, this, sub_self]
    have hae := (isOpen_Ioo (a := (0 : ℝ)) (b := T)).ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc hI
    have hae' : (fun t : ℝ => (∫ x, ψ x ∂(s113a_killedLaw P D X₀ X chi t.toNNReal)) -
        ∫ x, ψ x * F (t, x)) =ᵐ[volume.restrict (Set.Ioo 0 T)] fun _ => 0 := by
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
      filter_upwards [hae] with t h1 h2 using h1 h2
    have := Measure.eqOn_open_of_ae_eq hae' isOpen_Ioo (haI.sub hb) continuousOn_const ht
    simpa [sub_eq_zero] using this
  have hFcd : ContDiffOn ℝ ∞ F O := hf'sm.congr fun p hp => hFO p hp
  refine ⟨fun t z => F (t, z), ?_, ?_, fun t z => hFnn _, fun t z hz => hF0 _ (fun h => hz h.2), ?_, ?_⟩
  · exact hFm
  · exact hFcd
  · intro t ht
    haveI := s113a_killedLaw_finite P D X₀ X chi hchi1 t.toNNReal
    have hμD : (volume.withDensity (fun z => ENNReal.ofReal (F (t, z)))) Dᶜ = 0 := by
      rw [withDensity_apply _ hD.isClosed_compl.measurableSet]
      rw [setLIntegral_congr_fun hD.isClosed_compl.measurableSet (g := fun _ => 0) (fun z hz => by
        simp [hF0 (t, z) (fun h => hz h.2)])]
      simp
    have hFt : Measurable fun z => F (t, z) := hFm.comp (measurable_prodMk_left (x := t))
    refine s113a_measure_eq_of_Cc hD (s113a_killedLaw_compl P D hD X₀ X chi t.toNNReal (hsol.adapted _))
      hμD (fun ψ hψ hψc hψs => ?_) (fun ψ hψ hψc hψs => ?_)
    · beta_reduce
      rw [integrable_withDensity_iff_integrable_smul' (f := fun z => ENNReal.ofReal (F (t, z)))
        (ENNReal.measurable_ofReal.comp hFt) (ae_of_all _ fun z => ENNReal.ofReal_lt_top)]
      have hcont : ContinuousOn (fun z => (ENNReal.ofReal (F (t, z))).toReal • ψ z) (tsupport ψ) := by
        have h1 : ContinuousOn (fun z => F (t, z)) D :=
          hFc.comp (continuous_const.prodMk continuous_id).continuousOn (fun z hz => ⟨ht, hz⟩)
        refine ((h1.mono hψs).mul hψ.continuousOn).congr fun z _ => ?_
        simp [ENNReal.toReal_ofReal (hFnn _)]
      refine (integrableOn_iff_integrable_of_support_subset (s := tsupport ψ) ?_).1
        (hcont.integrableOn_compact hψc.isCompact)
      intro z hz
      by_contra h
      exact hz (by simp [image_eq_zero_of_notMem_tsupport h])
    · beta_reduce
      rw [hkey t ht ψ hψ hψc hψs, integral_withDensity_eq_integral_toReal_smul (f := fun z => ENNReal.ofReal (F (t, z)))
        (ENNReal.measurable_ofReal.comp hFt) (ae_of_all _ fun z => ENNReal.ofReal_lt_top)]
      refine integral_congr_ae (ae_of_all _ fun z => ?_)
      simp [ENNReal.toReal_ofReal (hFnn _), mul_comm]

  · -- the pointwise equation
    obtain ⟨-, -, hweak⟩ := s113a_killed_weak_fpe hβ hT hX D hD hfree chi hchi hchi0 hchi1
    have hb : ContDiffOn ℝ ∞ (s113a_drift d s q β N) O := by
      have h1 : ContDiffOn ℝ ∞ (fun x : EucConfig d N => fun i => particleDriftW (quadraticGradientDyn d s q β) x i)
          D := (s113a_drift_contDiffOn (N := N) s q β).mono hfree
      exact h1.comp contDiff_snd.contDiffOn (fun p hp => hp.2)
    have hbc : ∀ k : Fin N × Fin d, ContDiffOn ℝ ∞ (fun p => s113a_drift d s q β N p k.1 k.2) O := fun k => by
      have h1 : ContDiffOn ℝ ∞ (fun p' => s113a_drift d s q β N p' k.1) O := contDiffOn_pi.1 hb k.1
      exact (EuclideanSpace.proj k.2).contDiff.comp_contDiffOn h1
    have hG : ∀ k : Fin N × Fin d,
        ContDiffOn ℝ ∞ (fun p => F p * s113a_drift d s q β N p k.1 k.2) O := fun k => hFcd.mul (hbc k)
    -- the weak equation in density form
    have hdens : ∀ G : ℝ × EucConfig d N → ℝ, Measurable G → (∀ p, p ∉ O → G p = 0) →
        ∫ p, G p ∂(s113a_killedSpacetime P D X₀ X chi T) = ∫ p, F p * G p := by
      intro G hGm hG0
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hG0, hρ,
        integral_withDensity_eq_integral_toReal_smul₀ (f := fun p => ENNReal.ofReal (F p))
          (ENNReal.measurable_ofReal.comp hFm).aemeasurable (ae_of_all _ fun p => ENNReal.ofReal_lt_top)]
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => by simp [hG0 p hp])]
      refine integral_congr_ae (ae_of_all _ fun p => ?_)
      simp [ENNReal.toReal_ofReal (hFnn p)]
    have hweakF : ∀ Φ : ℝ × EucConfig d N → ℝ, ContDiff ℝ ∞ Φ → HasCompactSupport Φ → tsupport Φ ⊆ O →
        ∫ p, F p * HRS.MC.CepP3.Lop β⁻¹ (s113a_drift d s q β N) Φ p = 0 := by
      intro Φ hΦ hc hts
      have hKc : IsCompact (Prod.snd '' tsupport Φ) := hc.isCompact.image continuous_snd
      have hKD : Prod.snd '' tsupport Φ ⊆ D := by
        rintro _ ⟨p, hp, rfl⟩
        exact (hts hp).2
      have hKfree : ∀ x ∈ Prod.snd '' tsupport Φ, x ∉ eucCollisionSet d N := fun x hx => hfree (hKD hx)
      obtain ⟨hGc, -⟩ := s113a_gen_continuous (N := N) s q β hΦ hKc.isClosed hKfree
        (s113a_supp_of_tsupport (Phi := Φ))
      have h0 := (hweak Φ hΦ hc (fun p hp => ⟨(hts hp).1, (hts hp).2⟩)).2
      have hG0 : ∀ p, p ∉ O → s113a_gen d s q β N Φ p = 0 := by
        intro p hp
        have hpt : p ∉ tsupport Φ := fun h => hp (hts h)
        obtain ⟨h1, h2⟩ := s113a_fderiv2_zero_off hpt
        simp [s113a_gen, HRS.MC.CepP3.Lop, h1, h2]
      have := hdens _ hGc.measurable hG0
      rw [h0] at this
      exact this.symm
    have hpde := s113a_pde_of_weak hO hFcd hb hweakF
    intro t ht z hz
    have htz : (t, z) ∈ O := ⟨ht, hz⟩
    have h1 : HasDerivAt (fun r : ℝ => F (r, z)) (fderiv ℝ F (t, z) (1, 0)) t := by
      have hFd : DifferentiableAt ℝ F (t, z) := (hFcd.contDiffAt (hO.mem_nhds htz)).differentiableAt (by simp)
      have hc : HasDerivAt (fun r : ℝ => ((r, z) : ℝ × EucConfig d N)) ((1 : ℝ), (0 : EucConfig d N)) t :=
        (hasDerivAt_id t).prodMk (hasDerivAt_const t z)
      exact hFd.hasFDerivAt.comp_hasDerivAt t hc
    have h2 := s113a_movFP_eq s q β hO hFcd hG htz
    convert h1 using 1
    rw [h2, hpde (t, z) htz]

end HRS.MS.S113X2

end
