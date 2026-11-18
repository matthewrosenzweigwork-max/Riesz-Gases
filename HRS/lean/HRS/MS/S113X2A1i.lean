import HRS.MS.S113X2A1h

/-!
# S11.3 X2 part A1i: the every-time slice subsolution inequality for time-independent test functions
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113X2

open HRS HRS.Whole

variable {d N : ℕ}

theorem s113a_integral_Ioo_split {F : ℝ → ℝ} {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hF : IntegrableOn F (Set.Ioo 0 t)) :
    ∫ r in Set.Ioo 0 t, F r = (∫ r in Set.Ioo 0 s, F r) + ∫ r in Set.Ioo s t, F r := by
  have h1 : IntegrableOn F (Set.Ioc 0 t) := (integrableOn_Ioc_iff_integrableOn_Ioo).2 hF
  have h2 : IntervalIntegrable F volume 0 s :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hs).2 (h1.mono_set (Set.Ioc_subset_Ioc_right hst))
  have h3 : IntervalIntegrable F volume s t :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hst).2 (h1.mono_set (Set.Ioc_subset_Ioc_left hs))
  have e1 : ∫ r in Set.Ioo 0 t, F r = ∫ r in Set.Ioc 0 t, F r := setIntegral_congr_set Ioo_ae_eq_Ioc
  have e2 : ∫ r in Set.Ioo 0 s, F r = ∫ r in Set.Ioc 0 s, F r := setIntegral_congr_set Ioo_ae_eq_Ioc
  have e3 : ∫ r in Set.Ioo s t, F r = ∫ r in Set.Ioc s t, F r := setIntegral_congr_set Ioo_ae_eq_Ioc
  rw [e2, e3, e1,
    ← intervalIntegral.integral_of_le (hs.trans hst), ← intervalIntegral.integral_of_le hs,
    ← intervalIntegral.integral_of_le hst, intervalIntegral.integral_add_adjacent_intervals h2 h3]

/-- Core identity for a time-independent test function, for every `T ≥ 0`. -/
theorem s113a_Z_timeindep {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {s q β : ℝ} (hβ : 0 < β) {T : ℝ} (hT : 0 ≤ T)
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hX : MovParticleSetup P d s q β N X₀ W X)
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hF : IsWholeFilteredSolution P ℱ W' W X)
    (D : Set (EucConfig d N)) (chi : EucConfig d N → ℝ) (hchi : Measurable chi)
    (hchi0 : ∀ z, 0 ≤ chi z) (hchi1 : ∀ z, chi z ≤ 1)
    {τ : Ω → WithTop ℝ} (hτ : IsStoppingTime ℱ τ)
    (hτg : ∀ᵐ ζ ∂P, (∀ t : ℝ≥0, ζ ∈ s113a_survives D X t ↔ ((t : ℝ) : WithTop ℝ) < τ ζ) ∧
      ∀ c : ℝ, τ ζ = (c : WithTop ℝ) → 0 ≤ c ∧ X c.toNNReal ζ ∉ D)
    (phi : EucConfig d N → ℝ) (hphi : ContDiff ℝ ∞ phi) {K : Set (EucConfig d N)}
    (hKc : IsCompact K) (hKfree : ∀ x ∈ K, x ∉ eucCollisionSet d N)
    (hsupp : ∀ x, x ∉ K → phi x = 0) :
    ∃ Z : Ω → ℝ, Integrable Z P ∧
      ∫ ζ, Z ζ ∂P = ∫ ζ, chi (X 0 ζ) * phi (X 0 ζ) ∂P +
        ∫ r in Set.Ioo 0 T, ∫ x, s113a_genx d s q β N phi x ∂(s113a_killedLaw P D X₀ X chi r.toNNReal) ∧
      Integrable (fun r : ℝ => ∫ x, s113a_genx d s q β N phi x ∂(s113a_killedLaw P D X₀ X chi r.toNNReal))
        (volume.restrict (Set.Ioo 0 T)) ∧
      ∀ᵐ ζ ∂P,
        (((T : ℝ) : WithTop ℝ) < τ ζ → Z ζ = chi (X 0 ζ) * phi (X T.toNNReal ζ)) ∧
        ∀ c : ℝ, τ ζ = (c : WithTop ℝ) → c ≤ T → Z ζ = chi (X 0 ζ) * phi (X c.toNNReal ζ) := by
  classical
  have hsol := hX.sol T
  have hphi2 : ContDiff ℝ 2 phi := hphi.of_le (by simp)
  obtain ⟨C0, hC00, hC0b⟩ := s113a_bound_on_strip (N := N) hKc (F := fun p : ℝ × EucConfig d N => phi p.2)
    (hphi.continuous.comp continuous_snd) (fun r x hx => hsupp x hx) T
  have hphib : ∀ x, |phi x| ≤ C0 := fun x => by
    have := hC0b 0 ⟨le_rfl, hT⟩ x
    simpa using this
  have hZ0 : Integrable (fun ζ => chi (X 0 ζ) * phi (X 0 ζ)) P := by
    refine Integrable.of_bound (C := C0) ?_ (ae_of_all _ fun ζ => ?_)
    · exact ((hchi.comp (hsol.adapted 0)).mul
        (hphi.continuous.measurable.comp (hsol.adapted 0))).aestronglyMeasurable
    · rw [norm_mul, Real.norm_of_nonneg (hchi0 _)]
      calc chi (X 0 ζ) * ‖phi (X 0 ζ)‖ ≤ 1 * C0 :=
            mul_le_mul (hchi1 _) (by simpa using hphib _) (norm_nonneg _) zero_le_one
        _ = C0 := one_mul C0
  rcases hT.eq_or_lt with h0 | hpos
  · subst h0
    refine ⟨fun ζ => chi (X 0 ζ) * phi (X 0 ζ), hZ0, ?_, ?_, ?_⟩
    · simp
    · simp
    · filter_upwards [hτg] with ζ hg
      refine ⟨fun _ => by simp, fun c hc hc0 => ?_⟩
      have : c = 0 := le_antisymm hc0 (hg.2 c hc).1
      subst this
      simp
  · obtain ⟨hGc, hG0⟩ := s113a_gen_continuous (N := N) s q β (Phi := fun p : ℝ × EucConfig d N => phi p.2)
      (hphi.comp contDiff_snd) hKc.isClosed hKfree (fun r x hx => hsupp x hx)
    obtain ⟨C, hC0, hC⟩ := s113a_bound_on_strip hKc hGc hG0 T
    obtain ⟨Z, hZi, hZeq, hZae⟩ := s113a_core hβ hpos hX hF D chi hchi hchi0 hchi1 hτ hτg
      (fun p : ℝ × EucConfig d N => phi p.2) (hphi.comp contDiff_snd) hKc hKfree
      (fun r x hx => hsupp x hx)
    have hXm : Measurable fun z : ℝ × Ω => X z.1.toNNReal z.2 :=
      measurable_of_progressive hF.progressive
    obtain ⟨-, -, -, -, -, hslice, hsliceInt⟩ := s113a_killed_integral P X₀ X (hsol.adapted 0) hsol.init hXm
      D chi hchi hchi0 hchi1 T τ (s113a_measurableSet_lt_stopping hτ) (hτg.mono fun ζ h => h.1)
      (s113a_gen d s q β N (fun p : ℝ × EucConfig d N => phi p.2)) hGc.measurable C (fun p hp => by
        have := hC p.1 ⟨hp.1.le, hp.2.le⟩ p.2
        simpa using this)
    have hgen : (fun p : ℝ × EucConfig d N => s113a_gen d s q β N (fun p : ℝ × EucConfig d N => phi p.2) p) =
        fun p => s113a_genx d s q β N phi p.2 := by
      funext p
      exact s113a_gen_timeindep s q β hphi2 p.1 p.2
    refine ⟨Z, hZi, ?_, ?_, hZae⟩
    · rw [hZeq, hslice]
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioo fun r _ => ?_
      simp only [hgen]
    · refine hsliceInt.congr (ae_of_all _ fun r => ?_)
      simp only [hgen]

end HRS.MS.S113X2

end
