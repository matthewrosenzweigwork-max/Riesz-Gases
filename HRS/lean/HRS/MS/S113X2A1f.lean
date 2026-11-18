import HRS.MS.S113X2A1e

/-!
# S11.3 X2 part A1f: the stopped Itô identity for the killed process (core of the weak Fokker-Planck equations)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113X2

open HRS HRS.Whole

variable {d N : ℕ}

theorem s113a_X0_measurable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {X : ℝ≥0 → Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hF : IsWholeFilteredSolution P ℱ W' W X) (s : ℝ) : Measurable[ℱ s] (X 0) := by
  rcases le_or_gt 0 s with hs | hs
  · exact (hF.adapted 0).mono (ℱ.mono (by simpa using hs)) le_rfl
  · have h := hF.progressive.adapted s
    have e : ofNNRealTime X s = X 0 := by
      funext ξ
      simp [ofNNRealTime_apply, Real.toNNReal_of_nonpos hs.le]
    rw [e] at h
    exact h

/-- **Core identity.**  For a smooth space-time test function `Φ` vanishing for `x ∉ K` (`K` compact, collision-free),
the exit time `τ` from `D`, and `T > 0`: there is an integrable `Z` which a.s. equals `χ(X₀) Φ(τ ∧ T, X_{τ∧T})` and
`E Z = E[χ(X₀)Φ(0,X₀)] + ∫ (𝓛Φ) d(killed space-time measure)`. -/
theorem s113a_core {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {s q β : ℝ} (hβ : 0 < β) {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hX : MovParticleSetup P d s q β N X₀ W X)
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hF : IsWholeFilteredSolution P ℱ W' W X)
    (D : Set (EucConfig d N)) (chi : EucConfig d N → ℝ) (hchi : Measurable chi)
    (hchi0 : ∀ z, 0 ≤ chi z) (hchi1 : ∀ z, chi z ≤ 1)
    {τ : Ω → WithTop ℝ} (hτ : IsStoppingTime ℱ τ)
    (hτg : ∀ᵐ ζ ∂P, (∀ t : ℝ≥0, ζ ∈ s113a_survives D X t ↔ ((t : ℝ) : WithTop ℝ) < τ ζ) ∧
      ∀ c : ℝ, τ ζ = (c : WithTop ℝ) → 0 ≤ c ∧ X c.toNNReal ζ ∉ D)
    (Phi : ℝ × EucConfig d N → ℝ) (hPhi : ContDiff ℝ ∞ Phi) {K : Set (EucConfig d N)}
    (hKc : IsCompact K) (hKfree : ∀ x ∈ K, x ∉ eucCollisionSet d N)
    (hsupp : ∀ r x, x ∉ K → Phi (r, x) = 0) :
    ∃ Z : Ω → ℝ, Integrable Z P ∧
      ∫ ζ, Z ζ ∂P = ∫ ζ, chi (X 0 ζ) * Phi (0, X 0 ζ) ∂P +
        ∫ z, s113a_gen d s q β N Phi z ∂(s113a_killedSpacetime P D X₀ X chi T) ∧
      ∀ᵐ ζ ∂P,
        (((T : ℝ) : WithTop ℝ) < τ ζ → Z ζ = chi (X 0 ζ) * Phi (T, X T.toNNReal ζ)) ∧
        ∀ c : ℝ, τ ζ = (c : WithTop ℝ) → c ≤ T → Z ζ = chi (X 0 ζ) * Phi (c, X c.toNNReal ζ) := by
  classical
  have hsol := hX.sol T
  have hW := hF.brownian
  set Dyn := quadraticGradientDyn d s q β with hDyn
  have hPhi2 : ContDiff ℝ 2 Phi := hPhi.of_le (by simp)
  obtain ⟨hGc, hG0⟩ := s113a_gen_continuous (N := N) s q β hPhi hKc.isClosed hKfree hsupp
  obtain ⟨C, hC0, hC⟩ := s113a_bound_on_strip hKc hGc hG0 T
  have hD1 : Continuous (fderiv ℝ Phi) := hPhi.continuous_fderiv (by simp)
  have hD1z : ∀ r x, x ∉ K → fderiv ℝ Phi (r, x) = 0 := fun r x hx =>
    (s113a_fderiv_zero_off hKc.isClosed hsupp (r, x) hx).1
  obtain ⟨B, hB0, hB⟩ := s113a_bound_on_strip hKc hD1 hD1z T
  obtain ⟨C0, hC00, hC0b⟩ := s113a_bound_on_strip hKc hPhi.continuous hsupp T
  -- the Itô integrand
  set σ := HRS.MH.DualityRd.noiseDir (N := N) Dyn with hσ
  set f : ℝ → EucConfig d N → ℝ := fun r x => Phi (r, x) with hf
  set Ψ := itoIntegrand T Set.univ f (ofNNRealTime X) (fun _ _ => σ) with hΨ
  have hfC : IsC12On T Set.univ f := isC12On_of_contDiff_joint T Set.univ _ (by
    simpa [hf, Function.uncurry_def] using hPhi2)
  have hXc : ∀ᵐ ζ ∂P, Continuous fun t => ofNNRealTime X t ζ := by
    filter_upwards [hsol.cont] with ζ hζ
    exact continuous_ofNNRealTime X ζ (continuous_pi hζ)
  have hΦE : IsProgressiveLocL2E P ℱ (fun (_ : ℝ) (_ : Ω) => σ) := by
    refine ⟨isProgressive_const ℱ σ, fun T' => ae_of_all _ fun ζ => ?_⟩
    rw [lintegral_const]
    exact ENNReal.mul_lt_top (by simp) (by simp)
  have hΨprog : IsProgressive ℱ Ψ :=
    (isProgressiveLocL2_itoIntegrand Set.univ isClosed_univ Set.univ (Set.Subset.refl _) f hfC
      (ofNNRealTime X) hF.progressive hXc _ hΦE).prog
  have hΨb : ∀ r ζ k, |Ψ r ζ k| ≤ B * ∑ k', ‖σ k'‖ := by
    intro r ζ k
    by_cases hr : r ∈ Set.Icc 0 T
    · simp only [hΨ, itoIntegrand, Set.indicator_of_mem hr, Set.mem_univ, Set.ofPred_true,
        Set.indicator_univ, hf, ofNNRealTime_apply]
      rw [s113a_slice_fderiv Phi (hPhi.differentiable (by simp))]
      calc |fderiv ℝ Phi (r, X r.toNNReal ζ) (0, σ k)|
          ≤ ‖fderiv ℝ Phi (r, X r.toNNReal ζ)‖ * ‖((0 : ℝ), σ k)‖ := by
            rw [← Real.norm_eq_abs]; exact ContinuousLinearMap.le_opNorm _ _
        _ ≤ B * ‖σ k‖ := by
            rw [Prod.norm_def]
            simp only [norm_zero]
            rw [max_eq_right (norm_nonneg _)]
            exact mul_le_mul_of_nonneg_right (hB r hr _) (norm_nonneg _)
        _ ≤ B * ∑ k', ‖σ k'‖ :=
            mul_le_mul_of_nonneg_left (Finset.single_le_sum (fun k' _ => norm_nonneg (σ k'))
              (Finset.mem_univ k)) hB0
    · simp [hΨ, itoIntegrand, Set.indicator_of_notMem hr]
      positivity
  have hΨL2 : IsProgressiveL2 P ℱ Ψ := IsProgressiveL2.of_bounded P hΨprog _ hΨb
  have hΨ0 : ∀ r ≤ (-1 : ℝ), ∀ ζ, Ψ r ζ = 0 := by
    intro r hr ζ
    have : r ∉ Set.Icc (0 : ℝ) T := fun h => by linarith [h.1]
    funext k
    simp [hΨ, itoIntegrand, Set.indicator_of_notMem this]
  -- weighted mean zero of the stopped integral
  have hξ : Measurable[ℱ (-1)] (fun ζ => chi (X 0 ζ)) :=
    hchi.comp (s113a_X0_measurable hF (-1))
  have hξb : ∀ ζ, |chi (X 0 ζ)| ≤ 1 := fun ζ => by
    rw [abs_of_nonneg (hchi0 _)]; exact hchi1 _
  obtain ⟨hYint, hYzero⟩ := s113a_weighted_mean_zero hW hΨL2 hΨ0 hτ hξ hξb T
  have hstop := localItoIntegral_stopIntegrand hW hΨL2.locL2 hτ
  -- the Fubini identification
  have hGm : Measurable (s113a_gen d s q β N Phi) := hGc.measurable
  obtain ⟨-, -, hGint, hI1, hI2, -, -⟩ := s113a_killed_integral P X₀ X (hsol.adapted 0) hsol.init
    (measurable_of_progressive hF.progressive) D chi hchi hchi0 hchi1 T τ
    (s113a_measurableSet_lt_stopping hτ) (hτg.mono fun ζ h => h.1)
    (s113a_gen d s q β N Phi) hGm C (fun p hp => by
      have := hC p.1 ⟨hp.1.le, hp.2.le⟩ p.2
      simpa using this)
  set G := s113a_gen d s q β N Phi with hG
  set M := localItoIntegral P ℱ W' Ψ with hM
  set I : Ω → ℝ := fun ζ => ∫ r in Set.Ioo 0 T,
    (if ((r : ℝ) : WithTop ℝ) < τ ζ then G (r, X r.toNNReal ζ) else 0) with hIdef
  set Y : Ω → ℝ := fun ζ => localItoIntegral P ℱ W' (stopIntegrand Ψ τ) T ζ with hYdef
  have hZ0 : Integrable (fun ζ => chi (X 0 ζ) * Phi (0, X 0 ζ)) P := by
    refine Integrable.of_bound (C := C0) ?_ (ae_of_all _ fun ζ => ?_)
    · exact ((hchi.comp (hsol.adapted 0)).mul
        (hPhi.continuous.measurable.comp (measurable_const.prodMk (hsol.adapted 0)))).aestronglyMeasurable
    · rw [norm_mul, Real.norm_of_nonneg (hchi0 _)]
      calc chi (X 0 ζ) * ‖Phi (0, X 0 ζ)‖ ≤ 1 * C0 :=
            mul_le_mul (hchi1 _) (hC0b 0 ⟨le_rfl, hT.le⟩ _) (norm_nonneg _) zero_le_one
        _ = C0 := one_mul C0
  have hab : Integrable (fun ζ => chi (X 0 ζ) * Phi (0, X 0 ζ) + chi (X 0 ζ) * I ζ) P := hZ0.add hI1
  refine ⟨fun ζ => chi (X 0 ζ) * Phi (0, X 0 ζ) + chi (X 0 ζ) * I ζ + chi (X 0 ζ) * Y ζ,
    hab.add hYint, ?_, ?_⟩
  · rw [integral_add hab hYint, integral_add hZ0 hI1, hYzero, ← hI2]
    simp
  · have hito := s113a_ito_gen hβ hT hsol hF Phi hPhi2
    filter_upwards [hito, hτg, hstop] with ζ hIt hg hs
    obtain ⟨hint, hE⟩ := hIt
    have hr : ∀ r : ℝ, 0 ≤ r → r ≤ T → Phi (r, X r.toNNReal ζ) = Phi (0, X 0 ζ) +
        (∫ u in Set.Icc (0 : ℝ) r, G (u, X u.toNNReal ζ)) + M r ζ := by
      intro r h0 hrT
      have := hE r.toNNReal (by rw [Real.coe_toNNReal _ h0]; exact hrT)
      rwa [Real.coe_toNNReal _ h0] at this
    refine ⟨fun hlt => ?_, fun c hc hcT => ?_⟩
    · have hY : Y ζ = M T ζ := by
        simp only [hYdef]
        rw [hs T]
        exact stoppedProcess_eq_of_le hlt.le
      have hIv : I ζ = ∫ u in Set.Icc (0 : ℝ) T, G (u, X u.toNNReal ζ) := by
        simp only [hIdef]
        rw [← setIntegral_congr_set Ioo_ae_eq_Icc]
        refine setIntegral_congr_fun measurableSet_Ioo fun r hr' => ?_
        exact if_pos (lt_trans (by exact_mod_cast hr'.2) hlt)
      rw [hIv, hY, ← mul_add, ← mul_add, hr T hT.le le_rfl]
    · obtain ⟨hc0, -⟩ := (hg.2 c hc)
      have hY : Y ζ = M c ζ := by
        simp only [hYdef]
        rw [hs T, stoppedProcess_apply_coe hc, min_eq_right hcT]
      have hIv : I ζ = ∫ u in Set.Icc (0 : ℝ) c, G (u, X u.toNNReal ζ) := by
        simp only [hIdef]
        rw [← setIntegral_congr_set Ioo_ae_eq_Icc]
        have e : (fun r : ℝ => if ((r : ℝ) : WithTop ℝ) < τ ζ then G (r, X r.toNNReal ζ) else 0) =
            Set.indicator (Set.Iio c) (fun r => G (r, X r.toNNReal ζ)) := by
          funext r
          rw [Set.indicator_apply, hc]
          simp
        rw [e, setIntegral_indicator measurableSet_Iio]
        have : Set.Ioo (0 : ℝ) T ∩ Set.Iio c = Set.Ioo 0 c := by
          ext r; simp only [Set.mem_inter_iff, Set.mem_Ioo, Set.mem_Iio]
          constructor
          · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
          · rintro ⟨h1, h2⟩; exact ⟨⟨h1, lt_of_lt_of_le h2 hcT⟩, h2⟩
        rw [this]
      rw [hIv, hY, ← mul_add, ← mul_add, hr c hc0 hcT]

end HRS.MS.S113X2

end
