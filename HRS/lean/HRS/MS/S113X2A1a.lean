import HRS.MS.S113X2Defs
import HRS.MH.DualityRdA4

/-!
# S11.3 X2 part A1a: Itô's formula for space-time test functions along the particle process

`s113a_ito_gen`: for `Φ ∈ C²(ℝ × (ℝ^d)^N)` and the filtered particle solution, a.s. for all `t ≤ T`,
`Φ(t, X_t) = Φ(0, X_0) + ∫_0^t (𝓛Φ)(s, X_s) ds + M_t` with `M` the local Itô integral of `itoIntegrand`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113X2

open HRS HRS.Whole

variable {d N : ℕ}

/-! ### Pointwise identities between slice derivatives and product derivatives -/

theorem s113a_slice_hasFDerivAt (Phi : ℝ × EucConfig d N → ℝ) (hPhi : Differentiable ℝ Phi) (s : ℝ)
    (x : EucConfig d N) :
    HasFDerivAt (fun y : EucConfig d N => Phi (s, y))
      ((fderiv ℝ Phi (s, x)).comp (ContinuousLinearMap.inr ℝ ℝ (EucConfig d N))) x := by
  have h1 : HasFDerivAt (fun y : EucConfig d N => ((s, y) : ℝ × EucConfig d N))
      (ContinuousLinearMap.inr ℝ ℝ (EucConfig d N)) x :=
    (hasFDerivAt_const s x).prodMk (hasFDerivAt_id x) |>.congr_fderiv (by
      ext <;> simp)
  exact (hPhi (s, x)).hasFDerivAt.comp x h1

theorem s113a_slice_fderiv (Phi : ℝ × EucConfig d N → ℝ) (hPhi : Differentiable ℝ Phi) (s : ℝ)
    (x v : EucConfig d N) :
    fderiv ℝ (fun y : EucConfig d N => Phi (s, y)) x v = fderiv ℝ Phi (s, x) (0, v) := by
  rw [(s113a_slice_hasFDerivAt Phi hPhi s x).fderiv]
  rfl

theorem s113a_slice_fderiv2 (Phi : ℝ × EucConfig d N → ℝ) (hPhi : ContDiff ℝ 2 Phi) (s : ℝ)
    (x v w : EucConfig d N) :
    fderiv ℝ (fderiv ℝ (fun y : EucConfig d N => Phi (s, y))) x v w =
      fderiv ℝ (fderiv ℝ Phi) (s, x) (0, v) (0, w) := by
  have hd : Differentiable ℝ Phi := hPhi.differentiable (by norm_num)
  have hD : Differentiable ℝ (fderiv ℝ Phi) :=
    (hPhi.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  set L := ContinuousLinearMap.inr ℝ ℝ (EucConfig d N) with hL
  have e1 : fderiv ℝ (fun y : EucConfig d N => Phi (s, y)) = fun y =>
      (ContinuousLinearMap.compL ℝ (EucConfig d N) (ℝ × EucConfig d N) ℝ).flip L
        (fderiv ℝ Phi (s, y)) := by
    funext y
    exact (s113a_slice_hasFDerivAt Phi hd s y).fderiv
  have hg : HasFDerivAt (fun y : EucConfig d N => ((s, y) : ℝ × EucConfig d N)) L x :=
    (hasFDerivAt_const s x).prodMk (hasFDerivAt_id x) |>.congr_fderiv (by
      ext <;> simp [hL])
  have h3 : HasFDerivAt (fun y : EucConfig d N => fderiv ℝ Phi (s, y))
      ((fderiv ℝ (fderiv ℝ Phi) (s, x)).comp L) x := (hD (s, x)).hasFDerivAt.comp x hg
  have h4 := ((ContinuousLinearMap.compL ℝ (EucConfig d N) (ℝ × EucConfig d N) ℝ).flip L).hasFDerivAt.comp x h3
  rw [e1]
  exact congrArg (fun M => M v w) h4.fderiv

theorem s113a_time_derivWithin (Phi : ℝ × EucConfig d N → ℝ) (hPhi : Differentiable ℝ Phi) {T s : ℝ}
    (hT : 0 < T) (hs : s ∈ Set.Icc 0 T) (x : EucConfig d N) :
    derivWithin (fun r : ℝ => Phi (r, x)) (Set.Icc 0 T) s = fderiv ℝ Phi (s, x) (1, 0) := by
  have h1 : HasDerivAt (fun r : ℝ => ((r, x) : ℝ × EucConfig d N)) ((1, 0) : ℝ × EucConfig d N) s :=
    (hasDerivAt_id s).prodMk (hasDerivAt_const s x)
  have h2 := (hPhi (s, x)).hasFDerivAt.comp_hasDerivAt s h1
  exact h2.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hT s hs)

/-- The drift of Itô's formula along the noise directions `√(2β⁻¹) e_k` equals the space-time generator. -/
theorem s113a_itoDrift_eq (Phi : ℝ × EucConfig d N → ℝ) (hPhi : ContDiff ℝ 2 Phi) {T s : ℝ}
    (hT : 0 < T) (hs : s ∈ Set.Icc 0 T) (x : EucConfig d N) (b : EucConfig d N) {invβ : ℝ}
    (hinv : 0 ≤ invβ) :
    derivWithin (fun r : ℝ => Phi (r, x)) (Set.Icc 0 T) s +
      fderiv ℝ (fun y : EucConfig d N => Phi (s, y)) x b +
      (1 / 2) * ∑ k : Fin N × Fin d,
        fderiv ℝ (fderiv ℝ (fun y : EucConfig d N => Phi (s, y))) x
          (Real.sqrt (2 * invβ) • Pi.single k.1 (EuclideanSpace.single k.2 (1 : ℝ)) : EucConfig d N)
          (Real.sqrt (2 * invβ) • Pi.single k.1 (EuclideanSpace.single k.2 (1 : ℝ)) : EucConfig d N)
      = HRS.MC.CepP3.Lop invβ (fun _ => b) Phi (s, x) := by
  have hd : Differentiable ℝ Phi := hPhi.differentiable (by norm_num)
  have hsum : (1 / 2 : ℝ) * ∑ k : Fin N × Fin d,
        fderiv ℝ (fderiv ℝ (fun y : EucConfig d N => Phi (s, y))) x
          (Real.sqrt (2 * invβ) • Pi.single k.1 (EuclideanSpace.single k.2 (1 : ℝ)) : EucConfig d N)
          (Real.sqrt (2 * invβ) • Pi.single k.1 (EuclideanSpace.single k.2 (1 : ℝ)) : EucConfig d N)
      = invβ * ∑ k : Fin N × Fin d, fderiv ℝ (fderiv ℝ Phi) (s, x)
          (0, HRS.configBasis d N k) (0, HRS.configBasis d N k) := by
    have hc : Real.sqrt (2 * invβ) * Real.sqrt (2 * invβ) = 2 * invβ :=
      Real.mul_self_sqrt (by linarith)
    have : ∀ k : Fin N × Fin d,
        fderiv ℝ (fderiv ℝ (fun y : EucConfig d N => Phi (s, y))) x
          (Real.sqrt (2 * invβ) • Pi.single k.1 (EuclideanSpace.single k.2 (1 : ℝ)) : EucConfig d N)
          (Real.sqrt (2 * invβ) • Pi.single k.1 (EuclideanSpace.single k.2 (1 : ℝ)) : EucConfig d N)
        = (2 * invβ) * fderiv ℝ (fderiv ℝ Phi) (s, x)
          (0, HRS.configBasis d N k) (0, HRS.configBasis d N k) := by
      intro k
      rw [s113a_slice_fderiv2 Phi hPhi]
      have e : ((0 : ℝ), (Real.sqrt (2 * invβ) • Pi.single k.1 (EuclideanSpace.single k.2 (1 : ℝ)) : EucConfig d N))
          = Real.sqrt (2 * invβ) • ((0 : ℝ), HRS.configBasis d N k) := by
        ext <;> simp [HRS.configBasis]
      rw [e]
      simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
      rw [← mul_assoc, hc]
    simp only [this]
    rw [← Finset.mul_sum]
    ring
  unfold HRS.MC.CepP3.Lop
  rw [s113a_time_derivWithin Phi hd hT hs, s113a_slice_fderiv Phi hd]
  linarith [hsum]

/-! ### Itô's formula along the particle solution -/

theorem s113a_measurable_drift (d : ℕ) (s q β : ℝ) (N : ℕ) :
    Measurable fun x : EucConfig d N => fun i => particleDriftW (quadraticGradientDyn d s q β) x i := by
  have hGV : Measurable (gradient (quadraticGradientDyn d s q β).V) := by
    unfold gradient
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.measurable.comp
      (measurable_fderiv ℝ _)
  exact HRS.Whole.Q09B.q09b_measurable_driftVec (quadraticGradientDyn d s q β) hGV

/-- Itô's formula for a `C²` space-time function along the filtered particle solution. -/
theorem s113a_ito_gen {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {s q β : ℝ} (hβ : 0 < β) {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hsol : IsWholeStrongSolution P (quadraticGradientDyn d s q β) T X₀ W X)
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hF : IsWholeFilteredSolution P ℱ W' W X)
    (Phi : ℝ × EucConfig d N → ℝ) (hPhi : ContDiff ℝ 2 Phi) :
    ∀ᵐ om ∂P,
      IntegrableOn (fun r : ℝ => s113a_gen d s q β N Phi (r, X (Real.toNNReal r) om)) (Set.Icc 0 T) ∧
      ∀ t : ℝ≥0, (t : ℝ) ≤ T →
        Phi (t, X t om) = Phi (0, X 0 om) +
          (∫ r in Set.Icc (0 : ℝ) t, s113a_gen d s q β N Phi (r, X (Real.toNNReal r) om)) +
          localItoIntegral P ℱ W' (itoIntegrand T Set.univ (fun r (x : EucConfig d N) => Phi (r, x))
            (ofNNRealTime X) (fun _ _ => HRS.MH.DualityRd.noiseDir (quadraticGradientDyn d s q β))) t om := by
  classical
  set D := quadraticGradientDyn d s q β with hD
  have hinv : 0 ≤ D.invβ := by simp [hD, quadraticGradientDyn, inv_nonneg, hβ.le]
  have hbm := s113a_measurable_drift d s q β N
  have hZint : ∀ᵐ ζ ∂P, ∀ τ : ℝ≥0, (τ : ℝ) ≤ T →
      X τ ζ = X 0 ζ + (∫ s in Set.Icc (0 : ℝ) τ, particleDriftW D (X (Real.toNNReal s) ζ))
        + ∑ k, (W' τ ζ k - W' 0 ζ k) • HRS.MH.DualityRd.noiseDir D k := by
    filter_upwards [hsol.eqn, hF.coords] with ζ h1 h2 τ hτ
    obtain ⟨hI, h1⟩ := h1 τ hτ
    have e : ∀ k : Fin N × Fin d, W' τ ζ k - W' 0 ζ k
        = (fun l => W τ ζ l - W 0 ζ l) k.1 k.2 := by
      intro k
      have h3 := h2 τ k.1 k.2
      have h4 := h2 0 k.1 k.2
      rw [Prod.mk.eta] at h3 h4
      rw [h3, h4]
      simp
    funext i
    have hsum : (∑ k : Fin N × Fin d, (W' τ ζ k - W' 0 ζ k) • HRS.MH.DualityRd.noiseDir D k) i
        = Real.sqrt (2 * D.invβ) • (W τ ζ i - W 0 ζ i) := by
      simp only [e]
      exact HRS.MH.DualityRd.da4_sum_noiseDir_apply D (fun l => W τ ζ l - W 0 ζ l) i
    have hIi : Integrable (fun s : ℝ => particleDriftW D (X (Real.toNNReal s) ζ)) (volume.restrict (Set.Icc 0 (τ : ℝ))) :=
      integrable_pi_iff.2 hI
    simp only [Pi.add_apply]
    rw [hsum, HRS.MH.DualityRd.da4_integral_apply _ i hIi, ← h1 i]
  have hbint : ∀ᵐ ζ ∂P, IntegrableOn (fun s : ℝ => particleDriftW D (X (Real.toNNReal s) ζ)) (Set.Icc 0 T) := by
    filter_upwards [hsol.eqn] with ζ h1
    have htnn : (0 : ℝ) ≤ T := hT.le
    have htt : ((Real.toNNReal T : ℝ≥0) : ℝ) = T := Real.coe_toNNReal T htnn
    obtain ⟨hI, -⟩ := h1 (Real.toNNReal T) (le_of_eq htt)
    rw [htt] at hI
    exact integrable_pi_iff.2 hI
  have hX₀ : ∀ s : ℝ, Measurable[ℱ s] (X 0) := by
    intro s
    rcases le_or_gt 0 s with hs | hs
    · exact (hF.adapted 0).mono (ℱ.mono (by simpa using hs)) le_rfl
    · have h := hF.progressive.adapted s
      have e : ofNNRealTime X s = X 0 := by
        funext ξ
        simp [ofNNRealTime_apply, Real.toNNReal_of_nonpos hs.le]
      rw [e] at h
      exact h
  have hb : MeasureTheory.IsProgressive ℱ
      (ofNNRealTime (fun (s : ℝ≥0) (ξ : Ω) => particleDriftW D (X s ξ))) :=
    fun i => hbm.comp (hF.progressive i)
  have hito := ito_formula_additive (P := P) (ℱ := ℱ) hF.brownian (T := T) hT.le
    (fun r (Y : EucConfig d N) => Phi (r, Y)) (isC12On_of_contDiff_joint T Set.univ _ (by
      simpa [Function.uncurry_def] using hPhi))
    (HRS.MH.DualityRd.noiseDir D) X hsol.adapted hX₀ (fun (s : ℝ≥0) (ξ : Ω) => particleDriftW D (X s ξ))
    hb hbint hZint
  filter_upwards [hito] with om hom
  obtain ⟨hI, hE⟩ := hom
  have hdr : ∀ r ∈ Set.Icc (0 : ℝ) T,
      itoDrift T (fun r (Y : EucConfig d N) => Phi (r, Y)) (ofNNRealTime X)
        (ofNNRealTime (fun (s : ℝ≥0) (ξ : Ω) => particleDriftW D (X s ξ)))
        (fun _ _ => HRS.MH.DualityRd.noiseDir D) r om
      = s113a_gen d s q β N Phi (r, X (Real.toNNReal r) om) := by
    intro r hr
    have := s113a_itoDrift_eq Phi hPhi hT hr (X (Real.toNNReal r) om)
      (fun i => particleDriftW D (X (Real.toNNReal r) om) i) hinv
    unfold itoDrift
    simp only [ofNNRealTime_apply, HRS.MH.DualityRd.noiseDir]
    exact this
  refine ⟨hI.congr_fun hdr measurableSet_Icc, fun t ht => ?_⟩
  rw [hE t ht]
  congr 2
  exact setIntegral_congr_fun measurableSet_Icc fun r hr => hdr r ⟨hr.1, hr.2.trans ht⟩

end HRS.MS.S113X2

end
