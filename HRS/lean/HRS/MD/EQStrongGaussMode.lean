import HRS.MD.EQStrongGaussBase

/-!
# EQ-STRONG, Gaussian clause: the coordinate processes

For `0 ≤ s ≤ t` the pair `(Y_s, Y_t)` of the coordinate `Y = ⟨Z, e_k⟩` is centred Gaussian with covariance
`q41_r H`, so the increment is a centred Gaussian of variance `≤ 2 β⁻¹ C_c² ⟨k⟩² (t-s)`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MD.EQStrong

open HRS HRS.Q41 HRS.PDE HRS.PDE.MFAdjoint HRS.PDE.MFLinear HRS.PDE.MFPair

variable {d : ℕ}

section Mode

variable {s β c₀ Λ₀ : ℝ} {V ρβ : Torus d → ℝ} {m : ℝ}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} {Z : ℝ → Ω' → NegSobolev d m}

/-- the finite-dimensional law of the pair `(Y_{t₀}, Y_{t₁})`. -/
theorem eqstrong_pair_law (hs0 : 0 ≤ s) (hsd : s < d) (hβ0 : 0 < β)
    (H : FrozenHyp d s (2 * mStar d + 4) β⁻¹ β⁻¹ c₀ Λ₀ β V ρβ)
    (hZ : IsStationaryGaussianField P' s β hs0 hsd hβ0 V ρβ m Z) (k : NonzeroLattice d)
    {t₀ t₁ : ℝ} (h0 : 0 ≤ t₀) (h1 : 0 ≤ t₁) :
    P'.map (fun ω => (WithLp.toLp 2 fun a : Fin 2 => NegSobolev.eval (Z (![t₀, t₁] a) ω)
        (Torus.realMode k) : EuclideanSpace ℝ (Fin 2))) =
      multivariateGaussian 0 (Matrix.of fun a b : Fin 2 =>
        q41_r H (![t₀, t₁] a) (![t₀, t₁] b) k k) := by
  have hτ : ∀ a : Fin 2, 0 ≤ ![t₀, t₁] a := by
    intro a; fin_cases a <;> simp [h0, h1]
  have hφ : ∀ a : Fin 2, Torus.IsSmooth ((fun _ : Fin 2 => Torus.realMode k) a) :=
    fun _ => q38b_isSmooth_realMode k
  have hlaw := hZ.gaussian 2 ![t₀, t₁] (fun _ => Torus.realMode k) hτ hφ
  have hmat : PDE.stationaryLagCov d s β (PDE.mfData d s hs0 hsd V β hβ0) ρβ ![t₀, t₁]
      (fun _ => Torus.realMode k) = Matrix.of fun a b : Fin 2 =>
        q41_r H (![t₀, t₁] a) (![t₀, t₁] b) k k := by
    ext a b
    simp [q41_r, q41_cov2, PDE.stationaryLagCov]
  rw [hmat] at hlaw
  exact hlaw

/-- `E Y_0² ≤ 8`. -/
theorem eqstrong_zero_moment (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ0 : 0 < β)
    (hV : Torus.IsSmooth V) (hρ : IsThermalDensity (periodicRiesz d s) V β ρβ)
    [IsProbabilityMeasure P']
    (hZ : IsStationaryGaussianField P' s β hs0 hsd hβ0 V ρβ m Z) (k : NonzeroLattice d) :
    ∫⁻ ω, ENNReal.ofReal (NegSobolev.fourierCoeff (Z 0 ω) k ^ 2) ∂P' ≤ ENNReal.ofReal 8 := by
  obtain ⟨hpos, hsm⟩ := Q41.q41_thermal_regular hd hs0 hsd hβ0 hV hρ
  set τ : Fin 2 → ℝ := fun _ => 0 with hτ
  set φ : Fin 2 → Torus d → ℝ := fun _ => Torus.realMode k with hφ
  have hτ0 : ∀ a, 0 ≤ τ a := fun a => le_rfl
  have hφs : ∀ a, Torus.IsSmooth (φ a) := fun _ => q38b_isSmooth_realMode k
  have hlaw := hZ.gaussian 2 τ φ hτ0 hφs
  set W : Ω' → EuclideanSpace ℝ (Fin 2) := fun ω =>
    (WithLp.toLp 2 fun a => NegSobolev.eval (Z (τ a) ω) (φ a) : EuclideanSpace ℝ (Fin 2)) with hW
  have hmeas : ∀ a : Fin 2, Measurable fun ω => NegSobolev.eval (Z (τ a) ω) (φ a) :=
    fun a => (q38b_measurable_eval_realMode k).comp (hZ.meas (τ a))
  have hWm : Measurable W :=
    (MeasurableEquiv.toLp 2 (Fin 2 → ℝ)).measurable.comp (measurable_pi_iff.2 hmeas)
  have hpsd := Q41.q41_lagcov_psd hd hs0 hsd hβ0 hV hρ
    (PoleCavityAux.continuous_of_smoothPos ⟨hρ.1, hsm, hpos⟩) hpos τ hτ0 φ hφs
  have hS01 : PDE.stationaryLagCov d s β (PDE.mfData d s hs0 hsd V β hβ0) ρβ τ φ 0 1 =
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρβ) β (Torus.realMode k)
        (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ0) ρβ 0 (Torus.realMode k)) := by
    simp [PDE.stationaryLagCov, τ, φ]
  have hle := MD.EQInit.eqinit_susc_semigroup_zero_le hd hs0 hsd β hβ0 V hV ρβ hρ k
  have hint := MD.EQInit.eqinit_gauss_prod_integrable P' W hWm.aemeasurable _ hlaw
  have hval := q38b_gauss_prod P' W hWm.aemeasurable _ hpsd hlaw
  have hsq : ∀ ω, W ω 0 * W ω 1 = NegSobolev.eval (Z 0 ω) (Torus.realMode k) ^ 2 := by
    intro ω; simp [hW, τ, φ, sq]
  have hint2 : Integrable (fun ω => NegSobolev.eval (Z 0 ω) (Torus.realMode k) ^ 2) P' := by
    simpa [hsq] using hint
  have hval2 : ∫ ω, NegSobolev.eval (Z 0 ω) (Torus.realMode k) ^ 2 ∂P' ≤ 8 := by
    simp_rw [hsq] at hval
    rw [hval, hS01]; exact hle
  simp_rw [← q38b_eval_realMode]
  rw [← ofReal_integral_eq_lintegral_ofReal hint2
    (Filter.Eventually.of_forall fun ω => sq_nonneg _)]
  exact ENNReal.ofReal_le_ofReal hval2

/-- The fourth moment of the coordinate increments (`0 ≤ s' ≤ t'`). -/
theorem eqstrong_inc4 (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ0 : 0 < β)
    (hV : Torus.IsSmooth V) (hρ : IsThermalDensity (periodicRiesz d s) V β ρβ)
    (H : FrozenHyp d s (2 * mStar d + 4) β⁻¹ β⁻¹ c₀ Λ₀ β V ρβ)
    [IsProbabilityMeasure P']
    (hZ : IsStationaryGaussianField P' s β hs0 hsd hβ0 V ρβ m Z) {Cc : ℝ}
    (hCc : ∀ k : NonzeroLattice d, Torus.cbNorm 1 (Torus.realMode k) ≤ Cc * Lattice.jp k.1 ^ 1)
    (k : NonzeroLattice d) {s' t' : ℝ} (hs' : 0 ≤ s') (hst : s' ≤ t') :
    ∫⁻ ω, ENNReal.ofReal ((NegSobolev.fourierCoeff (Z t' ω) k -
        NegSobolev.fourierCoeff (Z s' ω) k) ^ 4) ∂P' ≤
      ENNReal.ofReal (48 * Real.exp (1 / 2) *
        (2 * β⁻¹ * Cc ^ 2 * Lattice.jp k.1 ^ 2 * (t' - s')) ^ 2) := by
  obtain ⟨hpos, hsm⟩ := Q41.q41_thermal_regular hd hs0 hsd hβ0 hV hρ
  have ht' : 0 ≤ t' := hs'.trans hst
  set f : Fin 2 → Ω' → ℝ := fun a ω => NegSobolev.eval (Z (![s', t'] a) ω) (Torus.realMode k)
    with hf
  have hfm : ∀ a, Measurable (f a) := fun a =>
    (q38b_measurable_eval_realMode k).comp (hZ.meas _)
  have hlaw := eqstrong_pair_law hs0 hsd hβ0 H hZ k hs' ht'
  have hτ : ∀ a : Fin 2, 0 ≤ ![s', t'] a := by
    intro a; fin_cases a <;> simp [hs', ht']
  have hpsd0 := Q41.q41_lagcov_psd hd hs0 hsd hβ0 hV hρ
    (PoleCavityAux.continuous_of_smoothPos ⟨hρ.1, hsm, hpos⟩) hpos ![s', t'] hτ
    (fun _ => Torus.realMode k) (fun _ => q38b_isSmooth_realMode k)
  have hmat : PDE.stationaryLagCov d s β (PDE.mfData d s hs0 hsd V β hβ0) ρβ ![s', t']
      (fun _ => Torus.realMode k) = Matrix.of fun a b : Fin 2 =>
        q41_r H (![s', t'] a) (![s', t'] b) k k := by
    ext a b
    simp [q41_r, q41_cov2, PDE.stationaryLagCov]
  rw [hmat] at hpsd0
  have hdl := eqstrong_diff_law P' f hfm _ hpsd0 hlaw
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hdl
  set v : ℝ := q41_r H s' s' k k + q41_r H t' t' k k - 2 * q41_r H s' t' k k with hv
  have hvb : v ≤ 2 * β⁻¹ * Cc ^ 2 * Lattice.jp k.1 ^ 2 * (t' - s') :=
    eqstrong_key (by omega) H hβ0 hCc k hs' hst
  have hV0 : 0 ≤ 2 * β⁻¹ * Cc ^ 2 * Lattice.jp k.1 ^ 2 * (t' - s') := by
    have := Torus.jp_pos k.1
    have : 0 ≤ t' - s' := by linarith
    positivity
  have hdiff : (fun ω => f 1 ω - f 0 ω) = fun ω => NegSobolev.fourierCoeff (Z t' ω) k -
      NegSobolev.fourierCoeff (Z s' ω) k := by
    funext ω
    simp [hf, q38b_eval_realMode]
  rw [hdiff] at hdl
  have hmeasd : Measurable fun ω => NegSobolev.fourierCoeff (Z t' ω) k -
      NegSobolev.fourierCoeff (Z s' ω) k := by
    rw [← hdiff]; exact (hfm 1).sub (hfm 0)
  have hlm : ∫⁻ ω, ENNReal.ofReal ((NegSobolev.fourierCoeff (Z t' ω) k -
        NegSobolev.fourierCoeff (Z s' ω) k) ^ 4) ∂P' =
      ∫⁻ x, ENNReal.ofReal (x ^ 4) ∂(P'.map fun ω => NegSobolev.fourierCoeff (Z t' ω) k -
        NegSobolev.fourierCoeff (Z s' ω) k) := by
    rw [lintegral_map (by fun_prop) hmeasd]
  rw [hlm, hdl]
  refine (q41_gauss_fourth_lintegral _).trans (ENNReal.ofReal_le_ofReal ?_)
  have hc : ((v.toNNReal : ℝ≥0) : ℝ) ≤ 2 * β⁻¹ * Cc ^ 2 * Lattice.jp k.1 ^ 2 * (t' - s') := by
    rw [Real.coe_toNNReal']
    exact max_le hvb hV0
  have := pow_le_pow_left₀ NNReal.zero_le_coe hc 2
  have h48 : 0 ≤ 48 * Real.exp (1 / 2) := by positivity
  exact mul_le_mul_of_nonneg_left this h48

end Mode

end HRS.MD.EQStrong
