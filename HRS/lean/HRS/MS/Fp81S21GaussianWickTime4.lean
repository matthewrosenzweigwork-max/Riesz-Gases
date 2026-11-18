import HRS.MS.Fp81S21GaussianWickTime3
import HRS.MS.Fp81S21GaussianWickTime2
import HRS.MS.Fp81S21GaussianWickTime
import HRS.MS.Fp81S21WickCrossPair

/-! Scalar time integrability and assembly of all five cubic integrability clauses.
Only fixed-time Wick algebra is used; no integrated W1/W2 formula is assumed.
Arbitrary chi is transferred pointwise in time by spatial almost-everywhere
agreement, using the same scalar transfer as `s21e_cfi_mono`. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Set
open scoped ENNReal RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.S21E
variable {p : Parameters} {δ : ℝ} {R : Trajectory p δ}

/-- Fixed-time half-Wick pairing, with both half terms combined by symmetry.
The conclusion uses physical volume and the supplied cross-densities. -/
theorem fp81s21_wick_time_quadratic_pair
    (Q : fp81s21_Physical35 p R) (a : ℝ)
    (τ : Fin 3 → Icc (0 : ℝ) p.T) (φ : Fin 3 → Euc p.d → ℝ)
    (χ : Fin 3 → ℝ → Euc p.d → ℝ)
    (hφ : ∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i))
    (hcross : fp81s21_Cross37 Q a τ φ χ hφ) (j k : Fin 3)
    (r : ℝ) (hr : r ∈ Icc 0 (a + p.T)) (f : Euc p.d → ℝ)
    (hf : IsR2WeightedTest (2 * p.d + 8) ((p.d : ℝ) + 2) f) :
    (∫ ω, fp81s21_chartAction Q.E (Q.S.qe Q.src.G0 r ω) f *
      fp81s21_cross37_X Q a τ φ hφ j ω * fp81s21_cross37_X Q a τ φ hφ k ω ∂Q.src.G0.P) =
    ∫ z : Euc p.d × Euc p.d, commutatorKernel p.d p.s (gradient f) z.1 z.2 *
      χ j r z.1 * χ k r z.2 := by
  letI : IsProbabilityMeasure Q.src.G0.P := Q.src.G0.prob
  letI : IsProbabilityMeasure (HRS.Whole.withDensityReal R.ρβ) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  let μ := HRS.Whole.withDensityReal R.ρβ
  let K := fun z : Euc p.d × Euc p.d => commutatorKernel p.d p.s (gradient f) z.1 z.2
  obtain ⟨G, hG, hT, hX, u, hu⟩ := hcross
  obtain ⟨hfμ, hK, hlin, hquad⟩ := Q.weighted r hr.1 f hf
  obtain ⟨hL, hJoint, hW⟩ := Q.supplied_half_wick r hr.1
  have hpair := fp81s21_wick_operator_mixed_pair μ Q.src.G0.P
    (Q.S.T Q.src.G0 r) Q.S.Kstar hL hJoint G hG (hT r hr.1)
    _ _ (hX j) (hX k) (u j r) (u k r)
    (fun g => ((hu j r hr).1 g).2) (fun g => ((hu k r hr).1 g).2) (hK.toLp K)
  have hleft : (∫ ω, fp81s21_chartAction Q.E (Q.S.qe Q.src.G0 r ω) f *
      fp81s21_cross37_X Q a τ φ hφ j ω * fp81s21_cross37_X Q a τ φ hφ k ω ∂Q.src.G0.P) =
      (1 / 2 : ℝ) * ∫ z, K z *
        (u j r z.1 * u k r z.2 + u k r z.1 * u j r z.2) ∂μ.prod μ := by
    calc
      _ = ∫ ω, Q.S.W Q.src.G0 r (hK.toLp K) ω *
          fp81s21_cross37_X Q a τ φ hφ j ω * fp81s21_cross37_X Q a τ φ hφ k ω ∂Q.src.G0.P := by
        apply integral_congr_ae
        filter_upwards [hquad] with ω hω
        rw [hω]
      _ = (1 / 2 : ℝ) * ∫ z, (hK.toLp K) z *
          (u j r z.1 * u k r z.2 + u k r z.1 * u j r z.2) ∂μ.prod μ := by
        rw [hW]
        exact hpair.2
      _ = _ := congrArg ((1 / 2 : ℝ) * ·) (integral_congr_ae
        (hK.coeFn_toLp.mono fun z hz => congrArg (fun w => w * _) hz))
  have h1 := hK.integrable_mul (s21g2_k11b_tensor_memLp (Lp.memLp (u j r)) (Lp.memLp (u k r))).1
  have h2 := hK.integrable_mul (s21g2_k11b_tensor_memLp (Lp.memLp (u k r)) (Lp.memLp (u j r))).1
  change Integrable (fun z => K z * (u j r z.1 * u k r z.2)) (μ.prod μ) at h1
  change Integrable (fun z => K z * (u k r z.1 * u j r z.2)) (μ.prod μ) at h2
  have hswap : (∫ z, K z * (u k r z.1 * u j r z.2) ∂μ.prod μ) =
      ∫ z, K z * (u j r z.1 * u k r z.2) ∂μ.prod μ := by
    calc
      _ = ∫ z : Euc p.d × Euc p.d, K z.swap * (u j r z.2 * u k r z.1) ∂μ.prod μ := by
        apply integral_congr_ae
        filter_upwards with z
        dsimp [K]
        rw [HRS.MS.Comm.comm_symm (gradient f) z.2 z.1]
        ring
      _ = _ := integral_prod_swap (μ := μ) (ν := μ)
        (fun z : Euc p.d × Euc p.d => K z * (u j r z.1 * u k r z.2))
  have hsingle : (1 / 2 : ℝ) * (∫ z, K z *
      (u j r z.1 * u k r z.2 + u k r z.1 * u j r z.2) ∂μ.prod μ) =
      ∫ z, K z * (u j r z.1 * u k r z.2) ∂μ.prod μ := by
    simp_rw [mul_add]
    rw [integral_add h1 h2, hswap]
    ring
  rw [hleft, hsingle]
  have hden : μ.prod μ = (volume : Measure (Euc p.d × Euc p.d)).withDensity
      (fun z => ENNReal.ofReal (R.ρβ z.1) * ENNReal.ofReal (R.ρβ z.2)) := by
    rw [Measure.volume_eq_prod]
    exact prod_withDensity R.thermal.1.1.measurable.ennreal_ofReal R.thermal.1.1.measurable.ennreal_ofReal
  have hm : Measurable (fun z : Euc p.d × Euc p.d =>
      ENNReal.ofReal (R.ρβ z.1) * ENNReal.ofReal (R.ρβ z.2)) :=
    (R.thermal.1.1.measurable.comp measurable_fst).ennreal_ofReal.mul
      (R.thermal.1.1.measurable.comp measurable_snd).ennreal_ofReal
  rw [hden, integral_withDensity_eq_integral_toReal_smul hm
    (ae_of_all _ fun _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)]
  calc
    _ = ∫ z : Euc p.d × Euc p.d,
        K z * (u j r z.1 * R.ρβ z.1) * (u k r z.2 * R.ρβ z.2) := by
      apply integral_congr_ae
      filter_upwards with z
      simp only [smul_eq_mul, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal (R.thermal.1.1.nonneg z.1),
        ENNReal.toReal_ofReal (R.thermal.1.1.nonneg z.2)]
      ring
    _ = _ := integral_congr_ae (s21e_prod_ae (hu j r hr).2 (hu k r hr).2
      (commutatorKernel p.d p.s (gradient f)))

/-- Clause 3: integrability of the literal iterated spatial drift integral. -/
theorem fp81s21_gaussian_wick_time_drift (p : Parameters) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
      ∀ Q : fp81s21_Physical35 p R, ∀ (a : ℝ), 0 ≤ a →
      ∀ (τ : Fin 3 → Icc (0 : ℝ) p.T) (φ : Fin 3 → Euc p.d → ℝ)
        (χ : Fin 3 → ℝ → Euc p.d → ℝ)
        (hφ : ∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i)),
      S21eChiClause p.d p.s p.a p.β p.γ R.ρ p.T a τ φ χ →
      ∀ i : Fin 3, IntegrableOn (fun r => ∫ x, ∫ y,
        commutatorKernel p.d p.s (gradient (fp81s21_wick_time_f R a τ φ i r)) x y *
          χ (i + 1) r x * χ (i + 2) r y) (Icc (0 : ℝ) (a + τ i)) := by
  obtain ⟨δD, hδD, hhalf, hdom⟩ := fp81s21_gaussian_wick_time_dom p
  obtain ⟨δE, hδE, _, horbit⟩ := fp81s21_moving_encoded_clamped_orbits p
  obtain ⟨δC, hδC, _, hcross⟩ := fp81s21_gaussian_cross_density p
  obtain ⟨δS, hδS, _, hspace⟩ := fp81s21_gaussian_wick_time_spatial_drift p
  refine ⟨min δD (min δE (min δC δS)), lt_min hδD (lt_min hδE (lt_min hδC hδS)),
    (min_le_left _ _).trans hhalf, ?_⟩
  intro δ hδ hδle R Q a ha τ φ χ hφ hχ i
  have hle : δ ≤ δD ∧ δ ≤ δE ∧ δ ≤ δC ∧ δ ≤ δS := by simpa only [le_min_iff] using hδle
  letI : IsProbabilityMeasure Q.src.G0.P := Q.src.G0.prob
  have hd := (hdom δ hδ hle.1 R Q a ha τ φ hφ i).1
  have hc := hcross δ hδ hle.2.2.1 R Q a ha τ φ χ hφ hχ
  have hb := (horbit δ hδ hle.2.1 R Q.E a ha τ φ hφ).1 i
  have hs := hspace δ hδ hle.2.2.2 R Q a ha τ φ χ hφ hχ i
  apply hd.integral_prod_right.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  have hw := hb.2.1 r
  simp only [projIcc_of_mem _ hr] at hw
  change (∫ ω, fp81s21_wick_time_D Q a τ φ hφ i ω r ∂Q.src.G0.P) = _
  simp only [fp81s21_wick_time_D]
  rw [fp81s21_wick_time_quadratic_pair Q a τ φ χ hφ hc (i + 1) (i + 2) r
    ⟨hr.1, hr.2.trans (by linarith [(τ i).property.2])⟩ (fp81s21_wick_time_f R a τ φ i r) hw]
  exact integral_prod (fun z : Euc p.d × Euc p.d =>
    commutatorKernel p.d p.s (gradient (fp81s21_wick_time_f R a τ φ i r)) z.1 z.2 *
      χ (i + 1) r z.1 * χ (i + 2) r z.2)
    (by simpa only [fp81s21_wick_time_f, r26t3_coeff, Measure.volume_eq_prod] using hs r hr)

/-- All five exact cubic integrability clauses, on one radius chosen before
any realization, preparation time, tests, or supplied cross-densities. -/
theorem fp81s21_gaussian_wick_time (p : Parameters) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
      ∀ Q : fp81s21_Physical35 p R, ∀ (a : ℝ), 0 ≤ a →
      ∀ (τ : Fin 3 → Icc (0 : ℝ) p.T) (φ : Fin 3 → Euc p.d → ℝ)
        (χ : Fin 3 → ℝ → Euc p.d → ℝ)
        (hφ : ∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i)),
      S21eChiClause p.d p.s p.a p.β p.γ R.ρ p.T a τ φ χ →
      CubicFormulaIntegrable (quadraticGradientDyn p.d p.s p.a p.β) R.ρ p.γ
        (HRS.Whole.withDensityReal (R.ρ 0)) (fun i => a + τ i) φ χ := by
  obtain ⟨δ0, h0, hhalf, hinit⟩ := fp81s21_gaussian_wick_time_initial p
  obtain ⟨δ2, h2, _, hsD⟩ := fp81s21_gaussian_wick_time_spatial_drift p
  obtain ⟨δ3, h3, _, htD⟩ := fp81s21_gaussian_wick_time_drift p
  obtain ⟨δ4, h4, _, hsJ⟩ := fp81s21_gaussian_wick_time_spatial_cov p
  obtain ⟨δ5, h5, _, htJ⟩ := fp81s21_gaussian_wick_time_cov p
  refine ⟨min δ0 (min δ2 (min δ3 (min δ4 δ5))),
    lt_min h0 (lt_min h2 (lt_min h3 (lt_min h4 h5))),
    (min_le_left _ _).trans hhalf, ?_⟩
  intro δ hδ hδle R Q a ha τ φ χ hφ hχ
  have hl : δ ≤ δ0 ∧ δ ≤ δ2 ∧ δ ≤ δ3 ∧ δ ≤ δ4 ∧ δ ≤ δ5 := by
    simpa only [le_min_iff] using hδle
  exact ⟨hinit δ hδ hl.1 R a ha τ φ hφ,
    hsD δ hδ hl.2.1 R Q a ha τ φ χ hφ hχ,
    htD δ hδ hl.2.2.1 R Q a ha τ φ χ hφ hχ,
    hsJ δ hδ hl.2.2.2.1 R Q a ha τ φ χ hφ hχ,
    htJ δ hδ hl.2.2.2.2 R Q a ha τ φ χ hφ hχ⟩

#print axioms fp81s21_wick_time_quadratic_pair
#print axioms fp81s21_gaussian_wick_time_drift
#print axioms fp81s21_gaussian_wick_time
end HRS.Fp81.S21
end
