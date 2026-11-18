import HRS.Energy.StaticLimitEnergy
import HRS.Energy.StaticLimitTiltedCore

/-!
# Identification of Gaussian laws on `H^{-m}_0` (work package STAT-4.21)
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.StaticLimitAux

open HRS Torus

variable {d : ℕ} {m : ℝ}

open Complex

open Classical in
theorem isSmooth_realMode' (k : NonzeroLattice d) : Torus.IsSmooth (Torus.realMode k) := by
  unfold Torus.IsSmooth Torus.IsCk
  have hdot : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Euc d => Lattice.dot k.1 y) := by
    unfold Lattice.dot
    refine ContDiff.sum fun i _ => contDiff_const.mul ?_
    exact (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff
  have hlift : Torus.lift (Torus.realMode k) = fun y : Euc d =>
      if Lattice.IsPosHalf k.1 then Real.sqrt 2 * Real.cos (2 * Real.pi * Lattice.dot k.1 y)
      else Real.sqrt 2 * Real.sin (2 * Real.pi * Lattice.dot k.1 y) := by
    funext y
    unfold Torus.lift Torus.realMode
    simp only [Function.comp, Torus.cosMode_mk, Torus.sinMode_mk]
  rw [hlift]
  split_ifs
  · exact contDiff_const.mul (Real.contDiff_cos.comp (contDiff_const.mul hdot))
  · exact contDiff_const.mul (Real.contDiff_sin.comp (contDiff_const.mul hdot))

open Classical in
theorem avec_realMode (k : NonzeroLattice d) :
    avec m (isSmooth_realMode' k) = Lattice.jp k.1 ^ m • (negBasis d m k : NegSobolev d m) := by
  refine NegSobolev.ext_coord' fun l => ?_
  rw [coord_avec, negBasis_apply]
  show _ = Lattice.jp k.1 ^ m * (show lp (fun _ : NonzeroLattice d => ℝ) 2 from
    lp.single 2 k (1 : ℝ)) l
  rw [lp.single_apply]
  unfold funRealCoeff
  have h := realMode_orthonormal l k
  rw [h]
  by_cases hlk : l = k
  · subst hlk; simp [Lattice.jp]
  · simp [hlk, Ne.symm hlk]


theorem bilin_ext_smooth (A A' : NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ)
    (h : ∀ φ ψ : Torus d → ℝ, ∀ (hφ : Torus.IsSmooth φ) (hψ : Torus.IsSmooth ψ),
      A (avec m hφ) (avec m hψ) = A' (avec m hφ) (avec m hψ)) : A = A' := by
  have hdense : Dense (Submodule.span ℝ (Set.range (negBasis d m)) : Set (NegSobolev d m)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr (negBasis d m).dense_span
  have hjp : ∀ k : NonzeroLattice d, (Lattice.jp k.1 ^ m) ≠ 0 := fun k =>
    (Real.rpow_pos_of_pos (Torus.jp_pos k.1) m).ne'
  have hb : ∀ k l : NonzeroLattice d, A (negBasis d m k) (negBasis d m l) =
      A' (negBasis d m k) (negBasis d m l) := by
    intro k l
    have h1 := h _ _ (isSmooth_realMode' k) (isSmooth_realMode' l)
    rw [avec_realMode, avec_realMode] at h1
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul] at h1
    exact mul_left_cancel₀ (hjp k) (mul_left_cancel₀ (hjp l) h1)
  refine ContinuousLinearMap.ext_on hdense ?_
  rintro _ ⟨k, rfl⟩
  refine ContinuousLinearMap.ext_on hdense ?_
  rintro _ ⟨l, rfl⟩
  exact hb k l

/-- A centered Gaussian on `H^{-m}_0` whose covariance on smooth test functions is
prescribed has covariance form `A`. -/
theorem covarianceBilin_eq_of_smooth (A : NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ)
    (γ : Measure (NegSobolev d m)) (hγ : IsCenteredGaussian γ)
    (h : ∀ φ ψ : Torus d → ℝ, ∀ (hφ : Torus.IsSmooth φ) (hψ : Torus.IsSmooth ψ),
      ∫ F, NegSobolev.eval F φ * NegSobolev.eval F ψ ∂γ = A (avec m hφ) (avec m hψ)) :
    ProbabilityTheory.covarianceBilin γ = A := by
  refine bilin_ext_smooth _ _ fun φ ψ hφ hψ => ?_
  have := hγ.1
  have hmem : MemLp id 2 γ := ProbabilityTheory.IsGaussian.memLp_two_id
  have h2 := ProbabilityTheory.covarianceBilin_apply hmem (avec m hφ) (avec m hψ)
  rw [HilbertCLTAux.gaussian_mean_zero hγ] at h2
  rw [h2, ← h φ ψ hφ hψ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun F => ?_)
  simp only [Pi.zero_apply, sub_zero, id]
  rw [eval_eq_inner m hφ, eval_eq_inner m hψ, real_inner_comm (avec m hφ), real_inner_comm (avec m hψ)]

/-- Centered Gaussian measures on a Hilbert space with the same covariance form coincide. -/
theorem gaussian_ext_of_cov {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]
    (γ γ' : Measure H) (hγ : IsCenteredGaussian γ) (hγ' : IsCenteredGaussian γ')
    (hc : ProbabilityTheory.covarianceBilin γ = ProbabilityTheory.covarianceBilin γ') : γ = γ' := by
  have h1 := hγ.1
  have h2 := hγ'.1
  refine Measure.ext_of_charFun (funext fun t => ?_)
  rw [ProbabilityTheory.IsGaussian.charFun_eq', ProbabilityTheory.IsGaussian.charFun_eq',
    HilbertCLTAux.gaussian_mean_zero hγ, HilbertCLTAux.gaussian_mean_zero hγ', hc]


/-- **Gaussian tilt identification** (source lines 5558-5600): the `H^{-m}_0`-marginal of the
Gaussian law `Γ` of `(δ_x - μ, Z(x))` tilted by `exp(-(β/2)‖f‖²)` is the centered Gaussian with
covariance `(I + βK_μ)^{-1}`-form `Cmap`, i.e. with the susceptibility covariance. -/
theorem tilted_marginal_cov (hm : (d : ℝ) < 2 * m) {a : Lattice d → ℝ} (ha0 : ∀ k, 0 ≤ a k)
    (has : Summable a) (μ : Measure (Torus d)) [IsProbabilityMeasure μ] {β : ℝ} (hβ : 0 ≤ β)
    (Γ : Measure (JSp d m)) (hΓ : IsCenteredGaussian Γ)
    (hcov : ∀ x y, ProbabilityTheory.covarianceBilin Γ x y =
      ProbabilityTheory.covarianceBilin (μ.map (Yj m ha0 has μ)) x y) :
    IsCenteredGaussian ((tiltMeasure (tw (qJ d m) β) Γ).map (TJ d m)) ∧
      ProbabilityTheory.covarianceBilin ((tiltMeasure (tw (qJ d m) β) Γ).map (TJ d m)) =
        Cmap μ ha0 has hβ hm := by
  classical
  haveI := hΓ.1
  obtain ⟨γ, hp, hg, hcovγ⟩ := exists_centeredGaussian_of_traceClass (Cmap μ ha0 has hβ hm)
    ⟨Cmap_symm μ ha0 has hβ hm, Cmap_nonneg μ ha0 has hβ hm, Cmap_trace μ ha0 has hβ hm⟩
  have hwm : Measurable (tw (qJ d m) β) := by
    unfold tw; exact Real.measurable_exp.comp (measurable_const.mul
      ((measurable_qJ (d := d) (m := m)).pow_const 2))
  have hw0 : ∀ x, 0 ≤ tw (qJ d m) β x := fun x => (tw_pos _ _ _).le
  have hint : Integrable (tw (qJ d m) β) Γ :=
    Integrable.of_bound hwm.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hw0 x)]; exact tw_le_one _ hβ x)
  have hA : 0 < ∫ y, tw (qJ d m) β y ∂Γ := by
    have h : 0 < ∫ y, Real.exp (-(β / 2) * qJ d m y ^ 2) ∂Γ := integral_exp_pos hint
    exact h
  haveI hprob : IsProbabilityMeasure (tiltMeasure (tw (qJ d m) β) Γ) := by
    refine ⟨?_⟩
    rw [tiltMeasure_eq _ Γ hwm hw0 hA, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact lintegral_ofReal_div _ hwm hw0 Γ hint hA
  haveI : IsProbabilityMeasure ((tiltMeasure (tw (qJ d m) β) Γ).map (TJ d m)) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_TJ (d := d) (m := m)).aemeasurable).2 hprob
  have heq : (tiltMeasure (tw (qJ d m) β) Γ).map (TJ d m) = γ := by
    refine Measure.ext_of_charFun (funext fun t => ?_)
    rw [charFun_tilt_map _ hwm hw0 Γ hA _ (measurable_TJ (d := d) (m := m)),
      HilbertCLTAux.charFun_centered_gaussian hg, hcovγ]
    have h := tilt_ident hm ha0 has μ hβ Γ hΓ hcov t
    have h2 : ∀ z : JSp d m, cexp ((⟪TJ d m z, t⟫ : ℝ) * Complex.I) * (tw (qJ d m) β z : ℂ) =
        cexp (Complex.I * (⟪z.fst, t⟫ : ℝ)) * (tw (qJ d m) β z : ℝ) := fun z => by
      show cexp (((⟪z.fst, t⟫ : ℝ) : ℂ) * Complex.I) * _ = _
      rw [mul_comm ((⟪z.fst, t⟫ : ℝ) : ℂ) Complex.I]
    simp_rw [h2]
    rw [h]
    have hne : ((∫ y, tw (qJ d m) β y ∂Γ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
    field_simp
  rw [heq]
  exact ⟨hg, ContinuousLinearMap.ext fun x => ContinuousLinearMap.ext (hcovγ x)⟩

end HRS.StaticLimitAux
