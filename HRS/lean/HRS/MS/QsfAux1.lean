import HRS.MS.ThCorrRespAux3
import HRS.Whole.Thermal

/-!
# S4.5 (`exists_gaussian_feature`, `quadratic_static_field`, `quadratic_static_field_osc`), packet A1

Worker S45.  Namespace `S45` (top level, so that `withDensityReal` etc. are not shadowed by the torus `HRS.*` versions), helper prefix `s45_`.  Frozen rows: `HRS/Whole/Thermal.lean`
(`exists_gaussian_feature` :334, `quadratic_static_field` :352, `quadratic_static_field_osc` :366);
TeX: supplement L2517-2550 (statement), L2551-2645 (proof).  Full plan: `S45_PLAN.md` (scratch directory);
the content is repeated here.

## Verdict on the statements

All three are true and non-vacuous as stated; no statement change is needed.  Junk-value audit:
the Bochner integral `Kop` is a genuine integral for `μ`-a.e. `x` (Schur test with `ρ ≤ M` for `s > 0`;
at `s = 0` exactly because of `HasLogMoment2`, which is why repair P1 was needed); `responseInverse` is the
junk `0` only if no response exists, excluded by conjunct 1 and by a.e. uniqueness of responses (injectivity of
`I + βK`); `featureVec = SeqL2.ofSeq …` is the honest vector because conjunct 1 of `StaticFieldConclusion`
proves `Memℓp` for every configuration (`|pair emp φ_j| ≤ ‖φ_j‖_∞ ≤ cbNorm J φ_j` and `ℓ¹ ⊆ ℓ²`);
`law P featureVec` is the honest law because the feature vector is proved measurable; `smoothDist` (a real
`iSup`) is only used through `Real.iSup_le` with a nonnegative bound; `canonicalGibbs` is a probability measure
by `euc_thermal_canonical_proof` / `logThermal_canonical_proof` and `GibbsWellDefined`; `thermalDensity` exists
by `thermalDensity_spec_proof` / `logThermalDensity_spec_proof` and `tc6_unif` gives `TcRef` (Gaussian bound),
hence `HasLogMoment2` at `s = 0`; `Real.log 0` and `0 ^ (-s)` at coinciding particles are never evaluated (the
diagonal is null and the Gibbs identity regularises the kernel).  `hd : 2 ≤ d`, `N ≥ 2`, the centering
`firstMarginal` is a probability measure, so there is no `d = 0, 1` or `ν = 0` case.  The constant `C` is
quantified before `φ, N, γ` and depends on `d, s, a, β, J` only.

## Merged inputs (exact names)

* S3.3 `HRS.MS.Wr.euc_static_proof`, `euc_static_commutator_proof`; S3.5 `HRS.MS.Wl.r2_log_static_proof`,
  `r2_log_static_commutator_proof`; S3.7 `HRS.Whole.static_stein_hilbert`.
* S3.4/S4.1: `thermalDensity_spec_proof`, `euc_thermal_regularity_proof`, `euc_thermal_canonical_proof`,
  `logThermalDensity_spec_proof`, `logThermal_bounds_proof`, `logThermal_regularity_proof`,
  `logThermal_canonical_proof`, `logThermal_stereographic_proof`.
* S4.4: `HRS.MS.Tc6.thermal_corrector_proof`, `thermal_corrector_sobolev_proof`, `tc6_unif`,
  `HRS.MS.Tc1.tc1_grad_rho`, `tc1_gen_eq_thermal`, `tc1_U_smooth`, `tc1_drift_data`.
* Response operator: `HRS.MS.TcR.tc2_Kc*`, `tc2_pos_log`, `tc2_kop_class_log` (`s = 0`);
  `HRS.Whole.Q34.Kc*`, `kop_class`, `partA`-`partD` (`s > 0`).  Gaussian: `HRS.exists_centeredGaussian_of_traceClass`.
  IBP: Mathlib `integral_bilinear_fderiv_right_eq_neg_left_of_integrable`.

## Packets (each at most 2k lines)

* A1 `QsfAux1` (this file): `HasLogMoment2` gives `log(1+|x|²) ∈ L²(μ)`, Schur bound of the shifted log kernel
  from `ρ ≤ M` alone, the interface `IsKData` (a bounded symmetric nonnegative operator on `L²(ν)` with centered
  range representing `Kop` on centered classes) and its two instances (`s > 0` from Q34, `s = 0` from TC-2).  ~300 lines.
* A2 `QsfAux2`: abstract Lax-Milgram resolvent `Rr`, uniqueness of responses, `T : H →L L²_0`, trace-class
  covariance form, existence of the Gaussian on any separable Hilbert space with a Hilbert basis.  ~550.
* A3 `QsfAux3`, `QsfTie`: `exists_gaussian_feature_proof` and its `type_of%` tie.  ~250.
* B1 `QsfAux4-5`: covariance identification `C_ij = β⁻¹ ∫ ∇χ_i·∇φ_j dμ` with the S4.4 correctors.  ~900.
* B2 `QsfAux6-7`: Gibbs integration by parts for the `N`-particle law (regularised kernel + Mathlib IBP + dominated
  convergence with the bounded symmetrised pair term).  ~900.
* B3 `QsfAux8`: exchangeability, `E μ_N(f) = m_N(f)`, probability measure, unified static bundle `0 ≤ s < d`.  ~500.
* B4 `QsfAux9-10`: `SteinIdentity` with `R`, `T`, bounds `E‖R‖ ≤ C S √δ_N`, `E‖T - C‖₁ ≤ C S² √δ_N`.  ~1000.
* B5 `QsfAux11-12`: `quadratic_static_field_proof` (product coupling, tails, four conjuncts) and tie.  ~900.
* C1 `QsfAux13-15`: `quadratic_static_field_osc_proof` (Hermite coordinates, `Σ‖e_ν‖_{H^J} < ∞` for `m > J + 2d`,
  `H^J` version via `thermal_corrector_sobolev_proof`).  ~1200.
-/

open MeasureTheory Filter Topology Set Metric InnerProductSpace
open scoped ENNReal NNReal

noncomputable section

namespace S45

open HRS.Whole HRS.Whole.Q34 HRS.MS.Thm HRS.MS.TcR
open HRS (Euc cbNorm MemCb smoothDist law IsCenteredGaussian)

variable {d : ℕ}

/-! ### `log(1+|x|²) ∈ L²(μ)` from the second logarithmic moment -/

theorem s45_l_memLp {ρ : Euc d → ℝ} (hρ : IsProbDensity ρ) {L : ℝ}
    (h2 : HasLogMoment2 (withDensityReal ρ) L) :
    MemLp (t67l : Euc d → ℝ) 2 (withDensityReal ρ) := by
  haveI := isProbabilityMeasure_nu hρ
  refine (memLp_two_iff_integrable_sq t67l_measurable.aestronglyMeasurable).2 ?_
  refine Integrable.mono' (h2.1.const_mul 4) (t67l_measurable.pow_const 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have hl0 := t67l_nonneg (d := d) x
  have hx : 0 ≤ ‖x‖ := norm_nonneg x
  have hle : t67l x ≤ 2 * Real.log (2 + ‖x‖) := by
    unfold t67l
    have h1 : Real.log (1 + ‖x‖ ^ 2) ≤ Real.log ((2 + ‖x‖) ^ 2) :=
      Real.log_le_log (by positivity) (by nlinarith)
    rw [Real.log_pow] at h1
    push_cast at h1
    exact h1
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc t67l x ^ 2 ≤ (2 * Real.log (2 + ‖x‖)) ^ 2 := pow_le_pow_left₀ hl0 hle 2
    _ = 4 * Real.log (2 + ‖x‖) ^ 2 := by ring

/-! ### The Schur bound for `K̃ = t67K d` from `ρ ≤ M` and `log ∈ L²(μ)` -/

/-- The Schur bound for `K̃` on `L²(μ)` (the proof of `tc2_bound` with the two hypotheses of its proof,
`ρ ≤ M` and `t67l ∈ L²(μ)`, in place of a Gaussian bound). -/
theorem s45_bound (hd : 1 ≤ d) {ρ : Euc d → ℝ} (hρ : IsProbDensity ρ) {M : ℝ}
    (hM : ∀ x, ρ x ≤ M) (hl2 : MemLp (t67l : Euc d → ℝ) 2 (withDensityReal ρ)) :
    ∃ Mg : ℝ, 0 ≤ Mg ∧ ∀ u : Euc d → ℝ, Measurable u → MemLp u 2 (withDensityReal ρ) →
      ∫⁻ x, tc2_Nu (withDensityReal ρ) (t67K d) u x ^ 2 ∂(withDensityReal ρ) ≤
        ENNReal.ofReal (Mg ^ 2 * ∫ x, u x ^ 2 ∂(withDensityReal ρ)) := by
  haveI := isProbabilityMeasure_nu hρ
  set ν := withDensityReal ρ with hν
  obtain ⟨Cs, hCs0, hCs⟩ := tc2_schur_k1 hd M
  set L := ∫ x, t67l x ^ 2 ∂ν with hL
  have hL0 : 0 ≤ L := integral_nonneg fun x => sq_nonneg _
  refine ⟨Real.sqrt (2 * (Cs ^ 2 + L)), Real.sqrt_nonneg _, fun u hu hu2 => ?_⟩
  set F : Euc d → ℝ≥0∞ := fun y => ENNReal.ofReal |u y| with hF
  have hFm : Measurable F := hu.abs.ennreal_ofReal
  set I := ∫ x, u x ^ 2 ∂ν with hI
  have hI0 : 0 ≤ I := integral_nonneg fun x => sq_nonneg _
  have hF2 : ∫⁻ y, F y ^ 2 ∂ν = ENNReal.ofReal I := tc2_lintegral_sq_abs hu2
  have hlf : ∫⁻ y, ENNReal.ofReal |t67l y| ^ 2 ∂ν = ENNReal.ofReal L :=
    tc2_lintegral_sq_abs hl2
  set c1 : ℝ≥0∞ := ∫⁻ y, ENNReal.ofReal |t67l y| * F y ∂ν with hc1
  have hc1sq : c1 ^ 2 ≤ ENNReal.ofReal L * ENNReal.ofReal I := by
    rw [← hlf, ← hF2]
    exact tc2_cs_sq ν (fun y => ENNReal.ofReal |t67l y|) F
      t67l_measurable.abs.ennreal_ofReal.aemeasurable hFm.aemeasurable
  set A : Euc d → ℝ≥0∞ := fun x => ∫⁻ y, ENNReal.ofReal (tc2_k1 d (x - y)) * F y ∂ν with hA
  have hpt : ∀ x, tc2_Nu ν (t67K d) u x ≤ A x + c1 := by
    intro x
    have hm1 : Measurable (fun y : Euc d => ENNReal.ofReal (tc2_k1 d (x - y)) * F y) :=
      (tc2_k1_measurable.comp (measurable_const.sub measurable_id)).ennreal_ofReal.mul hFm
    calc tc2_Nu ν (t67K d) u x = ∫⁻ y, ENNReal.ofReal (t67K d x y) * F y ∂ν := rfl
      _ ≤ ∫⁻ y, (ENNReal.ofReal (tc2_k1 d (x - y)) * F y +
            ENNReal.ofReal |t67l y| * F y) ∂ν := by
          refine lintegral_mono fun y => ?_
          rw [← add_mul]
          refine mul_le_mul' ?_ le_rfl
          rw [abs_of_nonneg (t67l_nonneg y), ← ENNReal.ofReal_add (tc2_k1_nonneg _)
            (t67l_nonneg y)]
          exact ENNReal.ofReal_le_ofReal (tc2_K_le x y)
      _ = A x + c1 := lintegral_add_left hm1 _
  have hAsq : ∫⁻ x, A x ^ 2 ∂ν ≤ ENNReal.ofReal Cs ^ 2 * ENNReal.ofReal I := by
    rw [← hF2]; exact hCs ρ hρ hM F hFm
  calc ∫⁻ x, tc2_Nu ν (t67K d) u x ^ 2 ∂ν ≤ ∫⁻ x, 2 * (A x ^ 2 + c1 ^ 2) ∂ν :=
        lintegral_mono fun x => (pow_le_pow_left' (hpt x) 2).trans (add_sq_le _ _)
    _ = 2 * (∫⁻ x, A x ^ 2 ∂ν + c1 ^ 2) := by
        rw [lintegral_const_mul' _ _ (by simp), lintegral_add_right _ measurable_const,
          lintegral_const, measure_univ, mul_one]
    _ ≤ 2 * (ENNReal.ofReal Cs ^ 2 * ENNReal.ofReal I + ENNReal.ofReal L * ENNReal.ofReal I) :=
        mul_le_mul' le_rfl (add_le_add hAsq hc1sq)
    _ = ENNReal.ofReal (Real.sqrt (2 * (Cs ^ 2 + L)) ^ 2 * I) := by
        rw [Real.sq_sqrt (by positivity)]
        rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_pow hCs0,
          ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul hL0,
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by norm_num)]
        congr 1; ring

theorem s45_tcker (hd : 1 ≤ d) {ρ : Euc d → ℝ} (hρ : IsProbDensity ρ) {M : ℝ}
    (hM : ∀ x, ρ x ≤ M) (hl2 : MemLp (t67l : Euc d → ℝ) 2 (withDensityReal ρ)) :
    ∃ Mg : ℝ, TcKer (withDensityReal ρ) (t67K d) Mg := by
  obtain ⟨Mg, hMg0, hb⟩ := s45_bound hd hρ hM hl2
  exact ⟨Mg, ⟨t67K_measurable, t67K_nonneg, t67K_symm, hMg0, hb⟩⟩

/-! ### The interface `IsKData` and its two instances -/

/-- `K` is a bounded operator on `L²(ν)` that is symmetric, nonnegative, has centered range, and represents
`Kop g ν` on centered classes. -/
structure IsKData (ν : Measure (Euc d)) [IsProbabilityMeasure ν] (g : Euc d → ℝ)
    (K : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν) : Prop where
  symm : ∀ U V, inner ℝ (K U) V = inner ℝ U (K V)
  pos : ∀ U, 0 ≤ inner ℝ (K U) U
  PK : ∀ U, Pc ν (K U) = K U
  kop : ∀ U : Lp ℝ 2 ν, Pc ν U = U → Kop g ν (U : Euc d → ℝ) =ᵐ[ν] (K U : Euc d → ℝ)

/-- `s = 0`: `K = P T̃ P` for the shifted log kernel; needs `ρ ≤ M` and the second log moment only. -/
theorem s45_kdata_zero (hd : 1 ≤ d) {ρ : Euc d → ℝ} (hρ : IsProbDensity ρ) {M : ℝ}
    (hM : ∀ x, ρ x ≤ M) {L : ℝ} (h2 : HasLogMoment2 (withDensityReal ρ) L) :
    haveI := isProbabilityMeasure_nu hρ
    ∃ K : Lp ℝ 2 (withDensityReal ρ) →L[ℝ] Lp ℝ 2 (withDensityReal ρ),
      IsKData (withDensityReal ρ) (rieszKernel d 0) K := by
  haveI := isProbabilityMeasure_nu hρ
  have hl2 := s45_l_memLp hρ h2
  obtain ⟨Mg, hk⟩ := s45_tcker hd hρ hM hl2
  have hp := tc2_pos_log hd hρ hk
  exact ⟨tc2_Kc hk, ⟨tc2_Kc_symm hk, tc2_Kc_pos hk hp, tc2_Pc_Kc hk, tc2_kop_class_log hρ hk hl2⟩⟩

/-- `0 < s < d`: `K = Kc` of the Q34 chain. -/
theorem s45_kdata_pos (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hsd : s < d) {ρ : Euc d → ℝ}
    (hρ : IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) :
    haveI := isProbabilityMeasure_nu hρ
    ∃ K : Lp ℝ 2 (withDensityReal ρ) →L[ℝ] Lp ℝ 2 (withDensityReal ρ),
      IsKData (withDensityReal ρ) (rieszKernel d s) K := by
  haveI := isProbabilityMeasure_nu hρ
  have h : Q34Hyp d s ρ M := ⟨hd, hs0, hsd, hρ, hM⟩
  exact ⟨Kc h, ⟨Kc_symm h, Kc_pos h, Pc_Kc h,
    fun U hU => kop_class h (Filter.EventuallyEq.refl _ _) hU⟩⟩

/-- Both cases: `0 ≤ s < d`, `ρ ≤ M`, and (at `s = 0`) `HasLogMoment2`. -/
theorem s45_kdata (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Euc d → ℝ}
    (hρ : IsProbDensity ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) {L : ℝ}
    (hL : s = 0 → HasLogMoment2 (withDensityReal ρ) L) :
    haveI := isProbabilityMeasure_nu hρ
    ∃ K : Lp ℝ 2 (withDensityReal ρ) →L[ℝ] Lp ℝ 2 (withDensityReal ρ),
      IsKData (withDensityReal ρ) (rieszKernel d s) K := by
  rcases hs0.eq_or_lt with h | h
  · subst h
    exact s45_kdata_zero hd hρ hM (hL rfl)
  · exact s45_kdata_pos hd h hsd hρ hM

end S45

end
