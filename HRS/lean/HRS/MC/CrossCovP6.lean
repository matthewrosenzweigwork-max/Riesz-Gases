import HRS.Main.HeadlineEdgeworth
import HRS.MC.CrossCovP1
import HRS.MC.CrossCovP2
import HRS.MC.CrossCovP3
import HRS.MC.CrossCovP4
import HRS.MC.CrossCovP5

/-!
# Packet CC6: assembly of the cross-covariance densities

Proves `ccd_cov_linear`, `ccd_cov_bound`, `ccd_single` and `p_assembly` of `HRS/MC/CrossCovSpec.lean`
(statements copied verbatim).  Inputs: CCD1-CCD5 in `HRS.MC.CrossCovP1` ... `HRS.MC.CrossCovP5`.
Helper lemmas carry the prefix `p_cc6_`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CrossCov

open HRS HRS.Main

variable {d : ℕ}

/-! ### CC6 helpers (`p_cc6_*`): linearity of `eval`, Gaussian integrability -/

theorem p_cc6_funRealCoeff_add {ψ ψ' : Torus d → ℝ} (hψ : Torus.IsSmooth ψ)
    (hψ' : Torus.IsSmooth ψ') (k : NonzeroLattice d) :
    Torus.funRealCoeff (ψ + ψ') k = Torus.funRealCoeff ψ k + Torus.funRealCoeff ψ' k := by
  have h1 : Integrable (fun x => Torus.realMode k x * ψ x) :=
    ((p_cc3_continuous (p_cc1_smooth_realMode k)).mul (p_cc3_continuous hψ)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have h2 : Integrable (fun x => Torus.realMode k x * ψ' x) :=
    ((p_cc3_continuous (p_cc1_smooth_realMode k)).mul (p_cc3_continuous hψ')).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  unfold Torus.funRealCoeff
  rw [← integral_add h1 h2]
  congr 1
  funext x
  simp only [Pi.add_apply]
  ring

theorem p_cc6_funRealCoeff_smul (c : ℝ) (ψ : Torus d → ℝ) (k : NonzeroLattice d) :
    Torus.funRealCoeff (c • ψ) k = c * Torus.funRealCoeff ψ k := by
  unfold Torus.funRealCoeff
  rw [← integral_const_mul]
  congr 1
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem p_cc6_funRealCoeff_const (c : ℝ) (k : NonzeroLattice d) :
    Torus.funRealCoeff (fun _ : Torus d => c) k = 0 := by
  unfold Torus.funRealCoeff
  simp only [integral_mul_const, Torus.integral_realMode, zero_mul]

theorem p_cc6_avec_add {m : ℝ} {ψ ψ' : Torus d → ℝ} (hψ : Torus.IsSmooth ψ)
    (hψ' : Torus.IsSmooth ψ') :
    HRS.StaticLimitAux.avec m (p_cc1_smooth_add hψ hψ') =
      HRS.StaticLimitAux.avec m hψ + HRS.StaticLimitAux.avec m hψ' := by
  apply Subtype.ext
  funext k
  show Lattice.jp k.1 ^ m * Torus.funRealCoeff (ψ + ψ') k =
    Lattice.jp k.1 ^ m * Torus.funRealCoeff ψ k + Lattice.jp k.1 ^ m * Torus.funRealCoeff ψ' k
  rw [p_cc6_funRealCoeff_add hψ hψ' k]
  ring

theorem p_cc6_eval_add {m : ℝ} (F : NegSobolev d m) {ψ ψ' : Torus d → ℝ}
    (hψ : Torus.IsSmooth ψ) (hψ' : Torus.IsSmooth ψ') :
    NegSobolev.eval F (ψ + ψ') = NegSobolev.eval F ψ + NegSobolev.eval F ψ' := by
  rw [HRS.StaticLimitAux.eval_eq_inner m (p_cc1_smooth_add hψ hψ') F, p_cc6_avec_add hψ hψ',
    inner_add_right, HRS.StaticLimitAux.eval_eq_inner m hψ F,
    HRS.StaticLimitAux.eval_eq_inner m hψ' F]

theorem p_cc6_eval_smul {m : ℝ} (F : NegSobolev d m) (c : ℝ) (ψ : Torus d → ℝ) :
    NegSobolev.eval F (c • ψ) = c * NegSobolev.eval F ψ := by
  unfold NegSobolev.eval
  rw [← tsum_mul_left]
  exact tsum_congr fun k => by rw [p_cc6_funRealCoeff_smul]; ring

theorem p_cc6_eval_const {m : ℝ} (F : NegSobolev d m) (c : ℝ) :
    NegSobolev.eval F (fun _ : Torus d => c) = 0 := by
  unfold NegSobolev.eval
  simp only [p_cc6_funRealCoeff_const, mul_zero, tsum_zero]

theorem p_cc6_eval_eq_innerSL {m : ℝ} {g : Torus d → ℝ} (hg : Torus.IsSmooth g) :
    (fun F : NegSobolev d m => NegSobolev.eval F g) =
      ⇑(innerSL ℝ (HRS.StaticLimitAux.avec m hg)) := by
  funext F
  rw [HRS.StaticLimitAux.eval_eq_inner m hg F, innerSL_apply_apply]
  exact real_inner_comm _ _

theorem p_cc6_measurable_eval {m : ℝ} {g : Torus d → ℝ} (hg : Torus.IsSmooth g) :
    Measurable (fun F : NegSobolev d m => NegSobolev.eval F g) := by
  rw [p_cc6_eval_eq_innerSL hg]
  exact (innerSL ℝ _).continuous.measurable

theorem p_cc6_memLp_gauss {m : ℝ} {γ : Measure (NegSobolev d m)} [IsGaussian γ]
    {g : Torus d → ℝ} (hg : Torus.IsSmooth g) :
    MemLp (fun F : NegSobolev d m => NegSobolev.eval F g) 2 γ := by
  rw [p_cc6_eval_eq_innerSL hg]
  exact IsGaussian.memLp_dual γ (innerSL ℝ (HRS.StaticLimitAux.avec m hg)) 2 (by simp)

theorem p_cc6_memLp_init {m : ℝ} {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω')
    (Z₀ : Ω' → NegSobolev d m) (ν : Measure (NegSobolev d m)) [IsGaussian ν]
    (hZ₀ : Measurable Z₀) (hlaw : law P' Z₀ = ν) {g : Torus d → ℝ} (hg : Torus.IsSmooth g) :
    MemLp (fun ω => NegSobolev.eval (Z₀ ω) g) 2 P' := by
  have h1 := p_cc6_memLp_gauss (γ := ν) hg
  rw [← hlaw] at h1
  exact (memLp_map_measure_iff (p_cc6_measurable_eval hg).aestronglyMeasurable
    hZ₀.aemeasurable).1 h1

theorem p_cc6_memLp_coord {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω')
    (G : Ω' → EuclideanSpace ℝ (Fin 1)) (hG : Measurable G) {S : Matrix (Fin 1) (Fin 1) ℝ}
    (hlaw : law P' G = multivariateGaussian 0 S) :
    MemLp (fun ω => G ω 0) 2 P' := by
  have h1 : MemLp (⇑(EuclideanSpace.proj (0 : Fin 1))) 2 (law P' G) := by
    rw [hlaw]
    exact IsGaussian.memLp_dual _ (EuclideanSpace.proj (0 : Fin 1)) 2 (by simp)
  have h2 := (memLp_map_measure_iff
    (EuclideanSpace.proj (0 : Fin 1)).continuous.measurable.aestronglyMeasurable hG.aemeasurable).1 h1
  have e : (⇑(EuclideanSpace.proj (0 : Fin 1)) ∘ G) = fun ω => G ω 0 := by
    funext ω
    simp
  rw [e] at h2
  exact h2

theorem p_cc6_memLp_eval (S : PreparedData d) (β₀ m T' : ℝ) (ν : Measure (NegSobolev d m))
    (hν : IsCenteredGaussianWithCov m ν (preparedCov d S.s β₀ S.μ0))
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z₀ : Ω' → NegSobolev d m) (Z : ℝ → Ω' → NegSobolev d m) (hZ : IsPreparedLinear S m T' ν P' Z₀ Z)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T') {ψ : Torus d → ℝ} (hψ : Torus.IsSmooth ψ) :
    MemLp (fun ω => NegSobolev.eval (Z r ω) ψ) 2 P' := by
  haveI : IsGaussian ν := hν.1.1
  have hU : Torus.IsSmooth (propagator S.dyn S.ρ 0 r ψ) :=
    ccd_propagator_smooth (u := 0) (t := r) S le_rfl hr.1 hψ
  have hC : MemLp (fun ω => NegSobolev.eval (Z₀ ω) (propagator S.dyn S.ρ 0 r ψ)) 2 P' :=
    p_cc6_memLp_init P' Z₀ ν hZ.meas hZ.law_init hU
  have hf : Measurable (fun ω => NegSobolev.eval (Z r ω) ψ -
      NegSobolev.eval (Z₀ ω) (propagator S.dyn S.ρ 0 r ψ)) :=
    ((p_cc6_measurable_eval hψ).comp (hZ.sol.meas r)).sub
      ((p_cc6_measurable_eval hU).comp hZ.meas)
  have hGm : Measurable (fun ω => (WithLp.toLp 2 (fun _ : Fin 1 => NegSobolev.eval (Z r ω) ψ -
      NegSobolev.eval (Z₀ ω) (propagator S.dyn S.ρ 0 r ψ)) : EuclideanSpace ℝ (Fin 1))) :=
    (PiLp.continuous_toLp 2 (fun _ : Fin 1 => ℝ)).measurable.comp (Measurable.of_eval fun _ => hf)
  obtain ⟨-, hlaw⟩ := hZ.sol.gaussian_part 1 (fun _ => r) (fun _ => ψ) (fun _ => hr) (fun _ => hψ)
  have hD : MemLp (fun ω => NegSobolev.eval (Z r ω) ψ -
      NegSobolev.eval (Z₀ ω) (propagator S.dyn S.ρ 0 r ψ)) 2 P' :=
    p_cc6_memLp_coord P' _ hGm hlaw
  convert hD.add hC using 1
  funext ω
  simp

theorem p_cc6_integrable (S : PreparedData d) (β₀ m T' : ℝ) (ν : Measure (NegSobolev d m))
    (hν : IsCenteredGaussianWithCov m ν (preparedCov d S.s β₀ S.μ0))
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z₀ : Ω' → NegSobolev d m) (Z : ℝ → Ω' → NegSobolev d m) (hZ : IsPreparedLinear S m T' ν P' Z₀ Z)
    {r t : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T') (ht : t ∈ Set.Icc (0 : ℝ) T')
    {ψ φ : Torus d → ℝ} (hψ : Torus.IsSmooth ψ) (hφ : Torus.IsSmooth φ) :
    Integrable (fun ω => NegSobolev.eval (Z r ω) ψ * NegSobolev.eval (Z t ω) φ) P' :=
  (p_cc6_memLp_eval S β₀ m T' ν hν P' Z₀ Z hZ hr hψ).integrable_mul
    (p_cc6_memLp_eval S β₀ m T' ν hν P' Z₀ Z hZ ht hφ)

theorem p_cc6_abs_add_mul (A B k a b : ℝ) (hk : 0 ≤ k) (hA : |A| ≤ a) (hB : |B| ≤ b) :
    |A + k * B| ≤ a + k * b := by
  calc |A + k * B| ≤ |A| + |k * B| := abs_add_le _ _
    _ = |A| + k * |B| := by rw [abs_mul, abs_of_nonneg hk]
    _ ≤ a + k * b := add_le_add hA (mul_le_mul_of_nonneg_left hB hk)

/-! ### CCD6: assembly -/

/-- **CCD6a** (`ccd_cov_linear`, glue).  For `r, t ∈ [0,T']` and smooth `φ`, the functional
`ψ ↦ E[Z^r(ψ) Z^t(φ)]` is additive and homogeneous on smooth functions and vanishes on constants (`eval` drops the zero
mode).  Additivity and homogeneity need integrability of the products: `Z^r(ψ), Z^t(φ) ∈ L²(P')` (from the decomposition of
CCD2: a centered Gaussian plus `Z₀(U^{0,r}ψ)` with `Z₀ ~ ν` centered Gaussian) and linearity of `eval` in smooth tests
(summability of the series). -/
theorem ccd_cov_linear (S : PreparedData d) (β₀ m T' : ℝ) (ν : Measure (NegSobolev d m))
    (hν : IsCenteredGaussianWithCov m ν (preparedCov d S.s β₀ S.μ0))
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z₀ : Ω' → NegSobolev d m) (Z : ℝ → Ω' → NegSobolev d m) (hZ : IsPreparedLinear S m T' ν P' Z₀ Z)
    {r t : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T') (ht : t ∈ Set.Icc (0 : ℝ) T')
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    (∀ ψ ψ' : Torus d → ℝ, Torus.IsSmooth ψ → Torus.IsSmooth ψ' →
      ∫ ω, NegSobolev.eval (Z r ω) (ψ + ψ') * NegSobolev.eval (Z t ω) φ ∂P' =
        ∫ ω, NegSobolev.eval (Z r ω) ψ * NegSobolev.eval (Z t ω) φ ∂P' +
        ∫ ω, NegSobolev.eval (Z r ω) ψ' * NegSobolev.eval (Z t ω) φ ∂P') ∧
    (∀ (c : ℝ) (ψ : Torus d → ℝ), Torus.IsSmooth ψ →
      ∫ ω, NegSobolev.eval (Z r ω) (c • ψ) * NegSobolev.eval (Z t ω) φ ∂P' =
        c * ∫ ω, NegSobolev.eval (Z r ω) ψ * NegSobolev.eval (Z t ω) φ ∂P') ∧
    (∀ c : ℝ, ∫ ω, NegSobolev.eval (Z r ω) (fun _ => c) * NegSobolev.eval (Z t ω) φ ∂P' = 0) := by
  refine ⟨fun ψ ψ' hψ hψ' => ?_, fun c ψ hψ => ?_, fun c => ?_⟩
  · have e : ∀ ω, NegSobolev.eval (Z r ω) (ψ + ψ') * NegSobolev.eval (Z t ω) φ =
        NegSobolev.eval (Z r ω) ψ * NegSobolev.eval (Z t ω) φ +
          NegSobolev.eval (Z r ω) ψ' * NegSobolev.eval (Z t ω) φ := by
      intro ω
      rw [p_cc6_eval_add _ hψ hψ']
      ring
    simp only [e]
    exact integral_add (p_cc6_integrable S β₀ m T' ν hν P' Z₀ Z hZ hr ht hψ hφ)
      (p_cc6_integrable S β₀ m T' ν hν P' Z₀ Z hZ hr ht hψ' hφ)
  · have e : ∀ ω, NegSobolev.eval (Z r ω) (c • ψ) * NegSobolev.eval (Z t ω) φ =
        c * (NegSobolev.eval (Z r ω) ψ * NegSobolev.eval (Z t ω) φ) := by
      intro ω
      rw [p_cc6_eval_smul]
      ring
    simp only [e]
    exact integral_const_mul c _
  · have e : ∀ ω, NegSobolev.eval (Z r ω) (fun _ => c) * NegSobolev.eval (Z t ω) φ = 0 := by
      intro ω
      rw [p_cc6_eval_const, zero_mul]
    simp only [e, integral_zero]

/-- **CCD6b** (`ccd_cov_bound`, the `H^{-N}` bound).  For `r, t ∈ [0,T']`, `0 ≤ β₀`, smooth `φ` and every `N`, there is `C`
with `|E[Z^r(ψ) Z^t(φ)]| ≤ C ‖ψ‖_{H^{-N}}` for all smooth `ψ`.  Route: `ccd_cross_cov` splits the covariance into the
initial term, bounded through `ccd_preparedCov_density` (`g = U^{0,t}φ`, smooth by `ccd_propagator_smooth`) and
`ccd_dual_pairing_bound` (`u = 0`, mean-zero `w`), plus the noise term `ccd_noise_bound`. -/
theorem ccd_cov_bound (S : PreparedData d) (β₀ m T' : ℝ) (hβ₀ : 0 ≤ β₀) (ν : Measure (NegSobolev d m))
    (hν : IsCenteredGaussianWithCov m ν (preparedCov d S.s β₀ S.μ0))
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z₀ : Ω' → NegSobolev d m) (Z : ℝ → Ω' → NegSobolev d m) (hZ : IsPreparedLinear S m T' ν P' Z₀ Z)
    {r t : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) T') (ht : t ∈ Set.Icc (0 : ℝ) T')
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (N : ℕ) :
    ∃ C : ℝ, ∀ ψ : Torus d → ℝ, Torus.IsSmooth ψ →
      |∫ ω, NegSobolev.eval (Z r ω) ψ * NegSobolev.eval (Z t ω) φ ∂P'| ≤
        C * HRS.sobolevNorm (-(N : ℝ)) ψ := by
  have hgφ : Torus.IsSmooth (propagator S.dyn S.ρ 0 t φ) :=
    ccd_propagator_smooth (u := 0) (t := t) S le_rfl ht.1 hφ
  obtain ⟨w, hwS, hwmean, hw⟩ := ccd_preparedCov_density S β₀ hβ₀ hgφ
  obtain ⟨C0, hC0, hdual⟩ := ccd_dual_pairing_bound S N
  obtain ⟨C1, hC1, hnoise⟩ := ccd_noise_bound S T' N ht hφ
  refine ⟨C0 * HRS.sobolevNorm (N : ℝ) w + 2 * S.β⁻¹ * C1, fun ψ hψ => ?_⟩
  have hk : 0 ≤ 2 * S.β⁻¹ := mul_nonneg (by norm_num) (inv_nonneg.2 S.hβ.le)
  have hU : Torus.IsSmooth (propagator S.dyn S.ρ 0 r ψ) :=
    ccd_propagator_smooth (u := 0) (t := r) S le_rfl hr.1 hψ
  have h1 : |preparedCov d S.s β₀ S.μ0 (propagator S.dyn S.ρ 0 r ψ) (propagator S.dyn S.ρ 0 t φ)|
      ≤ C0 * HRS.sobolevNorm (N : ℝ) w * HRS.sobolevNorm (-(N : ℝ)) ψ := by
    rw [hw _ hU]
    exact hdual 0 r le_rfl hr.1 w ψ hwS hwmean hψ
  have h2 := hnoise r hr ψ hψ
  rw [ccd_cross_cov S β₀ m T' ν hν P' Z₀ Z hZ hr ht hψ hφ]
  refine le_trans (p_cc6_abs_add_mul _ _ _ _ _ hk h1 h2) (le_of_eq ?_)
  ring

/-- **CCD6c** (`ccd_single`, note §3 CCD6, one observation).  For one observation `(t, φ)` with `t ∈ [0,T']` and smooth
`φ`, there are smooth densities `χ^r` (`r ∈ [0,T']`) with `∫ ψ χ^r = Cov(Z^r(ψ), Z^t(φ))` for all smooth `ψ`.  Route: for
each `r ∈ [0,T']` apply `ccd_smooth_density_of_bound` to `L ψ = E[Z^r(ψ)Z^t(φ)]` (hypotheses from `ccd_cov_linear` and
`ccd_cov_bound`), choose the densities with `Classical.choose` and put `χ r = 0` for `r ∉ [0,T']`. -/
theorem ccd_single (S : PreparedData d) (β₀ m T' : ℝ) (hβ₀ : 0 ≤ β₀) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T')
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    (ν : Measure (NegSobolev d m)) (hν : IsCenteredGaussianWithCov m ν (preparedCov d S.s β₀ S.μ0))
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z₀ : Ω' → NegSobolev d m) (Z : ℝ → Ω' → NegSobolev d m) (hZ : IsPreparedLinear S m T' ν P' Z₀ Z) :
    ∃ χ : ℝ → Torus d → ℝ, (∀ r, Torus.IsSmooth (χ r)) ∧
      ∀ r ∈ Set.Icc (0 : ℝ) T', ∀ ψ : Torus d → ℝ, Torus.IsSmooth ψ →
        ∫ x, ψ x * χ r x = ∫ ω, NegSobolev.eval (Z r ω) ψ * NegSobolev.eval (Z t ω) φ ∂P' := by
  have key : ∀ r : ℝ, ∃ χr : Torus d → ℝ, Torus.IsSmooth χr ∧
      (r ∈ Set.Icc (0 : ℝ) T' → ∀ ψ : Torus d → ℝ, Torus.IsSmooth ψ →
        ∫ x, ψ x * χr x = ∫ ω, NegSobolev.eval (Z r ω) ψ * NegSobolev.eval (Z t ω) φ ∂P') := by
    intro r
    by_cases hr : r ∈ Set.Icc (0 : ℝ) T'
    · have hlin := ccd_cov_linear S β₀ m T' ν hν P' Z₀ Z hZ hr ht hφ
      obtain ⟨χr, hχr, hL⟩ := ccd_smooth_density_of_bound
        (fun ψ => ∫ ω, NegSobolev.eval (Z r ω) ψ * NegSobolev.eval (Z t ω) φ ∂P')
        hlin.1 (fun c ψ hψ => hlin.2.1 c ψ hψ) (fun c => hlin.2.2 c)
        (ccd_cov_bound S β₀ m T' hβ₀ ν hν P' Z₀ Z hZ hr ht hφ)
      exact ⟨χr, hχr, fun _ ψ hψ => hL ψ hψ⟩
    · exact ⟨fun _ => 0, p_cc1_smooth_const 0, fun h => absurd h hr⟩
  choose χ hχs hχL using key
  exact ⟨χ, hχs, fun r hr ψ hψ => hχL r hr ψ hψ⟩

/-- **CCD6d** (`p_assembly`, the frozen target `HRS.Main.cross_cov_densities_exist`, copied verbatim; TeX L1296-1299).
Route: `β₀ ≥ 0` from `hE.β₀_nonneg`, `t i ∈ [a, a+T] ⊆ [0, a+T]` since `a ≥ 0`, `T' = a + T`, then `ccd_single` for
each `i : Fin 3` and `choose`. -/
theorem p_assembly (S : PreparedData d) (β₀ m T a : ℝ) (hE : EdgeworthHyp S β₀ m)
    (hT : 0 < T) (ha : 0 ≤ a) : CrossCovDensitiesExist S β₀ m T a := by
  unfold CrossCovDensitiesExist
  intro t φ ht hφ ν hν Ω' _ P' _ Z₀ Z hZ
  have h : ∀ i : Fin 3, ∃ χi : ℝ → Torus d → ℝ, (∀ r, Torus.IsSmooth (χi r)) ∧
      ∀ r ∈ Set.Icc (0 : ℝ) (a + T), ∀ ψ : Torus d → ℝ, Torus.IsSmooth ψ →
        ∫ x, ψ x * χi r x = ∫ ω, NegSobolev.eval (Z r ω) ψ * NegSobolev.eval (Z (t i) ω) (φ i) ∂P' := by
    intro i
    exact ccd_single (t := t i) S β₀ m (a + T) hE.β₀_nonneg ⟨by linarith [(ht i).1], (ht i).2⟩
      (hφ i) ν hν P' Z₀ Z hZ
  choose χ hχs hχL using h
  exact ⟨χ, fun i r => hχs i r, fun i r hr ψ hψ => hχL i r hr ψ hψ⟩

end HRS.MC.CrossCov

end
