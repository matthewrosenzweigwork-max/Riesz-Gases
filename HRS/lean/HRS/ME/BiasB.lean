import HRS.ME.Marginal

/-!
# Chunk E, row 2.10 (fixed-`β` closure), packet B: the `E_m` norm of the marginal shift

`shift_norm_bound_of_L2`: with `μ = ρ dx` and `M = M_N` the first marginal of the modulated Gibbs law,
`‖√N (M_N - μ) - (log N/√N) b_{β,μ}‖_{E_m} ≤ C √(log N)/√N` for `N ≥ 2`, `d < 2m`.
It follows from `HRS.ME.Marginal.critical_marginal_expansion_fixed` (the `L²(μ)` bound
`C√(log N)/N` on the density `dM_N/dμ - 1 - (log N/N) db/dμ`) and from the bound of the `E_m` norm
of the signed measure `f dx` by `C ‖f‖_{L¹}`, through Fourier coefficients:
`coord (ofMeasureDiff m M μ) k = jp(k)^{-m} (measureRealCoeff M k - measureRealCoeff μ k)` and
`|funRealCoeff f k| ≤ √2 ∫ |f|`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.ME.Bias

variable {d : ℕ}

open HRS HRS.Main
open HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer HRS.CavResp HRS.PDE

/-- A probability density gives a probability measure `ρ dx`. -/
theorem bias_isProb_wdr {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) :
    IsProbabilityMeasure (withDensityReal ρ) := by
  have hint : Integrable ρ :=
    Integrable.of_integral_ne_zero (by rw [hρ.integral_one]; exact one_ne_zero)
  refine ⟨?_⟩
  rw [withDensityReal, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hρ.nonneg),
    hρ.integral_one]
  simp

/-- `∫ φ d(ρ dx) = ∫ φ ρ dx`. -/
theorem integral_withDensityReal_eq {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) (φ : Torus d → ℝ) :
    ∫ x, φ x ∂(withDensityReal ρ) = ∫ x, φ x * ρ x := by
  have hmeas : Measurable (fun x => ENNReal.ofReal (ρ x)) :=
    ENNReal.measurable_ofReal.comp hρ.measurable
  rw [withDensityReal, integral_withDensity_eq_integral_toReal_smul hmeas
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top) φ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hρ.nonneg x)]
  ring

/-- Integrability against `ρ dx` is integrability of `φ ρ` for Lebesgue measure. -/
theorem integrable_withDensityReal_iff {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ)
    {φ : Torus d → ℝ} :
    Integrable φ (withDensityReal ρ) ↔ Integrable (fun x => φ x * ρ x) := by
  have hmeas : Measurable (fun x => ENNReal.ofReal (ρ x)) :=
    ENNReal.measurable_ofReal.comp hρ.measurable
  have hfin : ∀ᵐ x ∂(volume : Measure (Torus d)), ENNReal.ofReal (ρ x) < ⊤ :=
    Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  rw [withDensityReal, integrable_withDensity_iff_integrable_smul' hmeas hfin]
  constructor
  · intro h
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [smul_eq_mul, ENNReal.toReal_ofReal (hρ.nonneg x)]
    ring
  · intro h
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [smul_eq_mul, ENNReal.toReal_ofReal (hρ.nonneg x)]
    ring

/-- Multiplication of an integrable function by the bounded real mode `realMode k`. -/
theorem integrable_realMode_mul {φ : Torus d → ℝ} (hφ : Integrable φ) (k : NonzeroLattice d) :
    Integrable (fun x => Torus.realMode k x * φ x) :=
  hφ.bdd_mul (c := Real.sqrt 2) (Torus.continuous_realMode k).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact Torus.abs_realMode_le k x)

/-- `|f̂(k)| ≤ √2 ∫ |f|` (auxiliary form). -/
theorem funRealCoeff_bound_aux {f : Torus d → ℝ} (hf : Integrable f) (k : NonzeroLattice d) :
    |Torus.funRealCoeff f k| ≤ Real.sqrt 2 * ∫ x, |f x| := by
  unfold Torus.funRealCoeff
  calc |∫ x, Torus.realMode k x * f x|
      = ‖∫ x, Torus.realMode k x * f x‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x, ‖Torus.realMode k x * f x‖ := norm_integral_le_integral_norm _
    _ = ∫ x, |Torus.realMode k x * f x| := by simp only [Real.norm_eq_abs]
    _ ≤ ∫ x, Real.sqrt 2 * |f x| :=
        integral_mono (integrable_realMode_mul hf k).abs (hf.abs.const_mul _) (fun x => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (Torus.abs_realMode_le k x) (abs_nonneg _))
    _ = Real.sqrt 2 * ∫ x, |f x| := integral_const_mul _ _

/-- The coordinates of `ofFun m f` for an integrable `f`. -/
theorem coord_ofFun {m : ℝ} (hm : (d : ℝ) < 2 * m) {f : Torus d → ℝ} (hf : Integrable f)
    (k : NonzeroLattice d) :
    NegSobolev.coord (NegSobolev.ofFun m f) k = Lattice.jp k.1 ^ (-m) * Torus.funRealCoeff f k := by
  have hb : ∃ C, ∀ k : NonzeroLattice d, |Torus.funRealCoeff f k| ≤ C :=
    ⟨Real.sqrt 2 * ∫ x, |f x|, fun k => funRealCoeff_bound_aux hf k⟩
  exact NegSobolev.coord_ofSeq_of_mem (fun k : NonzeroLattice d => Torus.funRealCoeff f k)
    (NegSobolev.memℓp_of_bounded hm (fun k : NonzeroLattice d => Torus.funRealCoeff f k) hb) k

/-- `|f̂(k)| ≤ √2 ∫ |f|` (`realMode k` is bounded by `√2`). -/
theorem abs_funRealCoeff_le_integral {f : Torus d → ℝ} (hf : Integrable f) (k : NonzeroLattice d) :
    |Torus.funRealCoeff f k| ≤ Real.sqrt 2 * ∫ x, |f x| :=
  funRealCoeff_bound_aux hf k

/-- If all weighted coordinates are bounded by `K`, the norm is at most `K · sqrt(∑ jp^{-2m})`. -/
theorem norm_le_of_coord_bound {m : ℝ} (hm : (d : ℝ) < 2 * m) (F : NegSobolev d m) {K : ℝ}
    (hK : 0 ≤ K) (h : ∀ k : NonzeroLattice d, |NegSobolev.coord F k| ≤ K * Lattice.jp k.1 ^ (-m)) :
    ‖F‖ ≤ K * Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m))) := by
  obtain ⟨hs2, hn⟩ := NegSobolev.coord_sq F
  have hs := summable_jp_rpow (d := d) m hm
  have hb : ∀ k : NonzeroLattice d,
      NegSobolev.coord F k ^ 2 ≤ K ^ 2 * Lattice.jp k.1 ^ (-(2 * m)) := by
    intro k
    have h2 : NegSobolev.coord F k ^ 2 ≤ (K * Lattice.jp k.1 ^ (-m)) ^ 2 := by
      have h1 := pow_le_pow_left₀ (abs_nonneg (NegSobolev.coord F k)) (h k) 2
      rwa [sq_abs] at h1
    have h3 : (K * Lattice.jp k.1 ^ (-m)) ^ 2 = K ^ 2 * Lattice.jp k.1 ^ (-(2 * m)) := by
      rw [mul_pow, Torus.jp_rpow_sq, show -(2 * m) = 2 * (-m) by ring]
    exact h2.trans_eq h3
  have hsum := Summable.tsum_le_tsum hb hs2 (hs.mul_left (K ^ 2))
  rw [tsum_mul_left] at hsum
  have hS : 0 ≤ ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m)) :=
    tsum_nonneg fun k => Real.rpow_nonneg (Torus.jp_pos k.1).le _
  have hF2 : ‖F‖ ^ 2 ≤
      (K * Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m)))) ^ 2 := by
    rw [hn, mul_pow, Real.sq_sqrt hS]
    exact hsum
  have hKS : 0 ≤ K * Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m))) :=
    mul_nonneg hK (Real.sqrt_nonneg _)
  nlinarith [norm_nonneg F]

/-- The Fourier coefficients of a measure `M ≪ μ = ρ dx` with density `g = dM/dμ`:
`∫ φ dM = ∫ φ g ρ dx`. -/
theorem measureRealCoeff_eq_funRealCoeff {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ)
    {M : Measure (Torus d)} [IsFiniteMeasure M] (hM : M ≪ withDensityReal ρ) (k : NonzeroLattice d) :
    Torus.measureRealCoeff M k =
      Torus.funRealCoeff (fun y => ((M.rnDeriv (withDensityReal ρ) y).toReal) * ρ y) k := by
  haveI := bias_isProb_wdr hρ
  have hmeas : Measurable (M.rnDeriv (withDensityReal ρ)) := Measure.measurable_rnDeriv M _
  have hlt : ∀ᵐ x ∂(withDensityReal ρ), M.rnDeriv (withDensityReal ρ) x < ⊤ :=
    Measure.rnDeriv_lt_top M _
  have hMeq : (withDensityReal ρ).withDensity (M.rnDeriv (withDensityReal ρ)) = M :=
    Measure.withDensity_rnDeriv_eq M _ hM
  have e0 : ∫ x, Torus.realMode k x ∂M =
      ∫ x, (M.rnDeriv (withDensityReal ρ) x).toReal • Torus.realMode k x ∂(withDensityReal ρ) := by
    rw [← integral_withDensity_eq_integral_toReal_smul hmeas hlt, hMeq]
  unfold Torus.measureRealCoeff Torus.funRealCoeff
  rw [e0]
  refine (integral_withDensityReal_eq hρ _).trans ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [smul_eq_mul]
  ring

/-- `∫ |F ρ| ≤ B` from `‖F‖_{L²(ρ dx)} ≤ B` for a probability density `ρ` (auxiliary form with an
a.e.-measurable `F`). -/
theorem integral_abs_mul_le_aesm {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {F : Torus d → ℝ}
    (hF : AEStronglyMeasurable F (withDensityReal ρ)) {B : ℝ} (hB : 0 ≤ B)
    (h : eLpNorm F 2 (withDensityReal ρ) ≤ ENNReal.ofReal B) :
    Integrable (fun y => F y * ρ y) ∧ ∫ y, |F y * ρ y| ≤ B := by
  haveI := bias_isProb_wdr hρ
  have h1 : eLpNorm F 1 (withDensityReal ρ) ≤ eLpNorm F 2 (withDensityReal ρ) :=
    eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)
  have hfin : ∫⁻ x, ‖F x‖ₑ ∂(withDensityReal ρ) < ⊤ := by
    rw [← eLpNorm_one_eq_lintegral_enorm hF]
    exact lt_of_le_of_lt h1 (lt_of_le_of_lt h ENNReal.ofReal_lt_top)
  have hI : Integrable F (withDensityReal ρ) := ⟨hF, hfin⟩
  have e1 : ENNReal.ofReal (∫ x, ‖F x‖ ∂(withDensityReal ρ)) =
      eLpNorm F 1 (withDensityReal ρ) := by
    rw [eLpNorm_one_eq_lintegral_enorm hF]
    exact ofReal_integral_norm_eq_lintegral_enorm hI
  have hB' : ∫ x, ‖F x‖ ∂(withDensityReal ρ) ≤ B :=
    (ENNReal.ofReal_le_ofReal_iff hB).1 (e1.trans_le (h1.trans h))
  simp only [Real.norm_eq_abs] at hB'
  have hμ : ∫ y, |F y| ∂(withDensityReal ρ) = ∫ y, |F y| * ρ y :=
    integral_withDensityReal_eq hρ (fun y => |F y|)
  have hint : ∫ y, |F y * ρ y| = ∫ y, |F y| * ρ y :=
    integral_congr_ae (Filter.Eventually.of_forall fun y => by
      show |F y * ρ y| = |F y| * ρ y
      rw [abs_mul, abs_of_nonneg (hρ.nonneg y)])
  refine ⟨(integrable_withDensityReal_iff hρ).1 hI, ?_⟩
  rw [hint, ← hμ]
  exact hB'

/-- **The `L²` to `L¹` bound**: `∫ |F ρ| ≤ B` from `‖F‖_{L²(ρ dx)} ≤ B`, and `F ρ` is integrable. -/
theorem integral_abs_mul_le_of_eLpNorm_two {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ)
    {F : Torus d → ℝ} (hF : Measurable F) {B : ℝ} (hB : 0 ≤ B)
    (h : eLpNorm F 2 (withDensityReal ρ) ≤ ENNReal.ofReal B) :
    Integrable (fun y => F y * ρ y) ∧ ∫ y, |F y * ρ y| ≤ B :=
  integral_abs_mul_le_aesm hρ hF.aestronglyMeasurable hB h

/-- The `k`-th coordinate as a linear functional on `NegSobolev d m`. -/
def coordLin {m : ℝ} (k : NonzeroLattice d) : NegSobolev d m →ₗ[ℝ] ℝ where
  toFun F := NegSobolev.coord F k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem coord_sub_smul {m : ℝ} (a b : ℝ) (F G : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord (a • F - b • G) k = a * NegSobolev.coord F k - b * NegSobolev.coord G k := by
  have h := map_sub (coordLin (m := m) k) (a • F) (b • G)
  rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h
  exact h

/-- `coord (ofMeasureDiff m μ ν) k = jp^{-m} (μ̂(k) - ν̂(k))` (copy of the `StaticLimitBasic` fact). -/
theorem coordDiff {m : ℝ} (hm : (d : ℝ) < 2 * m) (μ ν : Measure (Torus d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (k : NonzeroLattice d) :
    NegSobolev.coord (NegSobolev.ofMeasureDiff m μ ν) k =
      Lattice.jp k.1 ^ (-m) * (Torus.measureRealCoeff μ k - Torus.measureRealCoeff ν k) := by
  have h := NegSobolev.fourierCoeff_ofMeasureDiff hm μ ν k
  unfold NegSobolev.fourierCoeff at h
  rw [← h, ← mul_assoc, ← Real.rpow_add (Torus.jp_pos k.1)]
  simp

theorem funRealCoeff_const_mul (a : ℝ) (φ : Torus d → ℝ) (k : NonzeroLattice d) :
    Torus.funRealCoeff (fun x => a * φ x) k = a * Torus.funRealCoeff φ k := by
  unfold Torus.funRealCoeff
  rw [← integral_const_mul]
  congr 1
  ext x
  ring

theorem funRealCoeff_sub_of {φ ψ : Torus d → ℝ} (hφ : Integrable φ) (hψ : Integrable ψ)
    (k : NonzeroLattice d) :
    Torus.funRealCoeff (fun x => φ x - ψ x) k =
      Torus.funRealCoeff φ k - Torus.funRealCoeff ψ k := by
  unfold Torus.funRealCoeff
  rw [← integral_sub (integrable_realMode_mul hφ k) (integrable_realMode_mul hψ k)]
  congr 1
  ext x
  ring

/-- **The `E_m` norm of the marginal shift from the `L²` expansion of the density.**  The constant
depends only on `m`, the constant `C₀` of the hypothesis (not on `ρ`, `β`). -/
theorem shift_norm_bound_of_L2 (hd : 2 ≤ d) {β : ℝ} (hβ : 0 < β) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) {m : ℝ} (hm : (d : ℝ) < 2 * m) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (hbound : ∀ N : ℕ, 2 ≤ N →
      firstMarginal (modulatedGibbs (periodicRiesz d ((d : ℝ) / 2)) N β (withDensityReal ρ)) ≪
          withDensityReal ρ ∧
        eLpNorm (fun y =>
            ((firstMarginal (modulatedGibbs (periodicRiesz d ((d : ℝ) / 2)) N β
                (withDensityReal ρ))).rnDeriv (withDensityReal ρ) y).toReal - 1 -
              Real.log N / N * (β ^ 2 * sphereArea d / d *
                responseInverse (periodicRiesz d ((d : ℝ) / 2)) (withDensityReal ρ) β ρ y))
          2 (withDensityReal ρ) ≤ ENNReal.ofReal (C₀ * Real.sqrt (Real.log N) / N)) :
    ∀ N : ℕ, 2 ≤ N →
      ‖Real.sqrt N • NegSobolev.ofMeasureDiff m
            (firstMarginal (modulatedGibbs (periodicRiesz d ((d : ℝ) / 2)) N β (withDensityReal ρ)))
            (withDensityReal ρ) -
          (Real.log N / Real.sqrt N) • criticalBias d ((d : ℝ) / 2) β m ρ‖ ≤
        Real.sqrt 2 * Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m))) * C₀ *
          Real.sqrt (Real.log N) / Real.sqrt N := by
  intro N hN
  have hs0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : (d : ℝ) / 2 < d := by linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNs : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hdiv : Real.sqrt N / N = 1 / Real.sqrt N := by
    rw [div_eq_div_iff hN0.ne' hNs.ne', one_mul, Real.mul_self_sqrt hN0.le]
  have hμP : IsProbabilityMeasure (withDensityReal ρ) := PoleCavityAux.isProbabilityMeasure_mu hρ
  have hQ : IsProbabilityMeasure (modulatedGibbs (periodicRiesz d ((d : ℝ) / 2)) N β
      (withDensityReal ρ)) := by
    rw [modulatedGibbs_eq_cavity hd hs0 hsd hβ hρ N (by omega)]
    exact cavity_isProb hd hs0 hsd β hρ N (β / N) (by positivity)
  haveI hPP : IsProbabilityMeasure (firstMarginal (modulatedGibbs (periodicRiesz d ((d : ℝ) / 2))
      N β (withDensityReal ρ))) := HRS.CavResp.isProb_firstMarginal (by omega : 0 < N) _
  obtain ⟨hPac, hFe⟩ := hbound N hN
  obtain ⟨hmh, -, -⟩ := eqbias_response hd hs0 hsd hρ hβ.le
  set P := firstMarginal (modulatedGibbs (periodicRiesz d ((d : ℝ) / 2)) N β
    (withDensityReal ρ)) with hPdef
  set h := responseInverse (periodicRiesz d ((d : ℝ) / 2)) (withDensityReal ρ) β ρ with hhdef
  set c : ℝ := β ^ 2 * sphereArea d / d with hcdef
  set cN : ℝ := Real.log N / N with hcNdef
  have hgm : Measurable (fun y => (P.rnDeriv (withDensityReal ρ) y).toReal) :=
    (Measure.measurable_rnDeriv P (withDensityReal ρ)).ennreal_toReal
  have hhaesm : AEStronglyMeasurable h (withDensityReal ρ) := hmh.aestronglyMeasurable
  have hGaesm : AEStronglyMeasurable
      (fun y => (P.rnDeriv (withDensityReal ρ) y).toReal - 1 - cN * (c * h y))
      (withDensityReal ρ) :=
    (hgm.aestronglyMeasurable.sub aestronglyMeasurable_const).sub
      ((hhaesm.const_mul c).const_mul cN)
  have hFe' : eLpNorm (fun y => (P.rnDeriv (withDensityReal ρ) y).toReal - 1 - cN * (c * h y)) 2
      (withDensityReal ρ) ≤ ENNReal.ofReal (C₀ * Real.sqrt (Real.log N) / N) := hFe
  obtain ⟨hIG, hIGb⟩ := integral_abs_mul_le_aesm hρ.density hGaesm
    (div_nonneg (mul_nonneg hC₀ (Real.sqrt_nonneg _)) hN0.le) hFe'
  have hPint : Integrable (fun y => (P.rnDeriv (withDensityReal ρ) y).toReal)
      (withDensityReal ρ) := Measure.integrable_toReal_rnDeriv
  have hgρ : Integrable (fun y => (P.rnDeriv (withDensityReal ρ) y).toReal * ρ y) :=
    (integrable_withDensityReal_iff hρ.density).1 hPint
  have hρint : Integrable ρ := by
    have h1 : Integrable (fun y => (1 : ℝ) * ρ y) :=
      (integrable_withDensityReal_iff hρ.density).1 (integrable_const (1 : ℝ))
    simpa using h1
  have hcμ : Integrable (fun y => c * h y) (withDensityReal ρ) :=
    (hmh.const_mul c).integrable (by norm_num)
  have hchρ : Integrable (fun y => c * h y * ρ y) :=
    (integrable_withDensityReal_iff hρ.density).1 hcμ
  have hmRCμ : ∀ k : NonzeroLattice d,
      Torus.measureRealCoeff (withDensityReal ρ) k = Torus.funRealCoeff ρ k :=
    fun k => integral_withDensityReal_eq hρ.density (Torus.realMode k)
  have hmRCP : ∀ k : NonzeroLattice d, Torus.measureRealCoeff P k =
      Torus.funRealCoeff (fun y => (P.rnDeriv (withDensityReal ρ) y).toReal * ρ y) k :=
    fun k => measureRealCoeff_eq_funRealCoeff hρ.density hPac k
  have hcoordMD : ∀ k : NonzeroLattice d,
      NegSobolev.coord (NegSobolev.ofMeasureDiff m P (withDensityReal ρ)) k =
        Lattice.jp k.1 ^ (-m) * (Torus.funRealCoeff
          (fun y => (P.rnDeriv (withDensityReal ρ) y).toReal * ρ y) k - Torus.funRealCoeff ρ k) := by
    intro k
    rw [coordDiff hm P (withDensityReal ρ) k, hmRCP k, hmRCμ k]
  have hcbk : ∀ k : NonzeroLattice d,
      NegSobolev.coord (criticalBias d ((d : ℝ) / 2) β m ρ) k =
        Lattice.jp k.1 ^ (-m) * Torus.funRealCoeff (fun y => c * h y * ρ y) k :=
    fun k => coord_ofFun hm hchρ k
  have hfk : ∀ k : NonzeroLattice d,
      Torus.funRealCoeff
          (fun y => ((P.rnDeriv (withDensityReal ρ) y).toReal - 1 - cN * (c * h y)) * ρ y) k =
        Torus.funRealCoeff (fun y => (P.rnDeriv (withDensityReal ρ) y).toReal * ρ y) k -
          Torus.funRealCoeff ρ k - cN * Torus.funRealCoeff (fun y => c * h y * ρ y) k := by
    intro k
    have e1 : (fun y => ((P.rnDeriv (withDensityReal ρ) y).toReal - 1 - cN * (c * h y)) * ρ y) =
        fun y => ((P.rnDeriv (withDensityReal ρ) y).toReal * ρ y - ρ y) - cN * (c * h y * ρ y) := by
      ext y
      ring
    have hI1 : Integrable (fun y => (P.rnDeriv (withDensityReal ρ) y).toReal * ρ y - ρ y) :=
      hgρ.sub hρint
    have hI2 : Integrable (fun y => cN * (c * h y * ρ y)) := hchρ.const_mul cN
    have e2 : Torus.funRealCoeff
        (fun y => ((P.rnDeriv (withDensityReal ρ) y).toReal * ρ y - ρ y) - cN * (c * h y * ρ y)) k =
        Torus.funRealCoeff (fun y => (P.rnDeriv (withDensityReal ρ) y).toReal * ρ y - ρ y) k -
          Torus.funRealCoeff (fun y => cN * (c * h y * ρ y)) k :=
      funRealCoeff_sub_of hI1 hI2 k
    have e3 : Torus.funRealCoeff (fun y => (P.rnDeriv (withDensityReal ρ) y).toReal * ρ y - ρ y) k =
        Torus.funRealCoeff (fun y => (P.rnDeriv (withDensityReal ρ) y).toReal * ρ y) k -
          Torus.funRealCoeff ρ k :=
      funRealCoeff_sub_of hgρ hρint k
    have e4 : Torus.funRealCoeff (fun y => cN * (c * h y * ρ y)) k =
        cN * Torus.funRealCoeff (fun y => c * h y * ρ y) k :=
      funRealCoeff_const_mul _ _ k
    rw [e1, e2, e3, e4]
  have hkey : Real.sqrt N * cN = Real.log N / Real.sqrt N := by
    rw [hcNdef]
    calc Real.sqrt N * (Real.log N / N) = Real.log N * (Real.sqrt N / N) := by ring
      _ = Real.log N * (1 / Real.sqrt N) := by rw [hdiv]
      _ = Real.log N / Real.sqrt N := by ring
  have hK2 : Real.sqrt N * (Real.sqrt 2 * (C₀ * Real.sqrt (Real.log N) / N)) =
      Real.sqrt 2 * C₀ * Real.sqrt (Real.log N) / Real.sqrt N := by
    calc Real.sqrt N * (Real.sqrt 2 * (C₀ * Real.sqrt (Real.log N) / N))
        = Real.sqrt 2 * C₀ * Real.sqrt (Real.log N) * (Real.sqrt N / N) := by ring
      _ = Real.sqrt 2 * C₀ * Real.sqrt (Real.log N) * (1 / Real.sqrt N) := by rw [hdiv]
      _ = Real.sqrt 2 * C₀ * Real.sqrt (Real.log N) / Real.sqrt N := by ring
  have hbnd : ∀ k : NonzeroLattice d,
      |Torus.funRealCoeff (fun y => ((P.rnDeriv (withDensityReal ρ) y).toReal - 1 - cN * (c * h y)) * ρ y) k|
        ≤ Real.sqrt 2 * (C₀ * Real.sqrt (Real.log N) / N) := fun k =>
    (abs_funRealCoeff_le_integral hIG k).trans (mul_le_mul_of_nonneg_left hIGb (Real.sqrt_nonneg 2))
  have hEform : ∀ k : NonzeroLattice d,
      NegSobolev.coord (Real.sqrt N • NegSobolev.ofMeasureDiff m P (withDensityReal ρ) -
          (Real.log N / Real.sqrt N) • criticalBias d ((d : ℝ) / 2) β m ρ) k =
        Real.sqrt N * Lattice.jp k.1 ^ (-m) *
          Torus.funRealCoeff
            (fun y => ((P.rnDeriv (withDensityReal ρ) y).toReal - 1 - cN * (c * h y)) * ρ y) k := by
    intro k
    rw [coord_sub_smul, hcoordMD k, hcbk k, hfk k]
    linear_combination (Lattice.jp k.1 ^ (-m) * Torus.funRealCoeff (fun y => c * h y * ρ y) k) * hkey
  have hcoordBound : ∀ k : NonzeroLattice d,
      |NegSobolev.coord (Real.sqrt N • NegSobolev.ofMeasureDiff m P (withDensityReal ρ) -
          (Real.log N / Real.sqrt N) • criticalBias d ((d : ℝ) / 2) β m ρ) k|
        ≤ (Real.sqrt 2 * C₀ * Real.sqrt (Real.log N) / Real.sqrt N) * Lattice.jp k.1 ^ (-m) := by
    intro k
    have hjp : 0 < Lattice.jp k.1 ^ (-m) := Real.rpow_pos_of_pos (Torus.jp_pos k.1) _
    rw [hEform k, abs_mul, abs_mul, abs_of_nonneg hNs.le, abs_of_pos hjp]
    calc Real.sqrt N * Lattice.jp k.1 ^ (-m) *
          |Torus.funRealCoeff
            (fun y => ((P.rnDeriv (withDensityReal ρ) y).toReal - 1 - cN * (c * h y)) * ρ y) k|
        ≤ Real.sqrt N * Lattice.jp k.1 ^ (-m) * (Real.sqrt 2 * (C₀ * Real.sqrt (Real.log N) / N)) :=
          mul_le_mul_of_nonneg_left (hbnd k) (by positivity)
      _ = (Real.sqrt 2 * C₀ * Real.sqrt (Real.log N) / Real.sqrt N) * Lattice.jp k.1 ^ (-m) := by
          rw [← hK2]
          ring
  have hK : 0 ≤ Real.sqrt 2 * C₀ * Real.sqrt (Real.log N) / Real.sqrt N :=
    div_nonneg (mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) hC₀) (Real.sqrt_nonneg _)) hNs.le
  refine (norm_le_of_coord_bound hm _ hK hcoordBound).trans (le_of_eq ?_)
  ring

end HRS.ME.Bias
