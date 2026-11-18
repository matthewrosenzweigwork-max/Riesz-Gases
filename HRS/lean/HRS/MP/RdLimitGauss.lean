import HRS.MP.RdMartingale
import HRS.Whole.Q09BAux3

/-!
# Packet MPRLGS: S.A.24 on `ℝ^d`, clause (c): the limiting Gaussian stochastic convolution has a
continuous `H^{-q}`-valued version, conditional on the kernel bound (S.A.22)

Namespace `HRS.MP.RdLGS`, helper names `rlg_`.

Route.  Let `Y` solve `IsAdjointDualityLimitW` with `η₀ = 0` for a coefficient `Cf` with
`KernelBoundRd Cf T q C₁`, and let `(e_ℓ)` be a smooth Parseval frame of `H^{-q}` (`mrm_e`).

(a) For `s ≤ t`, `Y_t(e_ℓ) - Y_s(e_ℓ)` is a centered Gaussian whose variance is
`D_ℓ = 2Q ∫_0^t ∫ ∑_j (c^t_{ℓ,j} - c^s_{ℓ,j})² ρ^r dx dr` with `c^u_{ℓ,j}(r,x) = 1_{r ≤ u} ∂_j U^{r,u} e_ℓ (x)`
(`rlg_var_formula`; the Gram form of `noiseCovW`).
(b) Pointwise in `(r,x)`, Parseval gives `∑_ℓ ∑_j (c^t - c^s)² = ∑_j ‖F_j(r,x)‖²_{H^{-q}}` with
`F_j = K_j^{r,t}(x) - 1_{r ≤ s} K_j^{r,s}(x)`, bounded by `d C₁² (|t-s|²(1+|x|)² + 1_{s < r})`
(`KernelBoundRd`); hence `∑_ℓ D_ℓ ≤ V |t-s|` (`rlg_sum_var`), using `∫ (1+|x|)² ρ^r dx ≤ M₂`.
(c) `E‖Y_t - Y_s‖⁴_{H^{-q}} ≤ M V² |t-s|²` (Gaussian fourth moments, Cauchy-Schwarz/Minkowski in `L²(P)`
over the frame), then Kolmogorov-Chentsov with `p = 4`, `β = 1`.

`Y_0 = 0` is not needed: Kolmogorov-Chentsov only uses the increment moments on `[0,T]`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MP.RdLGS

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.HNegInfra HRS.MP.RdMart

variable {d : ℕ}

/-! ### Part I: Gaussian fourth moments and Cauchy-Schwarz -/

theorem rlg_gauss_fourth : ∃ M : ℝ, 0 ≤ M ∧ ∀ v : ℝ, 0 ≤ v →
    ∫⁻ y, ‖y‖ₑ ^ 4 ∂(gaussianReal 0 v.toNNReal) ≤ ENNReal.ofReal (M * v ^ 2) := by
  have hmem : MemLp id 4 (gaussianReal 0 1) := memLp_id_gaussianReal' 4 (by simp)
  have hfin : ∫⁻ z, ‖z‖ₑ ^ ((4 : ℝ≥0∞).toReal) ∂(gaussianReal 0 1) < ∞ :=
    lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (by simp) (by simp) hmem.eLpNorm_lt_top
  have h4 : ((4 : ℝ≥0∞).toReal) = 4 := by norm_num
  rw [h4] at hfin
  set m0 : ℝ≥0∞ := ∫⁻ z, ‖z‖ₑ ^ ((4 : ℝ)) ∂(gaussianReal 0 1) with hm0
  refine ⟨m0.toReal, ENNReal.toReal_nonneg, fun v hv => ?_⟩
  have hmap : gaussianReal 0 v.toNNReal = (gaussianReal 0 1).map (fun z => Real.sqrt v * z) := by
    rw [gaussianReal_map_const_mul]
    simp only [mul_zero]
    congr 1
    ext
    simp [Real.sq_sqrt hv, hv]
  rw [hmap, lintegral_map (by fun_prop) (by fun_prop)]
  have : ∀ z : ℝ, ‖Real.sqrt v * z‖ₑ ^ 4 = ENNReal.ofReal (v ^ 2) * ‖z‖ₑ ^ 4 := by
    intro z
    rw [enorm_mul, mul_pow]
    congr 1
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    congr 1
    rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt hv]
  simp_rw [this]
  rw [lintegral_const_mul _ (by fun_prop)]
  have h4' : ∀ z : ℝ, ‖z‖ₑ ^ (4 : ℕ) = ‖z‖ₑ ^ (4 : ℝ) := fun z => by
    rw [← ENNReal.rpow_natCast]; norm_num
  simp_rw [h4']
  rw [← hm0, ← ENNReal.ofReal_toReal hfin.ne, ← ENNReal.ofReal_mul (by positivity)]
  exact le_of_eq (by congr 1; rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg] ; ring)

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

theorem rlg_fourth_diff {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (G : Ω → ℝ²)
    (hG : Measurable G) (S : Matrix (Fin 2) (Fin 2) ℝ) (hS : S.PosSemidef)
    (hlaw : P.map G = multivariateGaussian 0 S) (M : ℝ)
    (hM : ∀ v : ℝ, 0 ≤ v → ∫⁻ y, ‖y‖ₑ ^ 4 ∂(gaussianReal 0 v.toNNReal) ≤ ENNReal.ofReal (M * v ^ 2)) :
    0 ≤ S 0 0 - S 0 1 - S 1 0 + S 1 1 ∧
    ∫⁻ ω, ‖G ω 0 - G ω 1‖ₑ ^ 4 ∂P ≤
      ENNReal.ofReal (M * (S 0 0 - S 0 1 - S 1 0 + S 1 1) ^ 2) := by
  set w : ℝ² := WithLp.toLp 2 ![1, -1] with hw
  set L : StrongDual ℝ ℝ² := innerSL ℝ w with hL
  have hLx : ∀ x : ℝ², L x = x 0 - x 1 := by
    intro x
    simp [hL, hw, PiLp.inner_apply, Fin.sum_univ_two]
    ring
  have hvar : Var[L; multivariateGaussian (0 : ℝ²) S] = S 0 0 - S 0 1 - S 1 0 + S 1 1 := by
    have h1 := covarianceBilin_self (μ := multivariateGaussian (0 : ℝ²) S) IsGaussian.memLp_two_id w
    rw [covarianceBilin_multivariateGaussian hS] at h1
    have h2 : (fun u : ℝ² => (inner ℝ w u : ℝ)) = L := by
      funext u; rfl
    rw [h2] at h1
    rw [← h1]
    simp [dotProduct, Fin.sum_univ_two, Matrix.mulVec, hw]
    ring
  have hmean : (multivariateGaussian (0 : ℝ²) S)[L] = 0 := by
    rw [ContinuousLinearMap.integral_comp_id_comm IsGaussian.integrable_id L]
    simp
  have hmap : (multivariateGaussian (0 : ℝ²) S).map L = gaussianReal 0
      (S 0 0 - S 0 1 - S 1 0 + S 1 1).toNNReal := by
    rw [IsGaussian.map_eq_gaussianReal L, hmean, hvar]
  have hv0 : 0 ≤ S 0 0 - S 0 1 - S 1 0 + S 1 1 := by
    rw [← hvar]; exact variance_nonneg _ _
  refine ⟨hv0, ?_⟩
  calc ∫⁻ ω, ‖G ω 0 - G ω 1‖ₑ ^ 4 ∂P = ∫⁻ ω, ‖L (G ω)‖ₑ ^ 4 ∂P := by
        simp only [hLx]
    _ = ∫⁻ y, ‖L y‖ₑ ^ 4 ∂(P.map G) := by
        rw [lintegral_map (by fun_prop) hG]
    _ = ∫⁻ y, ‖y‖ₑ ^ 4 ∂((multivariateGaussian (0 : ℝ²) S).map L) := by
        rw [hlaw, lintegral_map (by fun_prop) (by fun_prop)]
    _ ≤ _ := by rw [hmap]; exact hM _ hv0

/-- the degenerate case: if `S` is not positive semidefinite, `multivariateGaussian 0 S = δ₀`. -/
theorem rlg_fourth_diff_nonpsd {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (G : Ω → ℝ²)
    (hG : Measurable G) (S : Matrix (Fin 2) (Fin 2) ℝ) (hS : ¬ S.PosSemidef)
    (hlaw : P.map G = multivariateGaussian 0 S) :
    ∫⁻ ω, ‖G ω 0 - G ω 1‖ₑ ^ 4 ∂P = 0 := by
  rw [multivariateGaussian_of_not_posSemidef _ hS] at hlaw
  have hm : Measurable fun y : ℝ² => ‖y 0 - y 1‖ₑ ^ 4 := by fun_prop
  rw [← lintegral_map hm hG, hlaw, lintegral_dirac' _ hm]
  simp

theorem rlg_cs_pair {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f g : Ω → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) {a b : ℝ≥0∞}
    (ha : ∫⁻ ζ, f ζ ^ 2 ∂P ≤ a ^ 2) (hb : ∫⁻ ζ, g ζ ^ 2 ∂P ≤ b ^ 2) :
    ∫⁻ ζ, f ζ * g ζ ∂P ≤ a * b := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P Real.HolderConjugate.two_two hf.aemeasurable
    hg.aemeasurable
  have e1 : ∀ x : ℝ≥0∞, x ^ (2 : ℝ) = x ^ 2 := fun x => ENNReal.rpow_two x
  have e2 : ∀ x : ℝ≥0∞, (x ^ 2) ^ ((1 : ℝ) / 2) = x := by
    intro x
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  simp only [Pi.mul_apply, e1] at h
  refine h.trans (mul_le_mul' ?_ ?_)
  · calc (∫⁻ ζ, f ζ ^ 2 ∂P) ^ ((1 : ℝ) / 2) ≤ (a ^ 2) ^ ((1 : ℝ) / 2) :=
          ENNReal.rpow_le_rpow ha (by norm_num)
      _ = a := e2 a
  · calc (∫⁻ ζ, g ζ ^ 2 ∂P) ^ ((1 : ℝ) / 2) ≤ (b ^ 2) ^ ((1 : ℝ) / 2) :=
          ENNReal.rpow_le_rpow hb (by norm_num)
      _ = b := e2 b

theorem rlg_sq_tsum {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {ι : Type*} [Countable ι]
    (f : ι → Ω → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) (m : ι → ℝ≥0∞)
    (hm : ∀ i, ∫⁻ ζ, f i ζ ^ 2 ∂P ≤ m i ^ 2) :
    ∫⁻ ζ, (∑' i, f i ζ) ^ 2 ∂P ≤ (∑' i, m i) ^ 2 := by
  have e1 : ∀ ζ, (∑' i, f i ζ) ^ 2 = ∑' i, ∑' j, f i ζ * f j ζ := fun ζ => by
    rw [sq, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun i => ?_
    rw [← ENNReal.tsum_mul_left]
  have e2 : (∑' i, m i) ^ 2 = ∑' i, ∑' j, m i * m j := by
    rw [sq, ← ENNReal.tsum_mul_right]
    refine tsum_congr fun i => ?_
    rw [← ENNReal.tsum_mul_left]
  simp_rw [e1]
  rw [lintegral_tsum (f := fun i ζ => ∑' j, f i ζ * f j ζ)
    (fun i => (Measurable.ennreal_tsum fun j => (hf i).mul (hf j)).aemeasurable), e2]
  refine ENNReal.tsum_le_tsum fun i => ?_
  rw [lintegral_tsum (f := fun j ζ => f i ζ * f j ζ) (fun j => ((hf i).mul (hf j)).aemeasurable)]
  exact ENNReal.tsum_le_tsum fun j => rlg_cs_pair (hf i) (hf j) (hm i) (hm j)

/-! ### Part II: the Gram form of the noise covariance -/

section Var

variable {Cf : WholeCoeff d} {T : ℝ} {q : ℕ} {C₁ : ℝ}
  {Kern : Fin d → ℝ → ℝ → Euc d → HNeg d (q : ℝ)}

/-- the space-time measure `1_{[0,t]}(r) dr dx`. -/
abbrev rlgμ (d : ℕ) (t : ℝ) : Measure (ℝ × Euc d) :=
  (volume.restrict (Set.Icc (0 : ℝ) t)).prod volume

/-- the cut-off gradient component `1_{[0,u]}(r) ∂_j U^{r,u}φ (x)`. -/
def rlgc (Cf : WholeCoeff d) (φ : Euc d → ℝ) (u : ℝ) (j : Fin d) (p : ℝ × Euc d) : ℝ :=
  if p.1 ∈ Set.Icc (0 : ℝ) u then gradient (propagatorW Cf p.1 u φ) p.2 j else 0

theorem rlgc_meas (Cf : WholeCoeff d) (φ : Euc d → ℝ) (u : ℝ) (j : Fin d) :
    Measurable (rlgc Cf φ u j) := mrm_meas_grad Cf u φ j

theorem rlg_sobolevNorm_nonneg (Γ : ℝ) (φ : Euc d → ℝ) : 0 ≤ HRS.Whole.sobolevNorm Γ φ :=
  Real.sqrt_nonneg _

theorem rlgc_bound (hK : MrmKern Cf T q C₁ Kern) {φ : Euc d → ℝ} (hφ : IsSobolevTest (q : ℝ) φ)
    {u : ℝ} (hu : u ≤ T) (j : Fin d) (p : ℝ × Euc d) :
    |rlgc Cf φ u j p| ≤ C₁ * HRS.Whole.sobolevNorm (q : ℝ) φ := by
  unfold rlgc
  split_ifs with h
  · rw [← hK.pair j p.1 u h.1 h.2 hu p.2 φ hφ]
    refine (hneg_pairing_le hφ _).trans ?_
    exact mul_le_mul_of_nonneg_right (hK.bdd j p.1 u h.1 h.2 hu p.2) (rlg_sobolevNorm_nonneg _ _)
  · simpa using mul_nonneg hK.nonneg (rlg_sobolevNorm_nonneg (q : ℝ) φ)

theorem rlg_inner_eq (a b : Euc d) : inner ℝ a b = ∑ j, a j * b j := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

theorem rlg_int_comb {α : Type*} [MeasurableSpace α] {μ : Measure α} {F1 F2 F3 F4 : α → ℝ}
    (h1 : Integrable F1 μ) (h2 : Integrable F2 μ) (h3 : Integrable F3 μ) (h4 : Integrable F4 μ) :
    ∫ x, (F1 x - F2 x - F3 x + F4 x) ∂μ =
      ∫ x, F1 x ∂μ - ∫ x, F2 x ∂μ - ∫ x, F3 x ∂μ + ∫ x, F4 x ∂μ := by
  have j1 : Integrable (fun x => F1 x - F2 x) μ := h1.sub h2
  have j2 : Integrable (fun x => F1 x - F2 x - F3 x) μ := j1.sub h3
  rw [integral_add j2 h4, integral_sub j1 h3, integral_sub h1 h2]

theorem rlg_probInt {ρ : Euc d → ℝ} (h : HRS.Whole.IsProbDensity ρ) : Integrable ρ := by
  by_contra hn
  have := h.integral_one
  rw [integral_undef hn] at this
  exact zero_ne_one this

theorem rlg_int_bdd {ρ : ℝ → Euc d → ℝ} {t T : ℝ} (ht : t ≤ T)
    (hρ : ∀ r ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (ρ r)) (hρm : Measurable (Function.uncurry ρ))
    {G : ℝ × Euc d → ℝ} (hG : Measurable G) {B : ℝ} (hB : ∀ p, |G p| ≤ B) :
    Integrable (fun p : ℝ × Euc d => G p * ρ p.1 p.2) (rlgμ d t) := by
  have hf : Measurable fun p : ℝ × Euc d => G p * ρ p.1 p.2 := hG.mul hρm
  rw [integrable_prod_iff hf.aestronglyMeasurable]
  have hmem : ∀ r ∈ Set.Icc (0 : ℝ) t, r ∈ Set.Icc (0 : ℝ) T := fun r hr => ⟨hr.1, hr.2.trans ht⟩
  refine ⟨?_, ?_⟩
  · refine ae_restrict_of_forall_mem measurableSet_Icc fun r hr => ?_
    have hint := rlg_probInt (hρ r (hmem r hr))
    refine hint.bdd_mul (hG.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (c := B) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]
    exact hB (r, x)
  · have hm : AEStronglyMeasurable (fun r : ℝ => ∫ x : Euc d, ‖G (r, x) * ρ r x‖)
        (volume.restrict (Set.Icc (0 : ℝ) t)) := by
      have := (hf.norm.stronglyMeasurable).integral_prod_right' (ν := (volume : Measure (Euc d)))
      exact this.aestronglyMeasurable
    refine Integrable.of_bound (C := |B|) hm ?_
    refine ae_restrict_of_forall_mem measurableSet_Icc fun r hr => ?_
    have hr' := hρ r (hmem r hr)
    have hint := rlg_probInt hr'
    have h1 : ∫ x : Euc d, ‖G (r, x) * ρ r x‖ ≤ B := by
      calc ∫ x : Euc d, ‖G (r, x) * ρ r x‖ ≤ ∫ x : Euc d, B * ρ r x := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _)
              (hint.const_mul B) (Eventually.of_forall fun x => ?_)
            show ‖G (r, x) * ρ r x‖ ≤ B * ρ r x
            rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hr'.nonneg x)]
            exact mul_le_mul_of_nonneg_right (hB (r, x)) (hr'.nonneg x)
        _ = B := by rw [integral_const_mul, hr'.integral_one, mul_one]
    have h2 : 0 ≤ ∫ x : Euc d, ‖G (r, x) * ρ r x‖ := integral_nonneg fun x => norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg h2]
    exact h1.trans (le_abs_self B)

theorem rlg_prod_int (hK : MrmKern Cf T q C₁ Kern)
    (hρ : ∀ r ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (Cf.ρ r))
    (hρm : Measurable (Function.uncurry Cf.ρ)) {φ : Euc d → ℝ} (hφ : IsSobolevTest (q : ℝ) φ)
    {t u v : ℝ} (hu : u ≤ T) (hv : v ≤ T) (htT : t ≤ T) :
    Integrable (fun p : ℝ × Euc d => (∑ j, rlgc Cf φ u j p * rlgc Cf φ v j p) * Cf.ρ p.1 p.2)
      (rlgμ d t) := by
  refine rlg_int_bdd htT hρ hρm (Finset.measurable_sum _ fun j _ =>
    (rlgc_meas Cf φ u j).mul (rlgc_meas Cf φ v j))
    (B := d * (C₁ * HRS.Whole.sobolevNorm (q : ℝ) φ) ^ 2) fun p => ?_
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ j, |rlgc Cf φ u j p * rlgc Cf φ v j p|
      ≤ ∑ _j : Fin d, (C₁ * HRS.Whole.sobolevNorm (q : ℝ) φ) ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul, sq]
        exact mul_le_mul (rlgc_bound hK hφ hu j p) (rlgc_bound hK hφ hv j p) (abs_nonneg _)
          ((abs_nonneg _).trans (rlgc_bound hK hφ hu j p))
    _ = d * (C₁ * HRS.Whole.sobolevNorm (q : ℝ) φ) ^ 2 := by simp

theorem rlg_cov_eq (hK : MrmKern Cf T q C₁ Kern)
    (hρ : ∀ r ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (Cf.ρ r))
    (hρm : Measurable (Function.uncurry Cf.ρ)) {φ : Euc d → ℝ} (hφ : IsSobolevTest (q : ℝ) φ)
    {t u v : ℝ} (hu : u ≤ t) (hv : v ≤ t) (htT : t ≤ T) (Qn : ℝ) :
    noiseCovW Cf Qn u v φ φ =
      2 * Qn * ∫ p, (∑ j, rlgc Cf φ u j p * rlgc Cf φ v j p) * Cf.ρ p.1 p.2 ∂(rlgμ d t) := by
  have hI := rlg_prod_int hK hρ hρm hφ (t := t) (hu.trans htT) (hv.trans htT) htT
  unfold noiseCovW
  congr 1
  rw [integral_prod _ hI]
  have hpt : ∀ r : ℝ, ∫ x : Euc d, (∑ j, rlgc Cf φ u j (r, x) * rlgc Cf φ v j (r, x)) * Cf.ρ r x =
      (Set.Icc (0 : ℝ) (min u v)).indicator (fun r => ∫ x : Euc d,
        inner ℝ (gradient (propagatorW Cf r u φ) x) (gradient (propagatorW Cf r v φ) x) *
          Cf.ρ r x) r := by
    intro r
    by_cases hr : r ∈ Set.Icc (0 : ℝ) (min u v)
    · have hru : r ∈ Set.Icc (0 : ℝ) u := ⟨hr.1, hr.2.trans (min_le_left _ _)⟩
      have hrv : r ∈ Set.Icc (0 : ℝ) v := ⟨hr.1, hr.2.trans (min_le_right _ _)⟩
      rw [Set.indicator_of_mem hr]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [rlgc, if_pos hru, if_pos hrv]
      congr 1
      rw [rlg_inner_eq]
    · rw [Set.indicator_of_notMem hr]
      have h0 : ∀ x : Euc d,
          (∑ j, rlgc Cf φ u j (r, x) * rlgc Cf φ v j (r, x)) * Cf.ρ r x = 0 := by
        intro x
        by_cases h1 : r ∈ Set.Icc (0 : ℝ) u
        · have h2 : r ∉ Set.Icc (0 : ℝ) v := fun h2 => hr ⟨h1.1, le_min h1.2 h2.2⟩
          simp [rlgc, h2]
        · simp [rlgc, h1]
      simp [h0]
  simp_rw [hpt]
  rw [integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc]
  have : Set.Icc (0 : ℝ) (min u v) ∩ Set.Icc (0 : ℝ) t = Set.Icc (0 : ℝ) (min u v) :=
    Set.inter_eq_left.2 (Set.Icc_subset_Icc le_rfl ((min_le_left _ _).trans hu))
  rw [this]

theorem rlg_var_formula (hK : MrmKern Cf T q C₁ Kern)
    (hρ : ∀ r ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (Cf.ρ r))
    (hρm : Measurable (Function.uncurry Cf.ρ)) {φ : Euc d → ℝ} (hφ : IsSobolevTest (q : ℝ) φ)
    {s t : ℝ} (hst : s ≤ t) (htT : t ≤ T) (Qn : ℝ) :
    noiseCovW Cf Qn t t φ φ - noiseCovW Cf Qn t s φ φ - noiseCovW Cf Qn s t φ φ +
        noiseCovW Cf Qn s s φ φ =
      2 * Qn * ∫ p, (∑ j, (rlgc Cf φ t j p - rlgc Cf φ s j p) ^ 2) * Cf.ρ p.1 p.2 ∂(rlgμ d t) := by
  rw [rlg_cov_eq hK hρ hρm hφ le_rfl le_rfl htT, rlg_cov_eq hK hρ hρm hφ le_rfl hst htT,
    rlg_cov_eq hK hρ hρm hφ hst le_rfl htT, rlg_cov_eq hK hρ hρm hφ hst hst htT]
  have i1 := rlg_prod_int hK hρ hρm hφ (t := t) htT htT htT
  have i2 := rlg_prod_int hK hρ hρm hφ (t := t) htT (hst.trans htT) htT
  have i3 := rlg_prod_int hK hρ hρm hφ (t := t) (hst.trans htT) htT htT
  have i4 := rlg_prod_int hK hρ hρm hφ (t := t) (hst.trans htT) (hst.trans htT) htT
  rw [show ∀ a b c e : ℝ, 2 * Qn * a - 2 * Qn * b - 2 * Qn * c + 2 * Qn * e =
    2 * Qn * (a - b - c + e) from fun a b c e => by ring]
  congr 1
  rw [← rlg_int_comb i1 i2 i3 i4]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp only
  have e : ∑ j, (rlgc Cf φ t j p - rlgc Cf φ s j p) ^ 2 =
      ∑ j, rlgc Cf φ t j p * rlgc Cf φ t j p - ∑ j, rlgc Cf φ t j p * rlgc Cf φ s j p -
        ∑ j, rlgc Cf φ s j p * rlgc Cf φ t j p + ∑ j, rlgc Cf φ s j p * rlgc Cf φ s j p := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [e]
  ring

end Var

/-! ### Part III: Parseval over the frame and the summed variance -/

section Sum

variable {Cf : WholeCoeff d} {T : ℝ} {q : ℕ} {C₁ : ℝ}
  {Kern : Fin d → ℝ → ℝ → Euc d → HNeg d (q : ℝ)}

/-- The `H^{-q}`-valued integrand of the increment: `K_j^{r,t}(x) - 1_{r ≤ s} K_j^{r,s}(x)`. -/
def rlgF (Kern : Fin d → ℝ → ℝ → Euc d → HNeg d (q : ℝ)) (s t : ℝ) (j : Fin d)
    (p : ℝ × Euc d) : HNeg d (q : ℝ) :=
  Kern j p.1 t p.2 - (if p.1 ≤ s then Kern j p.1 s p.2 else 0)

/-- The variance of the increment `Y_t(φ) - Y_s(φ)`. -/
def rlgD (Cf : WholeCoeff d) (Qn : ℝ) (φ : Euc d → ℝ) (s t : ℝ) : ℝ :=
  noiseCovW Cf Qn t t φ φ - noiseCovW Cf Qn t s φ φ - noiseCovW Cf Qn s t φ φ +
    noiseCovW Cf Qn s s φ φ

theorem rlg_parseval_pt (hK : MrmKern Cf T q C₁ Kern) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (htT : t ≤ T) {p : ℝ × Euc d} (hp : p.1 ∈ Set.Icc (0 : ℝ) t) :
    HasSum (fun ℓ => ∑ j, (rlgc Cf (mrm_e d (q : ℝ) ℓ) t j p -
        rlgc Cf (mrm_e d (q : ℝ) ℓ) s j p) ^ 2) (∑ j, ‖rlgF Kern s t j p‖ ^ 2) := by
  refine hasSum_sum fun j _ => ?_
  have key : ∀ ℓ, rlgc Cf (mrm_e d (q : ℝ) ℓ) t j p - rlgc Cf (mrm_e d (q : ℝ) ℓ) s j p =
      HNeg.pairing (mrm_e d (q : ℝ) ℓ) (rlgF Kern s t j p) := by
    intro ℓ
    have hℓ := mrm_e_test (d := d) (q : ℝ) ℓ
    have ht := hK.pair j p.1 t hp.1 hp.2 htT p.2 _ hℓ
    unfold rlgF
    by_cases h : p.1 ≤ s
    · have hs' : p.1 ∈ Set.Icc (0 : ℝ) s := ⟨hp.1, h⟩
      have hs2 := hK.pair j p.1 s hp.1 h (hst.trans htT) p.2 _ hℓ
      simp only [rlgc, if_pos hp, if_pos hs', if_pos h]
      rw [mhn_pairing_sub hℓ, ht, hs2]
    · have hs' : p.1 ∉ Set.Icc (0 : ℝ) s := fun h' => h h'.2
      simp only [rlgc, if_pos hp, if_neg hs', if_neg h, sub_zero]
      rw [ht]
  have hfun : (fun ℓ => (rlgc Cf (mrm_e d (q : ℝ) ℓ) t j p -
        rlgc Cf (mrm_e d (q : ℝ) ℓ) s j p) ^ 2) =
      fun ℓ => (HNeg.pairing (mrm_e d (q : ℝ) ℓ) (rlgF Kern s t j p)) ^ 2 := by
    funext ℓ; rw [key]
  rw [hfun]
  exact mrm_e_parseval (q : ℝ) _

theorem rlg_F_sum_bound (hK : MrmKern Cf T q C₁ Kern) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (htT : t ≤ T) {p : ℝ × Euc d} (hp : p.1 ∈ Set.Icc (0 : ℝ) t) :
    ∑ j, ‖rlgF Kern s t j p‖ ^ 2 ≤
      d * C₁ ^ 2 * (t - s) ^ 2 * (1 + ‖p.2‖) ^ 2 +
        (Set.Ioc s t).indicator (fun _ => (d : ℝ) * C₁ ^ 2) p.1 := by
  by_cases h : p.1 ≤ s
  · have hn : p.1 ∉ Set.Ioc s t := fun h' => absurd h'.1 (not_lt.2 h)
    rw [Set.indicator_of_notMem hn, add_zero]
    calc ∑ j, ‖rlgF Kern s t j p‖ ^ 2
        ≤ ∑ _j : Fin d, C₁ ^ 2 * (t - s) ^ 2 * (1 + ‖p.2‖) ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          have h1 := hK.incr j p.1 s t hp.1 h hst htT p.2
          have h2 : ‖rlgF Kern s t j p‖ = ‖Kern j p.1 t p.2 - Kern j p.1 s p.2‖ := by
            simp only [rlgF, if_pos h]
          rw [h2]
          calc ‖Kern j p.1 t p.2 - Kern j p.1 s p.2‖ ^ 2
              ≤ (C₁ * |t - s| * (1 + ‖p.2‖)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
            _ = C₁ ^ 2 * (t - s) ^ 2 * (1 + ‖p.2‖) ^ 2 := by
              rw [mul_pow, mul_pow, sq_abs]
      _ = d * C₁ ^ 2 * (t - s) ^ 2 * (1 + ‖p.2‖) ^ 2 := by simp; ring
  · have hm : p.1 ∈ Set.Ioc s t := ⟨not_le.1 h, hp.2⟩
    rw [Set.indicator_of_mem hm]
    have hpos : 0 ≤ (d : ℝ) * C₁ ^ 2 * (t - s) ^ 2 * (1 + ‖p.2‖) ^ 2 := by positivity
    have : ∑ j, ‖rlgF Kern s t j p‖ ^ 2 ≤ (d : ℝ) * C₁ ^ 2 := by
      calc ∑ j, ‖rlgF Kern s t j p‖ ^ 2 ≤ ∑ _j : Fin d, C₁ ^ 2 := by
            refine Finset.sum_le_sum fun j _ => ?_
            have h1 := hK.bdd j p.1 t hp.1 hp.2 htT p.2
            have h2 : ‖rlgF Kern s t j p‖ = ‖Kern j p.1 t p.2‖ := by
              simp only [rlgF, if_neg h, sub_zero]
            rw [h2]
            exact pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ = d * C₁ ^ 2 := by simp
    linarith

theorem rlg_sq_int (hK : MrmKern Cf T q C₁ Kern)
    (hρ : ∀ r ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (Cf.ρ r))
    (hρm : Measurable (Function.uncurry Cf.ρ)) {φ : Euc d → ℝ} (hφ : IsSobolevTest (q : ℝ) φ)
    {s t : ℝ} (hsT : s ≤ T) (htT : t ≤ T) :
    Integrable (fun p : ℝ × Euc d =>
      (∑ j, (rlgc Cf φ t j p - rlgc Cf φ s j p) ^ 2) * Cf.ρ p.1 p.2) (rlgμ d t) := by
  refine rlg_int_bdd htT hρ hρm (Finset.measurable_sum _ fun j _ =>
    ((rlgc_meas Cf φ t j).sub (rlgc_meas Cf φ s j)).pow_const 2)
    (B := d * (2 * C₁ * HRS.Whole.sobolevNorm (q : ℝ) φ) ^ 2) fun p => ?_
  rw [abs_of_nonneg (Finset.sum_nonneg fun j _ => sq_nonneg _)]
  calc ∑ j, (rlgc Cf φ t j p - rlgc Cf φ s j p) ^ 2
      ≤ ∑ _j : Fin d, (2 * C₁ * HRS.Whole.sobolevNorm (q : ℝ) φ) ^ 2 := by
        refine Finset.sum_le_sum fun j _ => ?_
        have h1 := rlgc_bound hK hφ htT j p
        have h2 := rlgc_bound hK hφ hsT j p
        have h3 : |rlgc Cf φ t j p - rlgc Cf φ s j p| ≤ 2 * C₁ * HRS.Whole.sobolevNorm (q : ℝ) φ := by
          calc |rlgc Cf φ t j p - rlgc Cf φ s j p| ≤ |rlgc Cf φ t j p| + |rlgc Cf φ s j p| :=
                abs_sub _ _
            _ ≤ _ := by linarith
        calc (rlgc Cf φ t j p - rlgc Cf φ s j p) ^ 2
            = |rlgc Cf φ t j p - rlgc Cf φ s j p| ^ 2 := (sq_abs _).symm
          _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) h3 2
    _ = d * (2 * C₁ * HRS.Whole.sobolevNorm (q : ℝ) φ) ^ 2 := by simp

theorem rlg_sum_var (hK : MrmKern Cf T q C₁ Kern)
    (hρ : ∀ r ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (Cf.ρ r))
    (hρm : Measurable (Function.uncurry Cf.ρ)) {M₂ : ℝ} (hM₂ : 0 ≤ M₂)
    (hmom : ∀ r ∈ Set.Icc (0 : ℝ) T, Integrable (fun x : Euc d => (1 + ‖x‖) ^ 2 * Cf.ρ r x) ∧
      ∫ x : Euc d, (1 + ‖x‖) ^ 2 * Cf.ρ r x ≤ M₂)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) {Qn : ℝ} (hQ : 0 ≤ Qn) :
    ∑' ℓ, ENNReal.ofReal (rlgD Cf Qn (mrm_e d (q : ℝ) ℓ) s t) ≤
      ENNReal.ofReal (2 * Qn * d * C₁ ^ 2 * (T ^ 2 * M₂ + 1) * (t - s)) := by
  set μ := rlgμ d t with hμ
  set e := mrm_e d (q : ℝ) with he
  have ht0 : 0 ≤ t := hs.trans hst
  have hδ : 0 ≤ t - s := sub_nonneg.2 hst
  have hae : ∀ᵐ p ∂μ, p.1 ∈ Set.Icc (0 : ℝ) t := by
    have h : ∀ᵐ r ∂(volume.restrict (Set.Icc (0 : ℝ) t)), r ∈ Set.Icc (0 : ℝ) t :=
      ae_restrict_mem measurableSet_Icc
    exact (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Set.Icc (0 : ℝ) t))
      (ν := (volume : Measure (Euc d)))).ae h
  have hρn : ∀ᵐ p ∂μ, 0 ≤ Cf.ρ p.1 p.2 :=
    hae.mono fun p hp => (hρ _ ⟨hp.1, hp.2.trans htT⟩).nonneg _
  set g : ℕ → ℝ × Euc d → ℝ := fun ℓ p =>
    ∑ j, (rlgc Cf (e ℓ) t j p - rlgc Cf (e ℓ) s j p) ^ 2 with hg
  have hgm : ∀ ℓ, Measurable (g ℓ) := fun ℓ =>
    Finset.measurable_sum _ fun j _ => ((rlgc_meas Cf (e ℓ) t j).sub (rlgc_meas Cf (e ℓ) s j)).pow_const 2
  have hgn : ∀ ℓ p, 0 ≤ g ℓ p := fun ℓ p => Finset.sum_nonneg fun j _ => sq_nonneg _
  have hgint : ∀ ℓ, Integrable (fun p : ℝ × Euc d => g ℓ p * Cf.ρ p.1 p.2) μ := fun ℓ =>
    rlg_sq_int hK hρ hρm (mrm_e_test (d := d) (q : ℝ) ℓ) (hst.trans htT) htT
  have hρm' : Measurable fun p : ℝ × Euc d => Cf.ρ p.1 p.2 := hρm
  have hgρm : ∀ ℓ, Measurable fun p : ℝ × Euc d => ENNReal.ofReal (g ℓ p * Cf.ρ p.1 p.2) :=
    fun ℓ => ENNReal.measurable_ofReal.comp ((hgm ℓ).mul hρm')
  have hD : ∀ ℓ, ENNReal.ofReal (rlgD Cf Qn (e ℓ) s t) =
      ENNReal.ofReal (2 * Qn) * ∫⁻ p, ENNReal.ofReal (g ℓ p * Cf.ρ p.1 p.2) ∂μ := by
    intro ℓ
    unfold rlgD
    rw [rlg_var_formula hK hρ hρm (mrm_e_test (d := d) (q : ℝ) ℓ) hst htT Qn,
      ENNReal.ofReal_mul (by positivity),
      ofReal_integral_eq_lintegral_ofReal (hgint ℓ)
        (hρn.mono fun p hp => mul_nonneg (hgn ℓ p) hp)]
  -- the two majorants
  set c1 : ℝ := d * C₁ ^ 2 * (t - s) ^ 2 with hc1
  set c2 : ℝ := d * C₁ ^ 2 with hc2
  have hc1n : 0 ≤ c1 := by positivity
  have hc2n : 0 ≤ c2 := by positivity
  set W1 : ℝ × Euc d → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (c1 * ((1 + ‖p.2‖) ^ 2 * Cf.ρ p.1 p.2)) with hW1
  set W2 : ℝ × Euc d → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (((Set.Ioc s t).indicator (fun _ => c2) p.1) * Cf.ρ p.1 p.2) with hW2
  have hW1m : Measurable W1 :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul
      ((by fun_prop : Measurable fun p : ℝ × Euc d => (1 + ‖p.2‖) ^ 2).mul hρm'))
  have hW2m : Measurable W2 :=
    ENNReal.measurable_ofReal.comp
      (((measurable_const.indicator measurableSet_Ioc).comp measurable_fst).mul hρm')
  have hpt : ∀ᵐ p ∂μ, ∑' ℓ, ENNReal.ofReal (g ℓ p * Cf.ρ p.1 p.2) ≤ W1 p + W2 p := by
    filter_upwards [hae, hρn] with p hp hρp
    have hsum := (rlg_parseval_pt hK hs hst htT hp).mul_right (Cf.ρ p.1 p.2)
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun ℓ => mul_nonneg (hgn ℓ p) hρp) hsum.summable,
      hsum.tsum_eq]
    have hind : 0 ≤ (Set.Ioc s t).indicator (fun _ => c2) p.1 :=
      Set.indicator_nonneg (fun _ _ => hc2n) _
    rw [hW1, hW2]
    simp only
    rw [← ENNReal.ofReal_add (mul_nonneg hc1n (mul_nonneg (sq_nonneg _) hρp))
      (mul_nonneg hind hρp)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hb : ∑ j, ‖rlgF Kern s t j p‖ ^ 2 ≤
        c1 * (1 + ‖p.2‖) ^ 2 + (Set.Ioc s t).indicator (fun _ => c2) p.1 :=
      rlg_F_sum_bound hK hs hst htT hp
    calc (∑ j, ‖rlgF Kern s t j p‖ ^ 2) * Cf.ρ p.1 p.2
        ≤ (c1 * (1 + ‖p.2‖) ^ 2 + (Set.Ioc s t).indicator (fun _ => c2) p.1) * Cf.ρ p.1 p.2 :=
          mul_le_mul_of_nonneg_right hb hρp
      _ = _ := by ring
  have hI1 : ∫⁻ p, W1 p ∂μ ≤ ENNReal.ofReal (c1 * M₂) * ENNReal.ofReal t := by
    rw [hμ, rlgμ, lintegral_prod _ hW1m.aemeasurable]
    calc ∫⁻ r, ∫⁻ x, W1 (r, x) ∂volume ∂(volume.restrict (Set.Icc (0 : ℝ) t))
        ≤ ∫⁻ _r, ENNReal.ofReal (c1 * M₂) ∂(volume.restrict (Set.Icc (0 : ℝ) t)) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
          have hr' := hρ r ⟨hr.1, hr.2.trans htT⟩
          obtain ⟨hint, hle⟩ := hmom r ⟨hr.1, hr.2.trans htT⟩
          calc ∫⁻ x, W1 (r, x) ∂volume
              = ENNReal.ofReal (∫ x : Euc d, c1 * ((1 + ‖x‖) ^ 2 * Cf.ρ r x)) := by
                rw [ofReal_integral_eq_lintegral_ofReal (hint.const_mul c1)
                  (Eventually.of_forall fun x => mul_nonneg hc1n
                    (mul_nonneg (sq_nonneg _) (hr'.nonneg x)))]
            _ ≤ ENNReal.ofReal (c1 * M₂) := by
                rw [integral_const_mul]
                exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hle hc1n)
      _ = ENNReal.ofReal (c1 * M₂) * ENNReal.ofReal t := by
          rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero]
  have hI2 : ∫⁻ p, W2 p ∂μ ≤ ENNReal.ofReal c2 * ENNReal.ofReal (t - s) := by
    rw [hμ, rlgμ, lintegral_prod _ hW2m.aemeasurable]
    refine le_of_eq ?_
    calc ∫⁻ r, ∫⁻ x, W2 (r, x) ∂volume ∂(volume.restrict (Set.Icc (0 : ℝ) t))
        = ∫⁻ r, (Set.Ioc s t).indicator (fun _ => ENNReal.ofReal c2) r
            ∂(volume.restrict (Set.Icc (0 : ℝ) t)) := by
          refine lintegral_congr_ae ?_
          filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
          have hr' := hρ r ⟨hr.1, hr.2.trans htT⟩
          by_cases h : r ∈ Set.Ioc s t
          · simp only [hW2, Set.indicator_of_mem h]
            rw [← ofReal_integral_eq_lintegral_ofReal ((rlg_probInt hr').const_mul c2)
              (Eventually.of_forall fun x => mul_nonneg hc2n (hr'.nonneg x)),
              integral_const_mul, hr'.integral_one, mul_one]
          · simp [hW2, Set.indicator_of_notMem h]
      _ = ENNReal.ofReal c2 * (volume.restrict (Set.Icc (0 : ℝ) t)) (Set.Ioc s t) :=
          lintegral_indicator_const measurableSet_Ioc _
      _ = ENNReal.ofReal c2 * ENNReal.ofReal (t - s) := by
          rw [Measure.restrict_apply measurableSet_Ioc,
            Set.inter_eq_left.2 (show Set.Ioc s t ⊆ Set.Icc 0 t from fun x hx => ⟨hs.trans hx.1.le, hx.2⟩),
            Real.volume_Ioc]
  calc ∑' ℓ, ENNReal.ofReal (rlgD Cf Qn (e ℓ) s t)
      = ENNReal.ofReal (2 * Qn) * ∑' ℓ, ∫⁻ p, ENNReal.ofReal (g ℓ p * Cf.ρ p.1 p.2) ∂μ := by
        simp_rw [hD]; rw [ENNReal.tsum_mul_left]
    _ = ENNReal.ofReal (2 * Qn) * ∫⁻ p, ∑' ℓ, ENNReal.ofReal (g ℓ p * Cf.ρ p.1 p.2) ∂μ := by
        rw [lintegral_tsum (fun ℓ => (hgρm ℓ).aemeasurable)]
    _ ≤ ENNReal.ofReal (2 * Qn) * (∫⁻ p, W1 p ∂μ + ∫⁻ p, W2 p ∂μ) := by
        gcongr
        rw [← lintegral_add_left hW1m]
        exact lintegral_mono_ae hpt
    _ ≤ ENNReal.ofReal (2 * Qn) * (ENNReal.ofReal (c1 * M₂) * ENNReal.ofReal t +
          ENNReal.ofReal c2 * ENNReal.ofReal (t - s)) := by gcongr
    _ = ENNReal.ofReal (2 * Qn * (c1 * M₂ * t + c2 * (t - s))) := by
        rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hδT : t - s ≤ T := by linarith
        have h1 : (t - s) * t ≤ T * T := mul_le_mul hδT htT ht0 (ht0.trans htT)
        have h2 : (t - s) ^ 2 * t ≤ (t - s) * T ^ 2 := by
          have : (t - s) ^ 2 * t = (t - s) * ((t - s) * t) := by ring
          rw [this]
          nlinarith [mul_le_mul_of_nonneg_left h1 hδ]
        have hk : 0 ≤ (d : ℝ) * C₁ ^ 2 := by positivity
        have h3 : c1 * M₂ * t ≤ (d * C₁ ^ 2) * ((t - s) * T ^ 2 * M₂) := by
          rw [hc1]
          calc d * C₁ ^ 2 * (t - s) ^ 2 * M₂ * t
              = (d * C₁ ^ 2) * (((t - s) ^ 2 * t) * M₂) := by ring
            _ ≤ (d * C₁ ^ 2) * (((t - s) * T ^ 2) * M₂) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h2 hM₂) hk
            _ = _ := by ring
        have h4 : c1 * M₂ * t + c2 * (t - s) ≤ d * C₁ ^ 2 * (T ^ 2 * M₂ + 1) * (t - s) := by
          calc c1 * M₂ * t + c2 * (t - s)
              ≤ (d * C₁ ^ 2) * ((t - s) * T ^ 2 * M₂) + c2 * (t - s) := by linarith
            _ = d * C₁ ^ 2 * (T ^ 2 * M₂ + 1) * (t - s) := by rw [hc2]; ring
        calc 2 * Qn * (c1 * M₂ * t + c2 * (t - s))
            ≤ 2 * Qn * (d * C₁ ^ 2 * (T ^ 2 * M₂ + 1) * (t - s)) :=
              mul_le_mul_of_nonneg_left h4 (by positivity)
          _ = _ := by ring

end Sum

/-! ### Part IV: the second moment of the limiting density -/

theorem rlg_mom {s : ℝ} {m : ℕ} {Λ T : ℝ} {ρ : ℝ → Euc d → ℝ}
    (hreg : IsRegularMFRd s m Λ T ρ)
    (hprob : ∀ t ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (ρ t)) :
    ∃ M₂ : ℝ, 0 ≤ M₂ ∧ ∀ r ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun x : Euc d => (1 + ‖x‖) ^ 2 * ρ r x) ∧
        ∫ x : Euc d, (1 + ‖x‖) ^ 2 * ρ r x ≤ M₂ := by
  have hint : Integrable (fun x : Euc d => (1 + ‖x‖ ^ 2) ^ (-((d : ℝ) + 1) / 2)) := by
    have := integrable_rpow_neg_one_add_norm_sq (E := Euc d) (μ := volume) (r := (d : ℝ) + 1)
      (by simp)
    exact this
  have hK : 0 ≤ HRS.Whole.Q09B.q09b_K d :=
    integral_nonneg fun x => (Real.rpow_pos_of_pos (by positivity) _).le
  refine ⟨2 * max Λ 0 * HRS.Whole.Q09B.q09b_K d, by positivity, fun t ht => ?_⟩
  obtain ⟨hmem, hfin, hΛ⟩ := hreg.1 t ht
  have hρ := hprob t ht
  have hcb : 0 ≤ cbNorm m (ρ t) :=
    Finset.sum_nonneg fun j _ => Real.iSup_nonneg fun _ => norm_nonneg _
  have hΛ' : (weightedSupE m ((d : ℝ) + 3) (ρ t)).toReal ≤ Λ := by linarith
  have hpt : ∀ x : Euc d, (1 + ‖x‖) ^ 2 * ρ t x ≤
      (2 * Λ) * (1 + ‖x‖ ^ 2) ^ (-((d : ℝ) + 1) / 2) := by
    intro x
    have ha : 0 < 1 + ‖x‖ ^ 2 := by positivity
    have hw := HRS.Whole.Q09B.q09b_jbracket_bound hfin x
    have hjb : jbracket x ^ ((d : ℝ) + 3) = (1 + ‖x‖ ^ 2) ^ (((d : ℝ) + 3) / 2) := by
      unfold jbracket
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ha.le]
      congr 1
      ring
    rw [hjb, abs_of_nonneg (hρ.nonneg x)] at hw
    have h1 : (1 + ‖x‖ ^ 2) ^ (((d : ℝ) + 3) / 2) * ρ t x ≤ Λ := hw.trans hΛ'
    have h2 : (1 + ‖x‖ ^ 2) ^ (((d : ℝ) + 3) / 2) =
        (1 + ‖x‖ ^ 2) ^ (((d : ℝ) + 1) / 2) * (1 + ‖x‖ ^ 2) := by
      rw [← Real.rpow_add_one ha.ne']
      congr 1
      ring
    set a : ℝ := 1 + ‖x‖ ^ 2 with hadef
    have hb : a ^ (-((d : ℝ) + 1) / 2) * a ^ (((d : ℝ) + 1) / 2) = 1 := by
      rw [← Real.rpow_add ha]
      have : -((d : ℝ) + 1) / 2 + ((d : ℝ) + 1) / 2 = 0 := by ring
      rw [this, Real.rpow_zero]
    have hbpos : 0 < a ^ (-((d : ℝ) + 1) / 2) := Real.rpow_pos_of_pos ha _
    have hρ0 := hρ.nonneg x
    have hρa : (1 + ‖x‖) ^ 2 * ρ t x ≤ 2 * (ρ t x * a) := by
      have : (1 + ‖x‖) ^ 2 ≤ 2 * a := by rw [hadef]; nlinarith [sq_nonneg (1 - ‖x‖)]
      nlinarith
    have h3 : ρ t x * a * a ^ (((d : ℝ) + 1) / 2) ≤ Λ := by
      rw [h2] at h1; nlinarith [h1]
    calc (1 + ‖x‖) ^ 2 * ρ t x ≤ 2 * (ρ t x * a) := hρa
      _ = 2 * ((ρ t x * a * a ^ (((d : ℝ) + 1) / 2)) * a ^ (-((d : ℝ) + 1) / 2)) := by
          rw [mul_assoc, mul_assoc, mul_comm (a ^ (((d : ℝ) + 1) / 2)), hb]; ring
      _ ≤ 2 * (Λ * a ^ (-((d : ℝ) + 1) / 2)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h3 hbpos.le) (by norm_num)
      _ = (2 * Λ) * a ^ (-((d : ℝ) + 1) / 2) := by ring
  have hmaj : Integrable (fun x : Euc d => (2 * Λ) * (1 + ‖x‖ ^ 2) ^ (-((d : ℝ) + 1) / 2)) :=
    hint.const_mul _
  have hnn : ∀ x : Euc d, 0 ≤ (1 + ‖x‖) ^ 2 * ρ t x := fun x =>
    mul_nonneg (sq_nonneg _) (hρ.nonneg x)
  have hmeas : Measurable fun x : Euc d => (1 + ‖x‖) ^ 2 * ρ t x :=
    (by fun_prop : Measurable fun x : Euc d => (1 + ‖x‖) ^ 2).mul hρ.measurable
  refine ⟨?_, ?_⟩
  · refine Integrable.mono' hmaj hmeas.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn x)]
    exact hpt x
  · calc ∫ x : Euc d, (1 + ‖x‖) ^ 2 * ρ t x
        ≤ ∫ x : Euc d, (2 * Λ) * (1 + ‖x‖ ^ 2) ^ (-((d : ℝ) + 1) / 2) :=
          integral_mono_of_nonneg (Eventually.of_forall hnn) hmaj (Eventually.of_forall hpt)
      _ = 2 * Λ * HRS.Whole.Q09B.q09b_K d := by
          rw [integral_const_mul]; rfl
      _ ≤ 2 * max Λ 0 * HRS.Whole.Q09B.q09b_K d := by
          refine mul_le_mul_of_nonneg_right ?_ hK
          linarith [le_max_left Λ 0]

/-! ### Part V: fourth moments of increments, Kolmogorov-Chentsov, and the theorem -/

section Fourth

variable {Cf : WholeCoeff d} {T : ℝ} {q : ℕ} {C₁ : ℝ}
  {Kern : Fin d → ℝ → ℝ → Euc d → HNeg d (q : ℝ)}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']

theorem rlg_mode_fourth {A Qn : ℝ} {Y : ℝ → Ω' → HNeg d (q : ℝ)}
    (hY : IsAdjointDualityLimitW P' Cf (q : ℝ) A Qn T (fun _ _ => 0) Y)
    {e : Euc d → ℝ} (he : IsSobolevTest (q : ℝ) e) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ v : ℝ, 0 ≤ v →
      ∫⁻ y, ‖y‖ₑ ^ 4 ∂(gaussianReal 0 v.toNNReal) ≤ ENNReal.ofReal (M * v ^ 2))
    {s t : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫⁻ ζ, ‖HNeg.pairing e (Y t ζ - Y s ζ)‖ₑ ^ 4 ∂P' ≤
      ENNReal.ofReal M * ENNReal.ofReal (rlgD Cf Qn e s t) ^ 2 := by
  have hts : ∀ a : Fin 2, (![t, s] : Fin 2 → ℝ) a ∈ Set.Icc (0 : ℝ) T := by
    intro a
    fin_cases a
    · exact ht
    · exact hs
  obtain ⟨-, hlaw⟩ := hY.gaussian_part 2 ![t, s] (fun _ => e) hts (fun _ => he)
  set S : Matrix (Fin 2) (Fin 2) ℝ :=
    Matrix.of fun a b => noiseCovW Cf Qn (![t, s] a) (![t, s] b) e e with hS
  set G : Ω' → EuclideanSpace ℝ (Fin 2) := fun ζ => WithLp.toLp 2 fun a : Fin 2 =>
    HNeg.pairing e (Y (![t, s] a) ζ) with hG
  have hGeq : G = fun ζ => (WithLp.toLp 2 (fun a : Fin 2 =>
      HNeg.pairing ((fun _ : Fin 2 => e) a) (Y (![t, s] a) ζ) - A *
        (fun (_ : Ω') (_ : Euc d → ℝ) => (0 : ℝ)) ζ
          (propagatorW Cf 0 (![t, s] a) ((fun _ : Fin 2 => e) a))) : EuclideanSpace ℝ (Fin 2)) := by
    funext ζ
    simp [hG]
  have hlawG : P'.map G = multivariateGaussian 0 S := by
    rw [hGeq]
    exact hlaw
  have hmeasG : Measurable G := by
    refine (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).measurable.comp ?_
    exact measurable_pi_iff.2 fun a => (mhn_continuous_pairing he).measurable.comp (hY.meas _)
  have hrel : ∀ ζ, HNeg.pairing e (Y t ζ - Y s ζ) = G ζ 0 - G ζ 1 := by
    intro ζ
    rw [mhn_pairing_sub he]
    simp [hG]
  have hDeq : S 0 0 - S 0 1 - S 1 0 + S 1 1 = rlgD Cf Qn e s t := by
    simp [hS, rlgD]
  simp_rw [hrel]
  by_cases hpsd : S.PosSemidef
  · obtain ⟨hD0, h4⟩ := rlg_fourth_diff P' G hmeasG S hpsd hlawG M hM
    rw [hDeq] at h4 hD0
    refine h4.trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul hM0, ENNReal.ofReal_pow hD0]
  · rw [rlg_fourth_diff_nonpsd P' G hmeasG S hpsd hlawG]
    exact zero_le

theorem rlg_fourth_moment {A Qn : ℝ} (hQ : 0 ≤ Qn) {Y : ℝ → Ω' → HNeg d (q : ℝ)}
    (hY : IsAdjointDualityLimitW P' Cf (q : ℝ) A Qn T (fun _ _ => 0) Y)
    (hK : MrmKern Cf T q C₁ Kern) (hρ : ∀ r ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (Cf.ρ r))
    {M₂ : ℝ} (hM₂ : 0 ≤ M₂)
    (hmom : ∀ r ∈ Set.Icc (0 : ℝ) T, Integrable (fun x : Euc d => (1 + ‖x‖) ^ 2 * Cf.ρ r x) ∧
      ∫ x : Euc d, (1 + ‖x‖) ^ 2 * Cf.ρ r x ≤ M₂) :
    ∃ C : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ζ, ‖Y t ζ - Y s ζ‖ₑ ^ 4 ∂P' ≤ ENNReal.ofReal (C * |t - s| ^ 2) := by
  obtain ⟨M, hM0, hM⟩ := rlg_gauss_fourth
  set V : ℝ := 2 * Qn * d * C₁ ^ 2 * (T ^ 2 * M₂ + 1) with hV
  refine ⟨M * V ^ 2, ?_⟩
  have core : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T, s ≤ t →
      ∫⁻ ζ, ‖Y t ζ - Y s ζ‖ₑ ^ 4 ∂P' ≤ ENNReal.ofReal (M * V ^ 2 * |t - s| ^ 2) := by
    intro s hs t ht hst
    set e := mrm_e d (q : ℝ) with he
    have hmeasF : Measurable fun ζ => Y t ζ - Y s ζ := (hY.meas t).sub (hY.meas s)
    set f : ℕ → Ω' → ℝ≥0∞ := fun ℓ ζ =>
      ENNReal.ofReal ((HNeg.pairing (e ℓ) (Y t ζ - Y s ζ)) ^ 2) with hf
    have hfm : ∀ ℓ, Measurable (f ℓ) := fun ℓ =>
      ENNReal.measurable_ofReal.comp
        (((mhn_continuous_pairing (mrm_e_test (d := d) (q : ℝ) ℓ)).measurable.comp hmeasF).pow_const 2)
    have h1 : ∀ ζ, ‖Y t ζ - Y s ζ‖ₑ ^ 4 = (∑' ℓ, f ℓ ζ) ^ 2 := by
      intro ζ
      have hsum := mrm_e_parseval (d := d) (q : ℝ) (Y t ζ - Y s ζ)
      simp only [hf]
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun ℓ => sq_nonneg _) hsum.summable, hsum.tsum_eq,
        ← ENNReal.ofReal_pow (sq_nonneg _), ← ofReal_norm_eq_enorm,
        ← ENNReal.ofReal_pow (norm_nonneg _)]
      congr 1; ring
    have h2 : ∀ ℓ ζ, f ℓ ζ ^ 2 = ‖HNeg.pairing (e ℓ) (Y t ζ - Y s ζ)‖ₑ ^ 4 := by
      intro ℓ ζ
      simp only [hf]
      rw [← ENNReal.ofReal_pow (sq_nonneg _), ← ofReal_norm_eq_enorm,
        ← ENNReal.ofReal_pow (norm_nonneg _)]
      congr 1
      rw [Real.norm_eq_abs, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs]
    have hm : ∀ ℓ, ∫⁻ ζ, f ℓ ζ ^ 2 ∂P' ≤
        (ENNReal.ofReal (Real.sqrt M) * ENNReal.ofReal (rlgD Cf Qn (e ℓ) s t)) ^ 2 := by
      intro ℓ
      simp_rw [h2]
      refine (rlg_mode_fourth hY (mrm_e_test (d := d) (q : ℝ) ℓ) hM0 hM hs ht).trans (le_of_eq ?_)
      rw [mul_pow, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hM0]
    have hbound := rlg_sq_tsum f hfm _ hm
    have hsumvar := rlg_sum_var hK hρ hY.rho_meas hM₂ hmom hs.1 hst ht.2 hQ
    simp_rw [h1]
    refine hbound.trans ?_
    rw [ENNReal.tsum_mul_left]
    calc (ENNReal.ofReal (Real.sqrt M) * ∑' ℓ, ENNReal.ofReal (rlgD Cf Qn (e ℓ) s t)) ^ 2
        ≤ (ENNReal.ofReal (Real.sqrt M) * ENNReal.ofReal (V * (t - s))) ^ 2 := by gcongr
      _ = ENNReal.ofReal (M * V ^ 2 * |t - s| ^ 2) := by
          rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg _), ← ENNReal.ofReal_pow (by
            exact mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (by positivity) (sub_nonneg.2 hst)))]
          congr 1
          rw [abs_of_nonneg (sub_nonneg.2 hst), mul_pow, mul_pow, Real.sq_sqrt hM0]
          ring
  intro s hs t ht
  rcases le_total s t with h | h
  · exact core s hs t ht h
  · have := core t ht s hs h
    rw [abs_sub_comm] at this
    refine le_trans (le_of_eq ?_) this
    exact lintegral_congr fun ζ => by rw [enorm_sub_rev]

theorem rlg_rpow4 (x : ℝ≥0∞) : x ^ (4 : ℝ) = x ^ 4 := by
  rw [← ENNReal.rpow_natCast]; norm_num

theorem rlg_rpow2 (x : ℝ) : x ^ (1 + (1 : ℝ)) = x ^ 2 := by
  rw [show (1 : ℝ) + 1 = 2 by norm_num, Real.rpow_two]

theorem rlg_cvt_to_has {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    {T : ℝ} (P'' : Measure Ω') (Y : ℝ → Ω' → E)
    (Zc : ℕ → ℝ → Ω' → E)
    (h : ContVersionTight T (fun _ : ℕ => P'') (fun _ => Y) Zc) :
    HasContVersion T P'' Y (Zc 1) := by
  obtain ⟨c1, c2, -⟩ := h
  refine ⟨fun t ht => c1 1 le_rfl t ht, ?_⟩
  filter_upwards [c2 1 le_rfl] with ζ hζ
  exact continuousOn_iff_continuous_restrict.2 hζ

/-- Kolmogorov-Chentsov for the limiting Gaussian convolution, conditional on the kernel bound. -/
theorem rlg_limit_cont {A Qn : ℝ} (hQ : 0 ≤ Qn) (hT : 0 < T) {Y : ℝ → Ω' → HNeg d (q : ℝ)}
    (hY : IsAdjointDualityLimitW P' Cf (q : ℝ) A Qn T (fun _ _ => 0) Y)
    (hker : KernelBoundRd Cf T q C₁)
    (hρ : ∀ r ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (Cf.ρ r))
    {M₂ : ℝ} (hM₂ : 0 ≤ M₂)
    (hmom : ∀ r ∈ Set.Icc (0 : ℝ) T, Integrable (fun x : Euc d => (1 + ‖x‖) ^ 2 * Cf.ρ r x) ∧
      ∫ x : Euc d, (1 + ‖x‖) ^ 2 * Cf.ρ r x ≤ M₂) :
    ∃ Yc, HasContVersion T P' Y Yc := by
  obtain ⟨Kern, hK⟩ := mrmKern_exists Cf T q C₁ hker
  obtain ⟨C, hC⟩ := rlg_fourth_moment hQ hY hK hρ hM₂ hmom
  have hmom4 : ∀ N : ℕ, 1 ≤ N → ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ζ, ‖(fun (_ : ℕ) => Y) N t ζ - (fun (_ : ℕ) => Y) N s ζ‖ₑ ^ (4 : ℝ)
          ∂((fun _ : ℕ => P') N) ≤ ENNReal.ofReal (C * |t - s| ^ (1 + (1 : ℝ))) := by
    intro N _ s hs t ht
    simp only [rlg_rpow4, rlg_rpow2]
    exact hC s hs t ht
  obtain ⟨Zc, hZc⟩ := HRS.MP.KC.kolmogorov_modulus_tightness_proof
    (E := HNeg d (q : ℝ)) (Ω := fun _ : ℕ => Ω') T hT (fun _ => P')
    (fun _ => Y) (fun _ _ => hY.meas) 4 1 C (by norm_num) (by norm_num) hmom4
  exact ⟨Zc 1, rlg_cvt_to_has P' Y Zc hZc⟩

end Fourth

/-! ### Part VI: Lemma S.A.24 (c) on `ℝ^d`, conditional on the kernel bound of S.A.22 -/

/-- Clause (c) of `HRS.Whole.AppendixALemmas.path_martingale_modulus_rd`, conditional on the kernel bound
`KernelBoundRd (L.coeff S) T (Γ+2) C₁` (the output of `path_propagator_increment_rd`): the limiting Gaussian
stochastic convolution has a continuous `H^{-(Γ+2)}`-valued version.  The `CoeffHypRd` field of
`LimitPathHyp` supplies the probability densities and the second moment of `ρ^r`
(`∫ (1+|x|)² ρ^r ≤ M₂`, from the decay `⟨x⟩^{d+3}|ρ^r| ≤ Λ`).  `Y_0 = 0` is not needed. -/
theorem path_limit_cont_rd_of_kernel {s : ℝ} (fd : FieldDensityRd d s) (S : WholeMainData d)
    (L : LimitCoeffsRd d) (ν₀ Λ Kadj Cw : ℝ) (m₀ : ℕ) (T C₁ : ℝ) (hT : S.T = T)
    (hL : LimitPathHyp S L fd ν₀ Λ Kadj Cw m₀)
    (hker : KernelBoundRd (L.coeff S) T (fd.Gamma + 2) C₁)
    {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : ℝ → Ω' → HNeg d ((fd.Gamma + 2 : ℕ) : ℝ))
    (hY : IsAdjointDualityLimitW P' (L.coeff S) ((fd.Gamma + 2 : ℕ) : ℝ) L.A L.invβstar T
      (fun _ _ => 0) Y) :
    ∃ Yc, HasContVersion T P' Y Yc := by
  have hTpos : 0 < T := hT ▸ S.hT
  have hcoeff : CoeffHypRd S.s (fd.Gamma + 2) Λ T L.ρ := hT ▸ hL.coeff
  obtain ⟨M₂, hM₂, hmom⟩ := rlg_mom hcoeff.regular hcoeff.prob
  exact rlg_limit_cont L.hinvβstar hTpos hY hker hcoeff.prob hM₂ hmom

end HRS.MP.RdLGS
