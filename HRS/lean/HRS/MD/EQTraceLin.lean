import HRS.MD.EQTraceBase
import HRS.MD.EQInitParticle
import HRS.MD.EQ29Vocab
import HRS.Main.EqMargFinal

/-!
# EQ-TRACE, linear statistic: `E (μ_N(g) - μ(g))² ≤ K B² b_N²`

For a continuous `g` with `|g| ≤ B`, uniformly in `β ∈ [β₋,β₊]`, the thermal density and `N ≥ 2`:
`E_{ℙ_{N,β}} (μ_N(g) - μ_β(g))² ≤ K B² (N^{-1/2} + δ_N)²`.  Variance part: `eq_static_linear_proof`; bias part
`(m_N - μ)(g)`: `equilibrium_marginal_L2_proof` (`L²(μ)` norm of `dm_N/dμ - 1`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MD.EQTrace

variable {d : ℕ}

theorem eqtrace_enorm_sq (a : ℝ) : ‖a‖ₑ ^ 2 = ENNReal.ofReal (a ^ 2) := by
  rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]

/-- the bias bound: `|∫ g dm - ∫ g dμ| ≤ B ‖dm/dμ - 1‖_{L²(μ)}`. -/
theorem eqtrace_bias_le {m μ : Measure (Torus d)} [IsProbabilityMeasure m] [IsProbabilityMeasure μ]
    (hmμ : m ≪ μ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hL2 : eLpNorm (fun y => (m.rnDeriv μ y).toReal - 1) 2 μ ≤ ENNReal.ofReal δ)
    {g : Torus d → ℝ} (hgm : Measurable g) {B : ℝ} (hB : ∀ x, |g x| ≤ B) :
    |∫ x, g x ∂m - ∫ x, g x ∂μ| ≤ B * δ := by
  set r : Torus d → ℝ := fun y => (m.rnDeriv μ y).toReal with hr
  have hrm : Measurable r := (Measure.measurable_rnDeriv m μ).ennreal_toReal
  have hri : Integrable r μ := Measure.integrable_toReal_rnDeriv
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hgb : ∀ x, ‖g x‖ ≤ B := fun x => by rw [Real.norm_eq_abs]; exact hB x
  have hgi : Integrable g μ :=
    Integrable.of_bound hgm.aestronglyMeasurable B (Filter.Eventually.of_forall hgb)
  have hrg : Integrable (fun x => r x * g x) μ :=
    hri.mul_bdd hgm.aestronglyMeasurable (Filter.Eventually.of_forall hgb)
  have hmg : ∫ x, g x ∂m = ∫ x, r x * g x ∂μ := (integral_toReal_rnDeriv_mul hmμ).symm
  have h1 : ∫ x, g x ∂m - ∫ x, g x ∂μ = ∫ x, (r x - 1) * g x ∂μ := by
    rw [hmg, ← integral_sub hrg hgi]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only []; ring)
  have hf1 : Integrable (fun x => r x - 1) μ := hri.sub (integrable_const _)
  have hfm : AEStronglyMeasurable (fun x => r x - 1) μ := (hrm.sub measurable_const).aestronglyMeasurable
  have h2 : ∫ x, ‖r x - 1‖ ∂μ ≤ δ := by
    rw [integral_norm_eq_lintegral_enorm hfm]
    have e1 : ∫⁻ x, ‖r x - 1‖ₑ ∂μ = eLpNorm (fun x => r x - 1) 1 μ :=
      (eLpNorm_one_eq_lintegral_enorm hfm).symm
    have e2 : eLpNorm (fun x => r x - 1) 1 μ ≤ ENNReal.ofReal δ :=
      (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num)).trans hL2
    rw [e1]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top e2).trans (le_of_eq (ENNReal.toReal_ofReal hδ))
  rw [h1]
  calc |∫ x, (r x - 1) * g x ∂μ| = ‖∫ x, (r x - 1) * g x ∂μ‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x, ‖(r x - 1) * g x‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ x, B * ‖r x - 1‖ ∂μ := by
        refine integral_mono (hf1.mul_bdd hgm.aestronglyMeasurable
          (Filter.Eventually.of_forall hgb)).norm (hf1.norm.const_mul B) fun x => ?_
        simp only [norm_mul]
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (hgb x) (norm_nonneg _)
    _ = B * ∫ x, ‖r x - 1‖ ∂μ := integral_const_mul _ _
    _ ≤ B * δ := mul_le_mul_of_nonneg_left h2 hB0

theorem eqtrace_bracket_sq {s : ℝ} {N : ℕ} (hN : 1 ≤ N) (hδ : 0 ≤ deltaN d s N) :
    (N : ℝ)⁻¹ ≤ EQ29.bracketBias d s N ^ 2 ∧ deltaN d s N ^ 2 ≤ EQ29.bracketBias d s N ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have ha0 : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hN0.le _
  have ha2 : ((N : ℝ) ^ (-(1 : ℝ) / 2)) ^ 2 = (N : ℝ)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le, ← Real.rpow_neg_one]
    congr 1; push_cast; ring
  unfold EQ29.bracketBias
  constructor
  · rw [← ha2]; nlinarith
  · nlinarith

theorem eqtrace_test_L2 (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (βm βp : ℝ) (hβm : 0 < βm) (hββ : βm ≤ βp) :
    ∃ K : ℝ, 0 < K ∧ ∀ β : ℝ, β ∈ Set.Icc βm βp → ∀ ρβ : Torus d → ℝ,
      IsThermalDensity (periodicRiesz d s) V β ρβ → ∀ N : ℕ, 2 ≤ N →
      ∀ (g : Torus d → ℝ) (B : ℝ), Continuous g → (∀ x, |g x| ≤ B) →
        ∫⁻ X, ENNReal.ofReal ((pair (empirical X) g - pair (withDensityReal ρβ) g) ^ 2)
          ∂(canonicalGibbs (periodicRiesz d s) V N β) ≤
        ENNReal.ofReal (K * B ^ 2 * EQ29.bracketBias d s N ^ 2) := by
  obtain ⟨C₁, hC₁, hlin⟩ := MD.EQStat.eq_static_linear_proof hd hs0 hsd V hV βm βp hβm hββ
  obtain ⟨C₂, hC₂, hmarg⟩ := Main.equilibrium_marginal_L2_proof hd hs0 hsd V hV βm βp hβm hββ
  obtain ⟨Lam, hLam⟩ := MD.EQStat.eqstat_thermal_setup hd hs0 hsd V hV βm βp hβm hββ
  refine ⟨2 * (C₁ + C₂ ^ 2), by positivity, ?_⟩
  intro β hβ ρβ hρ N hN g B hgc hgB
  obtain ⟨hρs, hΛ, hP⟩ := hLam β hβ ρβ hρ
  have hβ0 : 0 < β := lt_of_lt_of_le hβm hβ.1
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hgB 0)
  haveI hμ : IsProbabilityMeasure (withDensityReal ρβ) := isProb_withDensityReal hρs.density
  have hPm : canonicalGibbs (periodicRiesz d s) V N β =
      modulatedGibbs (periodicRiesz d s) N β (withDensityReal ρβ) := hP N
  haveI hPr : IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) V N β) := by
    rw [hPm]
    exact HRS.Q32c.q32c_Q_isProb hd hs0 hsd hβ0 (Λ := max Lam 1) (le_max_right _ _) hρs.density
      (fun x => (hΛ x).trans (le_max_left _ _)) (by omega)
  have hex : IsExchangeable (canonicalGibbs (periodicRiesz d s) V N β) := by
    rw [hPm]; exact modulatedGibbs_isExchangeable _ _ _ (fun x => periodicRiesz_neg x)
  set P := canonicalGibbs (periodicRiesz d s) V N β with hPdef
  have hgm : Measurable g := hgc.measurable
  set Y : Config d N → ℝ := fun X => pair (empirical X) g with hY
  have hYe : ∀ X, Y X = (N : ℝ)⁻¹ * ∑ i, g (X i) := fun X => pair_empirical (by omega) X g
  have hYm : Measurable Y := by
    have : Y = fun X => (N : ℝ)⁻¹ * ∑ i, g (X i) := funext hYe
    rw [this]
    exact measurable_const.mul (Finset.measurable_sum _ fun i _ => hgm.comp (measurable_pi_apply i))
  set m : ℝ := ∫ X, Y X ∂P with hm
  have hmeanEmp : meanEmpirical P = firstMarginal P := meanEmpirical_eq_firstMarginal P hex hN1
  haveI hME : IsProbabilityMeasure (meanEmpirical P) := isProbabilityMeasure_meanEmpirical P hN1
  haveI hFM : IsProbabilityMeasure (firstMarginal P) := by rw [← hmeanEmp]; exact hME
  have hmint : m = ∫ x, g x ∂(firstMarginal P) := by
    rw [← hmeanEmp, EQInit.eqinit_meanEmp_integral hN1 P hgc]
  -- the bias
  obtain ⟨hmμ, hL2⟩ := hmarg β hβ ρβ hρ N hN
  have hδ0 : 0 ≤ deltaN d s N := by
    have := MarginalAux.inv_le_deltaN (d := d) hs0 N hN1
    exact (inv_nonneg.2 hN0.le).trans this
  have hbias := eqtrace_bias_le hmμ (mul_nonneg hC₂.le hδ0) hL2 hgm hgB
  have hbias' : |m - pair (withDensityReal ρβ) g| ≤ B * (C₂ * deltaN d s N) := by
    rw [hmint]; exact hbias
  -- the variance
  have hgL2 : MemLp g 2 (withDensityReal ρβ) :=
    MemLp.of_bound hgm.aestronglyMeasurable B (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hgB x)
  have hvar := hlin β hβ ρβ hρ N hN g hgm hgL2
  have hint : ∫ x, g x ^ 2 ∂(withDensityReal ρβ) ≤ B ^ 2 := by
    have hb : ∀ x, g x ^ 2 ≤ B ^ 2 := fun x => by
      have := hgB x
      nlinarith [abs_nonneg (g x), sq_abs (g x)]
    have := integral_mono hgL2.integrable_sq (integrable_const (B ^ 2)) hb
    simpa using this
  have hvar' : evariance Y P ≤ ENNReal.ofReal (C₁ * (N : ℝ)⁻¹ * B ^ 2) := by
    refine hvar.trans (ENNReal.ofReal_le_ofReal ?_)
    have : 0 ≤ C₁ * (N : ℝ)⁻¹ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hint this]
  -- combine
  obtain ⟨hb1, hb2⟩ := eqtrace_bracket_sq (d := d) (s := s) hN1 hδ0
  set c : ℝ := pair (withDensityReal ρβ) g with hc
  have hpt : ∀ X, ENNReal.ofReal ((Y X - c) ^ 2) ≤
      2 * ‖Y X - m‖ₑ ^ 2 + 2 * ENNReal.ofReal ((m - c) ^ 2) := by
    intro X
    rw [eqtrace_enorm_sq]
    have : (Y X - c) ^ 2 ≤ 2 * (Y X - m) ^ 2 + 2 * (m - c) ^ 2 := by
      nlinarith [sq_nonneg (Y X - m - (m - c))]
    calc ENNReal.ofReal ((Y X - c) ^ 2) ≤ ENNReal.ofReal (2 * (Y X - m) ^ 2 + 2 * (m - c) ^ 2) :=
          ENNReal.ofReal_le_ofReal this
      _ = _ := by
          rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by norm_num),
            ENNReal.ofReal_mul (by norm_num)]
          simp
  have hmeasE : Measurable fun X => ‖Y X - m‖ₑ ^ 2 :=
    ((hYm.sub_const m).enorm).pow_const 2
  calc ∫⁻ X, ENNReal.ofReal ((pair (empirical X) g - c) ^ 2) ∂P
      = ∫⁻ X, ENNReal.ofReal ((Y X - c) ^ 2) ∂P := rfl
    _ ≤ ∫⁻ X, (2 * ‖Y X - m‖ₑ ^ 2 + 2 * ENNReal.ofReal ((m - c) ^ 2)) ∂P := lintegral_mono hpt
    _ = 2 * evariance Y P + 2 * ENNReal.ofReal ((m - c) ^ 2) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const_mul' _ _ (by simp)]
        simp only [lintegral_const, measure_univ, mul_one]
        rfl
    _ ≤ 2 * ENNReal.ofReal (C₁ * (N : ℝ)⁻¹ * B ^ 2) + 2 * ENNReal.ofReal ((B * (C₂ * deltaN d s N)) ^ 2) := by
        refine add_le_add (mul_le_mul_right hvar' 2) (mul_le_mul_right (ENNReal.ofReal_le_ofReal ?_) 2)
        have := pow_le_pow_left₀ (abs_nonneg _) hbias' 2
        rwa [sq_abs] at this
    _ = ENNReal.ofReal (2 * (C₁ * (N : ℝ)⁻¹ * B ^ 2) + 2 * (B * (C₂ * deltaN d s N)) ^ 2) := by
        have ha : 0 ≤ C₁ * (N : ℝ)⁻¹ * B ^ 2 :=
          mul_nonneg (mul_nonneg hC₁.le (inv_nonneg.2 hN0.le)) (sq_nonneg B)
        have hb : 0 ≤ (B * (C₂ * deltaN d s N)) ^ 2 := sq_nonneg _
        rw [ENNReal.ofReal_add (mul_nonneg (by norm_num) ha) (mul_nonneg (by norm_num) hb),
          ENNReal.ofReal_mul (p := 2) (q := C₁ * (N : ℝ)⁻¹ * B ^ 2) (by norm_num),
          ENNReal.ofReal_mul (p := 2) (q := (B * (C₂ * deltaN d s N)) ^ 2) (by norm_num)]
        simp only [ENNReal.ofReal_ofNat]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        have e1 : C₁ * (N : ℝ)⁻¹ * B ^ 2 ≤ C₁ * B ^ 2 * EQ29.bracketBias d s N ^ 2 := by
          nlinarith [mul_le_mul_of_nonneg_left hb1 (mul_nonneg hC₁.le (sq_nonneg B))]
        have e2 : (B * (C₂ * deltaN d s N)) ^ 2 ≤ C₂ ^ 2 * B ^ 2 * EQ29.bracketBias d s N ^ 2 := by
          have : (B * (C₂ * deltaN d s N)) ^ 2 = C₂ ^ 2 * B ^ 2 * deltaN d s N ^ 2 := by ring
          rw [this]
          nlinarith [mul_le_mul_of_nonneg_left hb2 (mul_nonneg (sq_nonneg C₂) (sq_nonneg B))]
        nlinarith

end HRS.MD.EQTrace
