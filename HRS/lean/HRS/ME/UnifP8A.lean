import HRS.ME.UnifP7A
import HRS.ME.Marginal

/-!
# Uniform Proposition 2.10, marginal expansion (packet P8): proof

`critical_marginal_expansion_unif_proof` has the frozen statement of `HRS.Main.critical_marginal_expansion`
(`HRS/Main/HeadlineEquilibrium.lean`, not edited; the tie is in `HRS/ME/UnifP8Tie.lean`).
Assembly of `cavity_response_unif` (UnifP5G), `insertion_coefficient_unif_proof` (UnifP7A), the glue
`HRS.ME.Marginal.me_marg_glue` and a uniform `L²(μ)` bound for the response `h = R P ρ` (helper `p8_resp_L2_le`).
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.ME.Unif

open HRS HRS.Main HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer HRS.CavResp

variable {d : ℕ}

/-- Uniform `L²(μ)` bound for the response: `∫ h² dμ ≤ Λ²` when `ρ ≤ Λ`. -/
theorem p8_resp_L2_le (hd : 2 ≤ d) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {β : ℝ} (hβ : 0 ≤ β)
    {Λ : ℝ} (hΛ : ∀ x, ρ x ≤ Λ) :
    ∫ x, responseInverse (periodicRiesz d ((d : ℝ) / 2)) (withDensityReal ρ) β ρ x ^ 2
      ∂(withDensityReal ρ) ≤ Λ ^ 2 := by
  have hs0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : (d : ℝ) / 2 < d := by linarith
  have hP := PoleCavityAux.isProbabilityMeasure_mu hρ
  set μ := withDensityReal ρ with hμ
  set h := responseInverse (periodicRiesz d ((d : ℝ) / 2)) μ β ρ with hh
  obtain ⟨hm, hp, he⟩ : MemLp h 2 μ ∧ pair μ h = 0 ∧
      ∀ᵐ x ∂μ, h x + β * Kop (periodicRiesz d ((d : ℝ) / 2)) μ h x = projMean μ ρ x :=
    eqbias_response hd hs0 hsd hρ hβ
  have hcoer := eqbias_coercive hd hs0 hsd hρ hβ hm hp
  have hρm := eqbias_memLp_rho hρ
  have hhi : Integrable h μ := hm.integrable one_le_two
  have hhρ : Integrable (fun x => h x * ρ x) μ := hm.integrable_mul hρm
  have hl2 : l2Inner μ h (fun x => h x + β * Kop (periodicRiesz d ((d : ℝ) / 2)) μ h x) =
      ∫ x, h x * ρ x ∂μ := by
    unfold l2Inner
    have : ∫ x, h x * (h x + β * Kop (periodicRiesz d ((d : ℝ) / 2)) μ h x) ∂μ =
        ∫ x, h x * projMean μ ρ x ∂μ := by
      refine integral_congr_ae ?_
      filter_upwards [he] with x hx
      rw [hx]
    rw [this]
    have hpt : ∀ x, h x * projMean μ ρ x = h x * ρ x - pair μ ρ * h x := fun x => by
      unfold projMean; ring
    simp_rw [hpt]
    rw [integral_sub hhρ (hhi.const_mul _), integral_const_mul]
    have : ∫ x, h x ∂μ = 0 := hp
    rw [this]; ring
  rw [hl2] at hcoer
  have hh2 : Integrable (fun x => h x ^ 2) μ := hm.integrable_sq
  have hpt : ∀ x, h x * ρ x ≤ (1 / 2) * h x ^ 2 + (1 / 2) * Λ ^ 2 := by
    intro x
    have h1 := hΛ x
    have h2 := hρ.pos x
    nlinarith [sq_nonneg (h x - ρ x), sq_nonneg (Λ - ρ x), mul_nonneg h2.le (sub_nonneg.2 h1)]
  have hint : ∫ x, h x * ρ x ∂μ ≤ ∫ x, ((1 / 2) * h x ^ 2 + (1 / 2) * Λ ^ 2) ∂μ :=
    integral_mono hhρ ((hh2.const_mul _).add (integrable_const _)) hpt
  rw [integral_add (hh2.const_mul _) (integrable_const _), integral_const_mul,
    integral_const, probReal_univ, one_smul] at hint
  linarith

/-- Lipschitz/sup membership: a smooth density with `ρ ≥ c₀`, `cbNorm 1 ρ ≤ Λ` lies in `UFam d c₀ (max Λ 1)`. -/
theorem p8_ufam {c₀ Λ : ℝ} {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (hlow : ∀ x, c₀ ≤ ρ x)
    (hΛ : Torus.cbNorm 1 ρ ≤ Λ) : UFam d c₀ (max Λ 1) ρ := by
  refine ⟨hρ, hlow, fun x => ?_, hΛ.trans (le_max_left _ _)⟩
  have h1 := HRS.PDE.R2Aux.abs_le_cbNorm (HRS.LocalDivAux.isCk_one_of_smooth hρ.smooth) x
  exact ((le_abs_self _).trans h1).trans (hΛ.trans (le_max_left _ _))

/-- Proposition 2.10 `M:H:prop:critical`, uniform marginal expansion (proof of the frozen statement
`HRS.Main.critical_marginal_expansion`). -/
theorem critical_marginal_expansion_unif_proof (hd : 2 ≤ d) (βm βp : ℝ) (hβm : 0 < βm)
    (hββ : βm ≤ βp) :
    ∃ k₀ : ℕ, ∀ c₀ Λ : ℝ, 0 < c₀ → ∃ C : ℝ, ∀ β : ℝ, β ∈ Set.Icc βm βp →
      ∀ ρ : Torus d → ℝ, SmoothPosDensity ρ → (∀ x, c₀ ≤ ρ x) → Torus.cbNorm k₀ ρ ≤ Λ →
      ∀ N : ℕ, 2 ≤ N →
      firstMarginal (modulatedGibbs (periodicRiesz d ((d : ℝ) / 2)) N β (withDensityReal ρ)) ≪
          withDensityReal ρ ∧
        eLpNorm (fun y =>
            ((firstMarginal (modulatedGibbs (periodicRiesz d ((d : ℝ) / 2)) N β
                (withDensityReal ρ))).rnDeriv (withDensityReal ρ) y).toReal - 1 -
              Real.log N / N * (β ^ 2 * sphereArea d / d *
                responseInverse (periodicRiesz d ((d : ℝ) / 2)) (withDensityReal ρ) β ρ y))
          2 (withDensityReal ρ) ≤ ENNReal.ofReal (C * Real.sqrt (Real.log N) / N) := by
  refine ⟨1, fun c₀ Λ hc₀ => ?_⟩
  have hs0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : (d : ℝ) / 2 < d := by linarith
  obtain ⟨B, hB⟩ := periodicRiesz_ge (d := d) hd hs0 hsd
  have hc : ∀ z, 0 ≤ periodicRiesz d ((d : ℝ) / 2) z + B := fun z => by linarith [hB z]
  set Λ' : ℝ := max Λ 1 with hΛ'
  have hΛ'1 : 1 ≤ Λ' := le_max_right _ _
  obtain ⟨C₁, hC₁⟩ := cavity_response_unif (s := (d : ℝ) / 2) hd rfl βm βp hβm hββ Λ' B hc
  obtain ⟨C₂, hC₂⟩ := insertion_coefficient_unif_proof (s := (d : ℝ) / 2) hd rfl B hc βm βp hβm hββ
    c₀ Λ' hc₀ hΛ'1
  have hS : 0 ≤ sphereArea d / d := by
    have := HRS.StaticLimitsAux.sphereArea_pos hd
    positivity
  refine ⟨|C₁| + |C₂| + βp ^ 2 * (sphereArea d / d) * Λ' / Real.sqrt (Real.log 2),
    fun β hβI ρ hρ hlow hlip N hN => ?_⟩
  have hβ : 0 < β := lt_of_lt_of_le hβm hβI.1
  have hfam := p8_ufam hρ hlow hlip
  have hup := hfam.up
  obtain ⟨hx, ⟨hP, -, -⟩, hF, -, hz⟩ := hC₁ β hβI ρ hρ hup N hN
  refine ⟨hP, ?_⟩
  have hglue := HRS.ME.Marginal.me_marg_glue hd rfl hβ hρ B hc hN hP hF hz
    (fun x => ⟨(hx x).2.2.1, (hx x).2.2.2.2⟩) (hC₂ β hβI ρ hfam N hN)
  refine hglue.trans (ENNReal.ofReal_le_ofReal ?_)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsq : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.2 hlog2
  have hA := p8_resp_L2_le hd hρ hβ.le hup
  have hsA : Real.sqrt (∫ x, responseInverse (periodicRiesz d ((d : ℝ) / 2)) (withDensityReal ρ) β ρ x ^ 2
      ∂(withDensityReal ρ)) ≤ Λ' := by
    calc _ ≤ Real.sqrt (Λ' ^ 2) := Real.sqrt_le_sqrt hA
      _ = Λ' := Real.sqrt_sq (by linarith)
  have hcoef : |β ^ 2 * sphereArea d / d| ≤ βp ^ 2 * (sphereArea d / d) := by
    rw [mul_div_assoc, abs_mul, abs_of_nonneg (sq_nonneg β), abs_of_nonneg hS]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hβ.le hβI.2 2) hS
  have hmid : |C₁| + |C₂| + |β ^ 2 * sphereArea d / d| *
      Real.sqrt (∫ x, responseInverse (periodicRiesz d ((d : ℝ) / 2)) (withDensityReal ρ) β ρ x ^ 2
        ∂(withDensityReal ρ)) / Real.sqrt (Real.log 2) ≤
      |C₁| + |C₂| + βp ^ 2 * (sphereArea d / d) * Λ' / Real.sqrt (Real.log 2) := by
    have : |β ^ 2 * sphereArea d / d| *
        Real.sqrt (∫ x, responseInverse (periodicRiesz d ((d : ℝ) / 2)) (withDensityReal ρ) β ρ x ^ 2
          ∂(withDensityReal ρ)) ≤ βp ^ 2 * (sphereArea d / d) * Λ' :=
      mul_le_mul hcoef hsA (Real.sqrt_nonneg _) (by positivity)
    have := div_le_div_of_nonneg_right this hsq.le
    linarith
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hmid (Real.sqrt_nonneg _)) hN0.le

end HRS.ME.Unif

end
