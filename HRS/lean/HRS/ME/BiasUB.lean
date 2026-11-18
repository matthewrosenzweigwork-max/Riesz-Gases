import HRS.ME.BiasH
import HRS.ME.UnifP8A

/-!
# Uniform `critical_bias_constants`: the norm bound of the critical bias (proof of P2)
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ME.Bias

variable {d : ℕ}

open HRS HRS.Main
open HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer HRS.CavResp HRS.PDE

/-- `L²` norm of `c • h` from the second moment bound. -/
theorem p_biasub_eLpNorm_le {μ : Measure (Torus d)} {h : Torus d → ℝ} (hm : MemLp h 2 μ)
    {c B : ℝ} (hc : 0 ≤ c) (hB : 0 ≤ B) (hint : ∫ x, h x ^ 2 ∂μ ≤ B ^ 2) :
    eLpNorm (fun x => c * h x) 2 μ ≤ ENNReal.ofReal (c * B) := by
  have hm' : MemLp (fun x => c * h x) 2 μ := hm.const_mul c
  rw [hm'.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  have e : ∫ x, ‖c * h x‖ ^ (ENNReal.toReal 2) ∂μ = c ^ 2 * ∫ x, h x ^ 2 ∂μ := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [ENNReal.toReal_ofNat, Real.norm_eq_abs]
    rw [Real.rpow_two, sq_abs, mul_pow]
  have h1 : c ^ 2 * ∫ x, h x ^ 2 ∂μ ≤ (c * B) ^ 2 := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_left hint (sq_nonneg c)
  have hcB : 0 ≤ c * B := mul_nonneg hc hB
  rw [e]
  rw [ENNReal.toReal_ofNat, ← one_div, ← Real.sqrt_eq_rpow]
  calc Real.sqrt (c ^ 2 * ∫ x, h x ^ 2 ∂μ) ≤ Real.sqrt ((c * B) ^ 2) := Real.sqrt_le_sqrt h1
    _ = c * B := Real.sqrt_sq hcB

/-- P2: norm bound of the critical bias for densities bounded above by `Λ`. -/
theorem criticalBias_norm_le (hd : 2 ≤ d) {m : ℝ} (hm : (d : ℝ) < 2 * m) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {Λ : ℝ} (hΛ : ∀ x, ρ x ≤ Λ) :
    ‖criticalBias d ((d : ℝ) / 2) β m ρ‖ ≤
      Real.sqrt 2 * (β ^ 2 * sphereArea d / d) * Λ *
        Real.sqrt (∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m))) := by
  have hs0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : (d : ℝ) / 2 < d := by linarith
  have hμP : IsProbabilityMeasure (withDensityReal ρ) := PoleCavityAux.isProbabilityMeasure_mu hρ
  obtain ⟨hmh, -, -⟩ := eqbias_response hd hs0 hsd hρ hβ.le
  set h := responseInverse (periodicRiesz d ((d : ℝ) / 2)) (withDensityReal ρ) β ρ with hhdef
  set c : ℝ := β ^ 2 * sphereArea d / d with hcdef
  have hA : 0 < sphereArea d := HRS.StaticLimitsAux.sphereArea_pos hd
  have hdpos : (0 : ℝ) < d := by linarith
  have hc : 0 ≤ c := by positivity
  have hΛ0 : 0 ≤ Λ := (hρ.pos (0 : Torus d)).le.trans (hΛ _)
  have hL2 := HRS.ME.Unif.p8_resp_L2_le hd hρ hβ.le hΛ
  have hFe := p_biasub_eLpNorm_le hmh hc hΛ0 hL2
  have hGaesm : AEStronglyMeasurable (fun y => c * h y) (withDensityReal ρ) :=
    (hmh.const_mul c).aestronglyMeasurable
  obtain ⟨hIG, hIGb⟩ := integral_abs_mul_le_aesm hρ.density hGaesm (mul_nonneg hc hΛ0) hFe
  have hcbk : ∀ k : NonzeroLattice d,
      NegSobolev.coord (criticalBias d ((d : ℝ) / 2) β m ρ) k =
        Lattice.jp k.1 ^ (-m) * Torus.funRealCoeff (fun y => c * h y * ρ y) k :=
    fun k => coord_ofFun hm hIG k
  have hK : 0 ≤ Real.sqrt 2 * (c * Λ) := mul_nonneg (Real.sqrt_nonneg 2) (mul_nonneg hc hΛ0)
  have hbnd : ∀ k : NonzeroLattice d,
      |NegSobolev.coord (criticalBias d ((d : ℝ) / 2) β m ρ) k| ≤
        (Real.sqrt 2 * (c * Λ)) * Lattice.jp k.1 ^ (-m) := by
    intro k
    have hjp : 0 < Lattice.jp k.1 ^ (-m) := Real.rpow_pos_of_pos (Torus.jp_pos k.1) _
    rw [hcbk k, abs_mul, abs_of_pos hjp]
    have := (abs_funRealCoeff_le_integral hIG k).trans
      (mul_le_mul_of_nonneg_left hIGb (Real.sqrt_nonneg 2))
    nlinarith
  have := norm_le_of_coord_bound hm _ hK hbnd
  calc _ ≤ _ := this
    _ = _ := by ring

end HRS.ME.Bias
