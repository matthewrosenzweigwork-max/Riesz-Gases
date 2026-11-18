/-
# HRS.Equilibrium.Q84dAuxI — packet Q84d: envelope bounds for `ψ`, `h_f` and integrals of `w`
-/
import HRS.Equilibrium.Q84dAuxH
import HRS.Equilibrium.LocalDivMain

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84d

variable {d : ℕ} {s : ℝ} {N : ℕ}

/-- `|ψ| ≤ 2 K w` off the diagonal, from the size condition `Q:eq:psi-size`. -/
theorem q84d_psi_le_w (hs1 : 1 ≤ s) {ψ : Torus d → Torus d → ℝ} {K : ℝ} (hψ : PsiSize s K ψ)
    (hK : 0 ≤ K) {x y : Torus d} (hxy : x ≠ y) : |ψ x y| ≤ 2 * K * wEnv s x y := by
  have h := hψ.size x y hxy
  have hr := PairCorrAux.rTrunc_pos hxy
  have hr1 := PairCorrAux.rTrunc_le_one x y
  set r := rTrunc x y with hrdef
  have hp0 : 0 ≤ r ^ (-s) := Real.rpow_nonneg hr.le _
  have h1 : r ^ (2 - s) ≤ r ^ (-s) := Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
  have h2 : r⁻¹ ≤ r ^ (-s) := by
    have := Real.rpow_le_rpow_of_exponent_ge hr hr1 (show -s ≤ -1 by linarith)
    rwa [Real.rpow_neg_one] at this
  have h3 : |Real.log r| ≤ r ^ (-s) := by
    rw [abs_of_nonpos (Real.log_nonpos hr.le hr1), ← Real.log_inv]
    have := Real.log_le_sub_one_of_pos (inv_pos.2 hr)
    linarith
  have h4 : 1 + r ^ (2 - s) + (if s = 2 then |Real.log r| else 0) ≤ 2 * wEnv s x y := by
    unfold wEnv
    rw [← hrdef]
    split_ifs <;> linarith
  calc |ψ x y| ≤ K * (1 + r ^ (2 - s) + if s = 2 then |Real.log r| else 0) := h
    _ ≤ K * (2 * wEnv s x y) := mul_le_mul_of_nonneg_left h4 hK
    _ = 2 * K * wEnv s x y := by ring

theorem q84d_eucDist_rpow_le_w (hs0 : 0 ≤ s) {x y : Torus d} (hxy : x ≠ y) :
    Torus.eucDist x y ^ (-s) ≤ wEnv s x y := by
  have hpos : 0 < Torus.eucDist x y :=
    lt_of_le_of_ne (PairCorrAux.eucDist_nonneg' x y)
      (fun h => hxy ((PairCorrAux.eucDist_eq_zero' x y).1 h.symm))
  unfold wEnv rTrunc
  rcases le_or_gt (Torus.eucDist x y) 1 with h | h
  · rw [min_eq_right h]; linarith
  · rw [min_eq_left h.le, Real.one_rpow]
    have : Torus.eucDist x y ^ (-s) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos h.le (by linarith)
    linarith

/-- `|h_f| ≤ B w` off the diagonal. -/
theorem q84d_hTransport_le_w (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {f : Torus d → ℝ}
    (hf : Torus.IsSmooth f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x y : Torus d, x ≠ y → |hTransport d s f x y| ≤ B * wEnv s x y := by
  obtain ⟨B, hB0, hB⟩ := HRS.LocalDivAux.h_bound_torus hd hs0 hsd hf
  refine ⟨B, hB0, fun x y hxy => ?_⟩
  have hpos : 0 < Torus.eucDist x y :=
    lt_of_le_of_ne (PairCorrAux.eucDist_nonneg' x y)
      (fun h => hxy ((PairCorrAux.eucDist_eq_zero' x y).1 h.symm))
  exact (hB x y hpos).trans (mul_le_mul_of_nonneg_left (q84d_eucDist_rpow_le_w hs0 hxy) hB0)

section Wint

variable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2)
include hd hcrit

theorem q84d_integrable_wEnv (x : Torus d) : Integrable (fun z => wEnv s x z) := by
  refine ⟨(PairCorrAux.measurable_wEnv s x).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun z =>
    (zero_le_one.trans (PairCorrAux.one_le_wEnv s x z) : (0 : ℝ) ≤ wEnv s x z))]
  exact lt_of_le_of_lt (PairCorrAux.radial_B0 hd hcrit x) ENNReal.ofReal_lt_top

theorem q84d_integral_wEnv_le : ∃ c : ℝ, 0 ≤ c ∧ ∀ x : Torus d, ∫ z, wEnv s x z ≤ c := by
  set c : ℝ := PairCorrAux.cdR d * ((1 / d + 1 / s) * 1 ^ s) + 2 with hc
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < s := by rw [hcrit]; linarith
  have hc0 : 0 ≤ c := by have := PairCorrAux.cdR_nonneg d; positivity
  refine ⟨c, hc0, fun x => ?_⟩
  have h1 := q84d_integrable_wEnv hd hcrit x
  have h2 : ∫ z, wEnv s x z = (∫⁻ z, ENNReal.ofReal (wEnv s x z)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun z =>
      (zero_le_one.trans (PairCorrAux.one_le_wEnv s x z))) h1.aestronglyMeasurable
  rw [h2]
  have h3 := PairCorrAux.radial_B0 hd hcrit x
  calc (∫⁻ z, ENNReal.ofReal (wEnv s x z)).toReal ≤ (ENNReal.ofReal c).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h3
    _ = c := ENNReal.toReal_ofReal hc0

omit hd hcrit in
theorem q84d_withDensity_le {ρ : Torus d → ℝ} {Λ : ℝ} (hρΛ : ∀ x, ρ x ≤ Λ) :
    withDensityReal ρ ≤ ENNReal.ofReal Λ • (volume : Measure (Torus d)) := by
  unfold withDensityReal
  rw [← withDensity_const]
  exact withDensity_mono (Filter.Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal (hρΛ x))

theorem q84d_integral_wEnv_mu_le {ρ : Torus d → ℝ} (hρs : SmoothPosDensity ρ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x : Torus d, Integrable (fun y => wEnv s x y) (withDensityReal ρ) ∧
      ∫ y, wEnv s x y ∂(withDensityReal ρ) ≤ M := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := PoleCavityAux.exists_density_bound hρs
  obtain ⟨c, hc0, hc⟩ := q84d_integral_wEnv_le hd hcrit
  have hle := q84d_withDensity_le hΛ
  refine ⟨Λ * c, mul_nonneg hΛ0.le hc0, fun x => ⟨?_, ?_⟩⟩
  · exact ((q84d_integrable_wEnv hd hcrit x).smul_measure ENNReal.ofReal_ne_top).mono_measure hle
  · calc ∫ y, wEnv s x y ∂(withDensityReal ρ)
        ≤ ∫ y, wEnv s x y ∂(ENNReal.ofReal Λ • (volume : Measure (Torus d))) :=
          integral_mono_measure hle (Filter.Eventually.of_forall fun z =>
            (zero_le_one.trans (PairCorrAux.one_le_wEnv s x z)))
            ((q84d_integrable_wEnv hd hcrit x).smul_measure ENNReal.ofReal_ne_top)
      _ = Λ * ∫ y, wEnv s x y := by
          rw [integral_smul_measure, ENNReal.toReal_ofReal hΛ0.le, smul_eq_mul]
      _ ≤ Λ * c := mul_le_mul_of_nonneg_left (hc x) hΛ0.le

end Wint

end HRS.Q84d

end
