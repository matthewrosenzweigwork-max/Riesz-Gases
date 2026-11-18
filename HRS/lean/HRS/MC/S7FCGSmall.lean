import Mathlib
import HRS.Torus.Basic

/-!
# FC-G, part 3: smallness of the `L^2` norm under the time-`t` background

If `mu_t <= kappa mu_0` and `||k_L||_{L^{2+eps}(mu_0 x mu_0)} -> 0` then
`iint k_L^2 d(mu_t x mu_t) -> 0` (as an `ℝ≥0∞` lintegral).  Packet prefix `fcg`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MC.Sec7.FCG

variable {d : ℕ}

/-- `∫⁻ ofReal (f^2) = ‖f‖_2^2`. -/
theorem fcg_lintegral_sq {α : Type*} [MeasurableSpace α] (ν : Measure α) {f : α → ℝ}
    (hf : Measurable f) :
    ∫⁻ x, ENNReal.ofReal (f x ^ 2) ∂ν = eLpNorm f (ENNReal.ofReal 2) ν ^ (2 : ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by simp) ENNReal.ofReal_ne_top hf.aestronglyMeasurable,
    ENNReal.toReal_ofReal (by norm_num), ← ENNReal.rpow_mul]
  norm_num
  refine lintegral_congr fun x => ?_
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]

theorem fcg_small {μ0 μt : Measure (Torus d)} [IsProbabilityMeasure μ0] [IsProbabilityMeasure μt]
    {κ : ℝ} (hκ : μt ≤ ENNReal.ofReal κ • μ0) {kk : ℕ → Torus d → Torus d → ℝ}
    (hmeas : ∀ L, Measurable (Function.uncurry (kk L))) {ε : ℝ} (hε : 0 < ε)
    (hconv : Tendsto (fun L => eLpNorm (fun p : Torus d × Torus d => kk L p.1 p.2)
      (ENNReal.ofReal (2 + ε)) (μ0.prod μ0)) atTop (𝓝 0)) :
    Tendsto (fun L => ∫⁻ z : Torus d × Torus d, ENNReal.ofReal (kk L z.1 z.2 ^ 2) ∂(μt.prod μt))
      atTop (𝓝 0) := by
  have hprod : μt.prod μt ≤ (ENNReal.ofReal κ * ENNReal.ofReal κ) • μ0.prod μ0 := by
    calc μt.prod μt ≤ (ENNReal.ofReal κ • μ0).prod (ENNReal.ofReal κ • μ0) := Measure.prod_mono hκ hκ
      _ = (ENNReal.ofReal κ * ENNReal.ofReal κ) • μ0.prod μ0 := by
        rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  have hbound : ∀ L, ∫⁻ z : Torus d × Torus d, ENNReal.ofReal (kk L z.1 z.2 ^ 2) ∂(μt.prod μt) ≤
      (ENNReal.ofReal κ * ENNReal.ofReal κ) *
        eLpNorm (fun p : Torus d × Torus d => kk L p.1 p.2) (ENNReal.ofReal (2 + ε)) (μ0.prod μ0) ^ (2 : ℝ) := by
    intro L
    have hm : Measurable fun p : Torus d × Torus d => kk L p.1 p.2 := hmeas L
    calc _ ≤ ∫⁻ z : Torus d × Torus d, ENNReal.ofReal (kk L z.1 z.2 ^ 2)
          ∂((ENNReal.ofReal κ * ENNReal.ofReal κ) • μ0.prod μ0) := lintegral_mono' hprod le_rfl
      _ = (ENNReal.ofReal κ * ENNReal.ofReal κ) *
          ∫⁻ z : Torus d × Torus d, ENNReal.ofReal (kk L z.1 z.2 ^ 2) ∂(μ0.prod μ0) := by
        rw [lintegral_smul_measure]; rfl
      _ = (ENNReal.ofReal κ * ENNReal.ofReal κ) *
          eLpNorm (fun p : Torus d × Torus d => kk L p.1 p.2) (ENNReal.ofReal 2) (μ0.prod μ0) ^ (2 : ℝ) := by
        rw [fcg_lintegral_sq (μ0.prod μ0) hm]
      _ ≤ _ := by
        gcongr
        exact eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal (by linarith))
  have hlim : Tendsto (fun L => (ENNReal.ofReal κ * ENNReal.ofReal κ) *
        eLpNorm (fun p : Torus d × Torus d => kk L p.1 p.2) (ENNReal.ofReal (2 + ε)) (μ0.prod μ0) ^ (2 : ℝ))
      atTop (𝓝 0) := by
    have h1 := (ENNReal.continuous_rpow_const (y := (2 : ℝ))).tendsto 0
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h1
    have h2 := h1.comp hconv
    simpa using ENNReal.Tendsto.const_mul h2 (Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      ENNReal.ofReal_ne_top))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => zero_le) hbound

end HRS.MC.Sec7.FCG

end
