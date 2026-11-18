import HRS.Kernel.Riesz

/-!
# Q33 helpers: uniform row bound for the torus periodic logarithm (supplement S11.5, torus clause)

Packet Q33 (W-LOG-ROW).  All constants below depend only on `d` and the bound `Λ`, never on the density `ρ`
(`periodic_log_row` gives its constant only after `ρ`, so its row bound is re-derived here with explicit constants).
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HRS.Whole

/-- `∫⁻ |g|` of the periodic logarithm `g = periodicRiesz d 0` over the torus. -/
def q33A (d : ℕ) : ℝ≥0∞ := ∫⁻ z : HRS.Torus d, ENNReal.ofReal ‖HRS.periodicRiesz d 0 z‖

/-- Uniform bound `T1` on `|g * μ|` for `μ = ρ dx`, `ρ ≤ Λ`. -/
def q33T1 (d : ℕ) (Λ : ℝ) : ℝ := (ENNReal.ofReal Λ * q33A d).toReal

/-- Uniform bound `T2` on `|∬ g dμ dμ|` for `μ = ρ dx`, `ρ ≤ Λ`. -/
def q33T2 (d : ℕ) (Λ : ℝ) : ℝ := (ENNReal.ofReal (q33T1 d Λ) * ENNReal.ofReal Λ).toReal

/-- `∫ exp(|g|)` over the torus (exponent `1`). -/
def q33I (d : ℕ) : ℝ≥0∞ :=
  ∫⁻ z : HRS.Torus d, ENNReal.ofReal (Real.exp (1 * |HRS.periodicRiesz d 0 z|))

/-- The uniform row constant. -/
def q33C (d : ℕ) (Λ : ℝ) : ℝ :=
  (ENNReal.ofReal (Real.exp (2 * q33T1 d Λ + q33T2 d Λ)) * (ENNReal.ofReal Λ * q33I d)).toReal

variable {d : ℕ}

theorem q33_A_ne_top (hd : 2 ≤ d) : q33A d ≠ ⊤ := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have h := (HRS.integral_periodicRiesz (s := 0) hd le_rfl hdR).1.2
  unfold HasFiniteIntegral at h
  unfold q33A
  simp only [ofReal_norm]
  exact h.ne

theorem q33_I_ne_top (hd : 2 ≤ d) : q33I d ≠ ⊤ :=
  (HRS.KernelAux2.lintegral_exp_abs_log_lt_top hd one_pos (by exact_mod_cast (show 1 < d by omega))).ne

theorem q33_T1_nonneg (Λ : ℝ) : 0 ≤ q33T1 d Λ := ENNReal.toReal_nonneg

theorem q33_T2_nonneg (Λ : ℝ) : 0 ≤ q33T2 d Λ := ENNReal.toReal_nonneg

/-- Mass bound: `μ = ρ dx ≤ Λ` in total mass. -/
theorem q33_mass_le (Λ : ℝ) (ρ : HRS.Torus d → ℝ) (hΛ : ∀ x, ρ x ≤ Λ) :
    HRS.withDensityReal ρ Set.univ ≤ ENNReal.ofReal Λ := by
  have h := HRS.KernelAux2.withDensityReal_le ρ Λ hΛ Set.univ
  simpa using h

/-- Uniform pointwise bound `|g * μ(x)| ≤ T1` for `μ = ρ dx`, `ρ ≤ Λ`. -/
theorem q33_conv_le (hd : 2 ≤ d) (Λ : ℝ) (ρ : HRS.Torus d → ℝ) (hΛ : ∀ x, ρ x ≤ Λ) (x : HRS.Torus d) :
    ‖HRS.convMeasure (HRS.periodicRiesz d 0) (HRS.withDensityReal ρ) x‖ ≤ q33T1 d Λ := by
  have h1 := norm_integral_le_lintegral_norm (μ := HRS.withDensityReal ρ)
    (fun y => HRS.periodicRiesz d 0 (x - y))
  have h2 := HRS.KernelAux2.lintegral_conv_le ρ Λ hΛ (fun z => ENNReal.ofReal ‖HRS.periodicRiesz d 0 z‖) x
  unfold HRS.convMeasure
  unfold q33T1
  exact h1.trans (ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (q33_A_ne_top hd)) h2)

/-- Uniform bound `|∬ g dμ dμ| ≤ T2` for `μ = ρ dx`, `ρ ≤ Λ`. -/
theorem q33_energy_le (hd : 2 ≤ d) (Λ : ℝ) (ρ : HRS.Torus d → ℝ) (hΛ : ∀ x, ρ x ≤ Λ) :
    |HRS.energyPairing (HRS.periodicRiesz d 0) (HRS.withDensityReal ρ) (HRS.withDensityReal ρ)| ≤ q33T2 d Λ := by
  have hE : HRS.energyPairing (HRS.periodicRiesz d 0) (HRS.withDensityReal ρ) (HRS.withDensityReal ρ) =
      ∫ x, HRS.convMeasure (HRS.periodicRiesz d 0) (HRS.withDensityReal ρ) x ∂(HRS.withDensityReal ρ) := rfl
  rw [hE, ← Real.norm_eq_abs]
  have h1 := norm_integral_le_lintegral_norm (μ := HRS.withDensityReal ρ)
    (fun x => HRS.convMeasure (HRS.periodicRiesz d 0) (HRS.withDensityReal ρ) x)
  have h2 : ∫⁻ x, ENNReal.ofReal ‖HRS.convMeasure (HRS.periodicRiesz d 0) (HRS.withDensityReal ρ) x‖
      ∂(HRS.withDensityReal ρ) ≤ ENNReal.ofReal (q33T1 d Λ) * ENNReal.ofReal Λ := by
    calc _ ≤ ∫⁻ _x, ENNReal.ofReal (q33T1 d Λ) ∂(HRS.withDensityReal ρ) :=
          lintegral_mono fun x => ENNReal.ofReal_le_ofReal (q33_conv_le hd Λ ρ hΛ x)
      _ = ENNReal.ofReal (q33T1 d Λ) * HRS.withDensityReal ρ Set.univ := lintegral_const _
      _ ≤ ENNReal.ofReal (q33T1 d Λ) * ENNReal.ofReal Λ := by
          gcongr
          exact q33_mass_le Λ ρ hΛ
  have hfin : ENNReal.ofReal (q33T1 d Λ) * ENNReal.ofReal Λ ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  unfold q33T2
  exact h1.trans (ENNReal.toReal_mono hfin h2)


/-- Integrability of `(x,y) ↦ g(x-y)` against `μ ⊗ μ` for `μ = ρ dx`, `ρ ≤ Λ` (torus). -/
theorem q33_integrable (hd : 2 ≤ d) (Λ : ℝ) (ρ : HRS.Torus d → ℝ) (hΛ : ∀ x, ρ x ≤ Λ) :
    Integrable (fun p : HRS.Torus d × HRS.Torus d => HRS.periodicRiesz d 0 (p.1 - p.2))
      ((HRS.withDensityReal ρ).prod (HRS.withDensityReal ρ)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hG : Integrable (HRS.periodicRiesz d 0) (volume : Measure (HRS.Torus d)) :=
    (HRS.integral_periodicRiesz (s := 0) hd le_rfl hdR).1
  have h2 := (integrable_const (1 : ℝ) : Integrable (fun _ : HRS.Torus d => (1 : ℝ))
    (volume : Measure (HRS.Torus d))).convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hG
  have h3 : Integrable (fun p : HRS.Torus d × HRS.Torus d => HRS.periodicRiesz d 0 (p.1 - p.2))
      ((volume : Measure (HRS.Torus d)).prod volume) := by
    simpa using h2
  haveI : IsFiniteMeasure (HRS.withDensityReal ρ) :=
    ⟨(q33_mass_le Λ ρ hΛ).trans_lt ENNReal.ofReal_lt_top⟩
  have hle : (HRS.withDensityReal ρ).prod (HRS.withDensityReal ρ) ≤
      (ENNReal.ofReal Λ * ENNReal.ofReal Λ) •
        ((volume : Measure (HRS.Torus d)).prod volume) := by
    calc (HRS.withDensityReal ρ).prod (HRS.withDensityReal ρ)
        ≤ (ENNReal.ofReal Λ • (volume : Measure (HRS.Torus d))).prod
            (ENNReal.ofReal Λ • (volume : Measure (HRS.Torus d))) :=
          Measure.prod_mono (HRS.KernelAux2.withDensityReal_le ρ Λ hΛ)
            (HRS.KernelAux2.withDensityReal_le ρ Λ hΛ)
      _ = (ENNReal.ofReal Λ * ENNReal.ofReal Λ) •
            ((volume : Measure (HRS.Torus d)).prod volume) := by
          rw [Measure.prod_smul_left, Measure.prod_smul_right, smul_smul]
  exact (h3.smul_measure (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)).mono_measure hle

/-- Uniform row bound (torus): `∫⁻ exp(|g_μ(x,y)|) dμ(y) ≤ C` with `C` depending only on `d, Λ`. -/
theorem q33_row_le (hd : 2 ≤ d) (Λ : ℝ) (ρ : HRS.Torus d → ℝ) (hΛ : ∀ x, ρ x ≤ Λ) (x : HRS.Torus d) :
    ∫⁻ y, ENNReal.ofReal (Real.exp (1 * |HRS.centeredKernel (HRS.periodicRiesz d 0)
        (HRS.withDensityReal ρ) x y|)) ∂(HRS.withDensityReal ρ) ≤ ENNReal.ofReal (q33C d Λ) := by
  have hpt : ∀ y, ENNReal.ofReal (Real.exp (1 * |HRS.centeredKernel (HRS.periodicRiesz d 0)
      (HRS.withDensityReal ρ) x y|))
      ≤ ENNReal.ofReal (Real.exp (2 * q33T1 d Λ + q33T2 d Λ)) *
        ENNReal.ofReal (Real.exp (1 * |HRS.periodicRiesz d 0 (x - y)|)) := by
    intro y
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have hx := q33_conv_le hd Λ ρ hΛ x
    have hy := q33_conv_le hd Λ ρ hΛ y
    have hE := q33_energy_le hd Λ ρ hΛ
    have hxa := abs_le.1 hx
    have hya := abs_le.1 hy
    have hEa := abs_le.1 hE
    have hG1 := neg_abs_le (HRS.periodicRiesz d 0 (x - y))
    have hG2 := le_abs_self (HRS.periodicRiesz d 0 (x - y))
    unfold HRS.centeredKernel
    rw [one_mul, one_mul, abs_le]
    constructor <;> linarith [hxa.1, hxa.2, hya.1, hya.2, hEa.1, hEa.2, hG1, hG2]
  calc _ ≤ ∫⁻ y, ENNReal.ofReal (Real.exp (2 * q33T1 d Λ + q33T2 d Λ)) *
        ENNReal.ofReal (Real.exp (1 * |HRS.periodicRiesz d 0 (x - y)|)) ∂(HRS.withDensityReal ρ) :=
        lintegral_mono hpt
    _ = ENNReal.ofReal (Real.exp (2 * q33T1 d Λ + q33T2 d Λ)) *
        ∫⁻ y, ENNReal.ofReal (Real.exp (1 * |HRS.periodicRiesz d 0 (x - y)|)) ∂(HRS.withDensityReal ρ) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (Real.exp (2 * q33T1 d Λ + q33T2 d Λ)) * (ENNReal.ofReal Λ * q33I d) := by
        gcongr
        exact HRS.KernelAux2.lintegral_conv_le ρ Λ hΛ
          (fun z => ENNReal.ofReal (Real.exp (1 * |HRS.periodicRiesz d 0 z|))) x
    _ = ENNReal.ofReal (q33C d Λ) := by
        unfold q33C
        rw [ENNReal.ofReal_toReal]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (q33_I_ne_top hd))

end HRS.Whole
