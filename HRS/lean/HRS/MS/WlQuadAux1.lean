import HRS.MS.WlRefAux3
import HRS.MS.WrQuadAux1

/-!
# HRS.MS.WlQuadAux1 -- centered quadratic functional under the calibrated reference, part 1: envelope integrals (WL-10)

Packet WL-10 of `docs/WR_LOG_PLAN.md` (Step 11 of the proof of `r2_log_static`).  Infrastructure lemmas, not manuscript
rows.  Namespace `HRS.MS.Wl`, helper prefix `wl10_`.  Port of the three envelope integrals of `HRS.MS.WrQuadAux1`
(`wr14a_Hc_bound`, `wr14a_variance_integral_le`, `wr14a_mean_one_le`) from the Riesz envelope `1 + W_s(x - y)` to the
logarithmic envelope `1 + K(x, y)`, `K = sphericalLogKernel`.

Contents.
* `wl10_lintegral_abs_le`: `∫ |f| dν ≤ b c C_p` for `|f| ≤ b (1 + K(x, ·))` and `ν ≤ C_p μ` (from `wl_row_pow`);
  consequences `wl10_Hc_bound` (`|H(x)| ≤ c C_p B`), `wl10_integrable_of_env_bound`, `wl10_abs_cK_le` (envelope of the
  doubly centered kernel);
* `wl10_variance_integral_le` (no retained repulsion is needed: `∫ K² dμ ≤ C₂` by `wl_row_pow`);
* `wl10_mean_one_le` (**the new truncated row mean**, one coordinate): split `{K(x, y) ≤ L}` (bounded by `b (1 + L)`,
  total-variation closeness `ε`) and `{K(x, y) > L}` (`wl_row_tail`, `ν, π ≤ C_p μ`):
  `|∫ f dν - ∫ f dπ| ≤ 2 b (1 + L) ε + 4 c C_p b (1 + L) e^{-dL}` for `L ≥ 1`.

All constants are uniform in `x`, in `ρ` (with `HasSphericalBound A ρ`) and in `L ≥ 1`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MS.Wl

open HRS.Whole HRS.MS.Wr HRS.External

variable {d : ℕ}

/-! ### Row mass of the envelope against a dominated measure -/

/-- `∫ (1 + K(x, y)) dν(y) ≤ c C_p` for `ν ≤ C_p μ`, uniformly in `x`. -/
theorem wl10_env_lintegral_le (hd : 2 ≤ d) (A : ℝ) : ∃ c : ℝ, 0 ≤ c ∧ ∀ ρ : Euc d → ℝ,
    HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ →
      ∀ {ν : Measure (Euc d)} {Cp : ℝ}, ν ≤ ENNReal.ofReal Cp • HRS.Whole.withDensityReal ρ → 0 ≤ Cp →
      ∀ x : Euc d, ∫⁻ y, ENNReal.ofReal (1 + sphericalLogKernel x y) ∂ν ≤ ENNReal.ofReal (c * Cp) := by
  obtain ⟨C1, hC10, hC1⟩ := wl_row_pow hd A 1
  refine ⟨1 + C1, by positivity, fun ρ hρ hA {ν Cp} hν hCp x => ?_⟩
  haveI := wl2_isProb hρ
  obtain ⟨hi, hle⟩ := hC1 ρ hρ hA x
  simp only [pow_one] at hi hle
  have hnn : 0 ≤ᵐ[HRS.Whole.withDensityReal ρ] fun y => 1 + sphericalLogKernel x y :=
    Filter.Eventually.of_forall fun y => by
      have := HRS.MS.Comm.comm_log_nonneg x y
      simp only [Pi.zero_apply]; linarith
  have h1 : ∫⁻ y, ENNReal.ofReal (1 + sphericalLogKernel x y) ∂(HRS.Whole.withDensityReal ρ)
      = ENNReal.ofReal (1 + ∫ y, sphericalLogKernel x y ∂(HRS.Whole.withDensityReal ρ)) := by
    have := ofReal_integral_eq_lintegral_ofReal (f := fun y => 1 + sphericalLogKernel x y)
      ((integrable_const (1 : ℝ)).add hi) hnn
    rw [← this, integral_add (integrable_const _) hi]
    simp
  calc ∫⁻ y, ENNReal.ofReal (1 + sphericalLogKernel x y) ∂ν
      ≤ ∫⁻ y, ENNReal.ofReal (1 + sphericalLogKernel x y)
          ∂(ENNReal.ofReal Cp • HRS.Whole.withDensityReal ρ) := lintegral_mono' hν le_rfl
    _ = ENNReal.ofReal Cp * ∫⁻ y, ENNReal.ofReal (1 + sphericalLogKernel x y)
          ∂(HRS.Whole.withDensityReal ρ) := by rw [lintegral_smul_measure, smul_eq_mul]
    _ = ENNReal.ofReal Cp * ENNReal.ofReal (1 + ∫ y, sphericalLogKernel x y ∂(HRS.Whole.withDensityReal ρ)) := by
        rw [h1]
    _ ≤ ENNReal.ofReal Cp * ENNReal.ofReal (1 + C1) := by
        gcongr
    _ = ENNReal.ofReal ((1 + C1) * Cp) := by rw [← ENNReal.ofReal_mul hCp, mul_comm]

/-- `∫ |f| dν ≤ b c C_p` for `|f(y)| ≤ b (1 + K(x, y))` off the point `x`, `ν ≤ C_p μ`. -/
theorem wl10_lintegral_abs_le (hd : 2 ≤ d) (A : ℝ) : ∃ c : ℝ, 0 ≤ c ∧ ∀ ρ : Euc d → ℝ,
    HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ →
      ∀ {ν : Measure (Euc d)} {Cp : ℝ}, ν ≤ ENNReal.ofReal Cp • HRS.Whole.withDensityReal ρ → 0 ≤ Cp →
      ∀ {b : ℝ}, 0 ≤ b → ∀ {x : Euc d} {f : Euc d → ℝ},
      (∀ y, y ≠ x → |f y| ≤ b * (1 + sphericalLogKernel x y)) →
      ∫⁻ y, ENNReal.ofReal |f y| ∂ν ≤ ENNReal.ofReal (b * (c * Cp)) := by
  obtain ⟨c, hc0, hcb⟩ := wl10_env_lintegral_le hd A
  refine ⟨c, hc0, fun ρ hρ hA {ν Cp} hν hCp {b} hb {x f} hf => ?_⟩
  have hae : ∀ᵐ y ∂ν, y ≠ x :=
    (Measure.absolutelyContinuous_of_le_smul hν).ae_le (wl2_ae_ne (by omega) ρ x)
  calc ∫⁻ y, ENNReal.ofReal |f y| ∂ν
      ≤ ∫⁻ y, ENNReal.ofReal b * ENNReal.ofReal (1 + sphericalLogKernel x y) ∂ν := by
        refine lintegral_mono_ae ?_
        filter_upwards [hae] with y hy
        rw [← ENNReal.ofReal_mul hb]
        exact ENNReal.ofReal_le_ofReal (hf y hy)
    _ = ENNReal.ofReal b * ∫⁻ y, ENNReal.ofReal (1 + sphericalLogKernel x y) ∂ν := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal b * ENNReal.ofReal (c * Cp) := by gcongr; exact hcb ρ hρ hA hν hCp x
    _ = ENNReal.ofReal (b * (c * Cp)) := by rw [← ENNReal.ofReal_mul hb]

/-- `|H(x)| ≤ c C_p B` for `|h| ≤ B (1 + K)` off the diagonal and `π ≤ C_p μ`. -/
theorem wl10_Hc_bound (hd : 2 ≤ d) (A : ℝ) : ∃ c : ℝ, 0 ≤ c ∧ ∀ ρ : Euc d → ℝ,
    HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ →
      ∀ {π : Measure (Euc d)} {Cp : ℝ}, π ≤ ENNReal.ofReal Cp • HRS.Whole.withDensityReal ρ → 0 ≤ Cp →
      ∀ {B : ℝ}, 0 ≤ B → ∀ {h : Euc d → Euc d → ℝ},
      (∀ x y, x ≠ y → |h x y| ≤ B * (1 + sphericalLogKernel x y)) →
      ∀ x : Euc d, |wr14a_Hc h π x| ≤ c * Cp * B := by
  obtain ⟨c, hc0, hcb⟩ := wl10_lintegral_abs_le hd A
  refine ⟨c, hc0, fun ρ hρ hA {π Cp} hπ hCp {B} hB {h} hh x => ?_⟩
  unfold wr14a_Hc
  have h1 := norm_integral_le_lintegral_norm (μ := π) (fun y => h x y)
  have h2 := hcb ρ hρ hA hπ hCp hB (x := x) (f := fun y => h x y) (fun y hy => hh x y (Ne.symm hy))
  have h3 : (∫⁻ y, ENNReal.ofReal ‖h x y‖ ∂π).toReal ≤ c * Cp * B := by
    refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
    simp only [Real.norm_eq_abs]
    refine h2.trans (le_of_eq ?_)
    congr 1; ring
  rw [← Real.norm_eq_abs]
  exact h1.trans h3

/-- Integrability of a measurable function with the envelope bound against a dominated measure. -/
theorem wl10_integrable_of_env_bound (hd : 2 ≤ d) (A : ℝ) : ∀ ρ : Euc d → ℝ,
    HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ →
      ∀ {ν : Measure (Euc d)} {Cp : ℝ}, ν ≤ ENNReal.ofReal Cp • HRS.Whole.withDensityReal ρ → 0 ≤ Cp →
      ∀ {b : ℝ}, 0 ≤ b → ∀ {x : Euc d} {f : Euc d → ℝ}, Measurable f →
      (∀ y, y ≠ x → |f y| ≤ b * (1 + sphericalLogKernel x y)) → Integrable f ν := by
  obtain ⟨c, hc0, hcb⟩ := wl10_lintegral_abs_le hd A
  intro ρ hρ hA ν Cp hν hCp b hb x f hfm hf
  refine ⟨hfm.aestronglyMeasurable, ?_⟩
  have h2 := hcb ρ hρ hA hν hCp hb (x := x) (f := f) hf
  have : ∫⁻ y, ‖f y‖ₑ ∂ν ≤ ENNReal.ofReal (b * (c * Cp)) := by
    refine le_trans (le_of_eq ?_) h2
    refine lintegral_congr fun y => ?_
    rw [Real.enorm_eq_ofReal_abs]
  exact lt_of_le_of_lt this ENNReal.ofReal_lt_top

/-! ### The doubly centered kernel -/

/-- The envelope of `h_c = h - H(x) - H(y) + h₀`: `|h_c(x,y)| ≤ (B + 3 H_B) e` when `|h| ≤ B e` and `e ≥ 1`. -/
theorem wl10_abs_cK_le {h : Euc d → Euc d → ℝ} (π : Measure (Euc d)) [IsProbabilityMeasure π] {B HB : ℝ}
    (hHB : ∀ x, |wr14a_Hc h π x| ≤ HB) (x y : Euc d) {e : ℝ} (he : 1 ≤ e) (hh : |h x y| ≤ B * e) :
    |wr14a_cK h π x y| ≤ (B + 3 * HB) * e := by
  unfold wr14a_cK
  have h2 := hHB x
  have h3 := hHB y
  have h4 := wr14a_abs_h0_le π hHB
  have hHB0 : 0 ≤ HB := (abs_nonneg _).trans h2
  have : |h x y - wr14a_Hc h π x - wr14a_Hc h π y + wr14a_h0 h π|
      ≤ |h x y| + |wr14a_Hc h π x| + |wr14a_Hc h π y| + |wr14a_h0 h π| := by
    calc _ ≤ |h x y - wr14a_Hc h π x - wr14a_Hc h π y| + |wr14a_h0 h π| := abs_add_le _ _
      _ ≤ |h x y - wr14a_Hc h π x| + |wr14a_Hc h π y| + |wr14a_h0 h π| := by gcongr; exact abs_sub _ _
      _ ≤ |h x y| + |wr14a_Hc h π x| + |wr14a_Hc h π y| + |wr14a_h0 h π| := by gcongr; exact abs_sub _ _
  nlinarith

/-! ### The variance integral (no retained repulsion needed) -/

/-- `∫ |f|² e^{ψ} dμ ≤ 2 b² e^{M₀} (1 + C₂)` for `|f| ≤ b (1 + K(x, ·))` and `ψ ≤ M₀`. -/
theorem wl10_variance_integral_le (hd : 2 ≤ d) (A : ℝ) : ∃ c : ℝ, 0 ≤ c ∧ ∀ ρ : Euc d → ℝ,
    HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ →
      ∀ {b : ℝ}, 0 ≤ b → ∀ {x : Euc d} {M0 : ℝ} {f ψ : Euc d → ℝ},
      (∀ y, y ≠ x → |f y| ≤ b * (1 + sphericalLogKernel x y)) → (∀ y, ψ y ≤ M0) →
      ∫⁻ y, ‖f y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (ψ y)) ∂(HRS.Whole.withDensityReal ρ)
        ≤ ENNReal.ofReal (c * b ^ 2 * Real.exp M0) := by
  obtain ⟨C2, hC20, hC2⟩ := wl_row_pow hd A 2
  refine ⟨2 * (1 + C2), by positivity, fun ρ hρ hA {b} hb {x M0 f ψ} hf hψ => ?_⟩
  haveI := wl2_isProb hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have hae : ∀ᵐ y ∂μ, y ≠ x := wl2_ae_ne (by omega) ρ x
  obtain ⟨hi2, hle2⟩ := hC2 ρ hρ hA x
  have hi1 : Integrable (fun y => (2 * b ^ 2 * Real.exp M0) * (1 + sphericalLogKernel x y ^ 2)) μ :=
    ((integrable_const (1 : ℝ)).add hi2).const_mul _
  have hnn : 0 ≤ᵐ[μ] fun y => (2 * b ^ 2 * Real.exp M0) * (1 + sphericalLogKernel x y ^ 2) :=
    Filter.Eventually.of_forall fun y => by simp only [Pi.zero_apply]; positivity
  have hpt : ∀ᵐ y ∂μ, ‖f y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (ψ y)) ≤
      ENNReal.ofReal ((2 * b ^ 2 * Real.exp M0) * (1 + sphericalLogKernel x y ^ 2)) := by
    filter_upwards [hae] with y hy
    have h1 := hf y hy
    have hK0 := HRS.MS.Comm.comm_log_nonneg x y
    have e : ‖f y‖ₑ ^ 2 = ENNReal.ofReal (f y ^ 2) := by
      rw [← enorm_pow, Real.enorm_of_nonneg (sq_nonneg _)]
    rw [e, ← ENNReal.ofReal_mul (sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    set g := sphericalLogKernel x y with hg
    have h3 : f y ^ 2 ≤ b ^ 2 * (1 + g) ^ 2 := by
      have := pow_le_pow_left₀ (abs_nonneg _) h1 2
      rwa [mul_pow, sq_abs] at this
    have h4 : Real.exp (ψ y) ≤ Real.exp M0 := Real.exp_le_exp.2 (hψ y)
    have h5 : (1 + g) ^ 2 ≤ 2 * (1 + g ^ 2) := by nlinarith [sq_nonneg (1 - g)]
    calc f y ^ 2 * Real.exp (ψ y) ≤ (b ^ 2 * (1 + g) ^ 2) * Real.exp M0 :=
          mul_le_mul h3 h4 (Real.exp_pos _).le (by positivity)
      _ ≤ (b ^ 2 * (2 * (1 + g ^ 2))) * Real.exp M0 := by gcongr
      _ = (2 * b ^ 2 * Real.exp M0) * (1 + g ^ 2) := by ring
  calc ∫⁻ y, ‖f y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (ψ y)) ∂μ
      ≤ ∫⁻ y, ENNReal.ofReal ((2 * b ^ 2 * Real.exp M0) * (1 + sphericalLogKernel x y ^ 2)) ∂μ :=
        lintegral_mono_ae hpt
    _ = ENNReal.ofReal (∫ y, (2 * b ^ 2 * Real.exp M0) * (1 + sphericalLogKernel x y ^ 2) ∂μ) :=
        (ofReal_integral_eq_lintegral_ofReal hi1 hnn).symm
    _ ≤ ENNReal.ofReal (2 * (1 + C2) * b ^ 2 * Real.exp M0) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_const_mul, integral_add (integrable_const _) hi2]
        simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
        have h0 : 0 ≤ 2 * b ^ 2 * Real.exp M0 := by positivity
        calc 2 * b ^ 2 * Real.exp M0 * (1 + ∫ y, sphericalLogKernel x y ^ 2 ∂μ)
            ≤ 2 * b ^ 2 * Real.exp M0 * (1 + C2) := mul_le_mul_of_nonneg_left (by linarith) h0
          _ = _ := by ring

/-! ### The truncated row mean (one coordinate) -/

/-- **Tail of the envelope**: for `κ ≤ C_p μ` and `L ≥ 1`,
`∫_{K(x,y) > L} (1 + K(x,y)) dκ(y) ≤ 2 c C_p (1 + L) e^{-dL}` (`wl_row_tail`, `1 + K ≤ 2K` on `{K > L}`). -/
theorem wl10_env_tail_lintegral (hd : 2 ≤ d) (A : ℝ) : ∃ c : ℝ, 0 ≤ c ∧ ∀ ρ : Euc d → ℝ,
    HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ →
      ∀ {κ : Measure (Euc d)} {Cp : ℝ}, κ ≤ ENNReal.ofReal Cp • HRS.Whole.withDensityReal ρ → 0 ≤ Cp →
      ∀ (x : Euc d) {L : ℝ}, 1 ≤ L →
      ∫⁻ y, {y : Euc d | L < sphericalLogKernel x y}.indicator
          (fun y => ENNReal.ofReal (1 + sphericalLogKernel x y)) y ∂κ
        ≤ ENNReal.ofReal (c * Cp * (1 + L) * Real.exp (-(d : ℝ) * L)) := by
  obtain ⟨C, hC0, hC⟩ := wl_row_tail hd A
  refine ⟨2 * C, by positivity, fun ρ hρ hA {κ Cp} hκ hCp x {L} hL => ?_⟩
  haveI := wl2_isProb hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set S : Set (Euc d) := {y : Euc d | L < sphericalLogKernel x y} with hS
  have hSm : MeasurableSet S := measurableSet_lt measurable_const (wl2_K_measurable_right x)
  obtain ⟨hint, hle⟩ := hC ρ hρ hA x L hL
  have hL0 : 0 ≤ L := by linarith
  have hmu : ∫⁻ y, S.indicator (fun y => ENNReal.ofReal (1 + sphericalLogKernel x y)) y ∂μ
      ≤ ENNReal.ofReal (2 * C * (1 + L) * Real.exp (-(d : ℝ) * L)) := by
    rw [lintegral_indicator hSm]
    have h1 : ∫⁻ y in S, ENNReal.ofReal (1 + sphericalLogKernel x y) ∂μ
        ≤ ∫⁻ y in S, ENNReal.ofReal (2 * sphericalLogKernel x y) ∂μ := by
      refine setLIntegral_mono' hSm fun y hy => ?_
      refine ENNReal.ofReal_le_ofReal ?_
      have : L < sphericalLogKernel x y := hy
      linarith
    refine h1.trans ?_
    have hi2 : IntegrableOn (fun y => 2 * sphericalLogKernel x y) S μ := hint.const_mul 2
    have hnn : 0 ≤ᵐ[μ.restrict S] fun y => 2 * sphericalLogKernel x y :=
      Filter.Eventually.of_forall fun y => by
        simp only [Pi.zero_apply]; have := HRS.MS.Comm.comm_log_nonneg x y; linarith
    rw [← ofReal_integral_eq_lintegral_ofReal hi2 hnn, integral_const_mul]
    refine ENNReal.ofReal_le_ofReal ?_
    have := mul_le_mul_of_nonneg_left hle (show (0 : ℝ) ≤ 2 by norm_num)
    linarith
  calc ∫⁻ y, S.indicator (fun y => ENNReal.ofReal (1 + sphericalLogKernel x y)) y ∂κ
      ≤ ∫⁻ y, S.indicator (fun y => ENNReal.ofReal (1 + sphericalLogKernel x y)) y
          ∂(ENNReal.ofReal Cp • μ) := lintegral_mono' hκ le_rfl
    _ = ENNReal.ofReal Cp * ∫⁻ y, S.indicator (fun y => ENNReal.ofReal (1 + sphericalLogKernel x y)) y ∂μ := by
        rw [lintegral_smul_measure, smul_eq_mul]
    _ ≤ ENNReal.ofReal Cp * ENNReal.ofReal (2 * C * (1 + L) * Real.exp (-(d : ℝ) * L)) := by gcongr
    _ = ENNReal.ofReal (2 * C * Cp * (1 + L) * Real.exp (-(d : ℝ) * L)) := by
        rw [← ENNReal.ofReal_mul hCp]; congr 1; ring

/-- **Mean of the row, one coordinate, truncated at level `L`** (the new truncated row mean): near part
`{y ≠ x, K(x,y) ≤ L}` bounded by `b (1 + L)` and compared through the total-variation closeness `ε`, far part
`{K(x,y) > L}` by the level-set tail `wl_row_tail`. -/
theorem wl10_mean_one_le (hd : 2 ≤ d) (A : ℝ) : ∃ c : ℝ, 0 ≤ c ∧ ∀ ρ : Euc d → ℝ,
    HRS.Whole.IsProbDensity ρ → HasSphericalBound A ρ →
      ∀ {Cp : ℝ}, 0 ≤ Cp → ∀ {b : ℝ}, 0 ≤ b → ∀ {x : Euc d} {ε L : ℝ}, 0 ≤ ε → 1 ≤ L →
      ∀ {π ν : Measure (Euc d)} [IsProbabilityMeasure π] [IsProbabilityMeasure ν],
      π ≤ ENNReal.ofReal Cp • HRS.Whole.withDensityReal ρ →
      ν ≤ ENNReal.ofReal Cp • HRS.Whole.withDensityReal ρ →
      (∀ S : Set (Euc d), MeasurableSet S → |ν.real S - π.real S| ≤ ε) →
      ∀ {f : Euc d → ℝ}, Measurable f →
      (∀ y, y ≠ x → |f y| ≤ b * (1 + sphericalLogKernel x y)) →
      |∫ y, f y ∂ν - ∫ y, f y ∂π|
        ≤ 2 * b * (1 + L) * ε + 2 * (c * Cp * b * (1 + L) * Real.exp (-(d : ℝ) * L)) := by
  obtain ⟨c, hc0, hct⟩ := wl10_env_tail_lintegral hd A
  refine ⟨c, hc0, fun ρ hρ hA {Cp} hCp {b} hb {x ε L} hε hL {π ν} _ _ hπ hν hTV {f} hfm hf => ?_⟩
  have hL0 : 0 ≤ L := by linarith
  set K : Euc d → ℝ := sphericalLogKernel x with hK
  have hKm : Measurable K := wl2_K_measurable_right x
  set T : Set (Euc d) := {y : Euc d | y ≠ x ∧ K y ≤ L} with hT
  have hTm : MeasurableSet T :=
    (measurableSet_singleton x).compl.inter (measurableSet_le hKm measurable_const)
  set f1 : Euc d → ℝ := T.indicator f with hf1
  set f2 : Euc d → ℝ := Tᶜ.indicator f with hf2
  have hsplit : ∀ y, f y = f1 y + f2 y := fun y => by
    have := congrFun (Set.indicator_self_add_compl T f) y
    exact this.symm
  have hf1m : Measurable f1 := hfm.indicator hTm
  have hf1b : ∀ y, |f1 y| ≤ b * (1 + L) := by
    intro y
    by_cases hy : y ∈ T
    · rw [hf1, Set.indicator_of_mem hy]
      have h1 := hf y hy.1
      have h2 : 1 + K y ≤ 1 + L := by linarith [hy.2]
      exact h1.trans (mul_le_mul_of_nonneg_left h2 hb)
    · rw [hf1, Set.indicator_of_notMem hy]; simp; positivity
  have hfi : ∀ (κ : Measure (Euc d)), κ ≤ ENNReal.ofReal Cp • HRS.Whole.withDensityReal ρ → Integrable f κ :=
    fun κ hκ => wl10_integrable_of_env_bound hd A ρ hρ hA hκ hCp hb hfm hf
  have hf1i : ∀ (κ : Measure (Euc d)) [IsProbabilityMeasure κ], Integrable f1 κ := fun κ _ =>
    Integrable.of_bound hf1m.aestronglyMeasurable (b * (1 + L)) (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs]; exact hf1b y)
  have hf2i : ∀ (κ : Measure (Euc d)), κ ≤ ENNReal.ofReal Cp • HRS.Whole.withDensityReal ρ → Integrable f2 κ :=
    fun κ hκ => (hfi κ hκ).indicator hTm.compl
  have hint : ∀ (κ : Measure (Euc d)) [IsProbabilityMeasure κ],
      κ ≤ ENNReal.ofReal Cp • HRS.Whole.withDensityReal ρ → ∫ y, f y ∂κ = ∫ y, f1 y ∂κ + ∫ y, f2 y ∂κ := by
    intro κ _ hκ
    rw [← integral_add (hf1i κ) (hf2i κ hκ)]
    exact integral_congr_ae (Filter.Eventually.of_forall hsplit)
  have htail : ∀ (κ : Measure (Euc d)), κ ≤ ENNReal.ofReal Cp • HRS.Whole.withDensityReal ρ →
      |∫ y, f2 y ∂κ| ≤ c * Cp * b * (1 + L) * Real.exp (-(d : ℝ) * L) := by
    intro κ hκ
    have hae : ∀ᵐ y ∂κ, y ≠ x :=
      (Measure.absolutelyContinuous_of_le_smul hκ).ae_le (wl2_ae_ne (by omega) ρ x)
    set F : Euc d → ℝ≥0∞ := {y : Euc d | L < K y}.indicator (fun y => ENNReal.ofReal (1 + K y)) with hF
    have hpt : ∀ᵐ y ∂κ, ENNReal.ofReal ‖f2 y‖ ≤ ENNReal.ofReal b * F y := by
      filter_upwards [hae] with y hy
      by_cases hyT : y ∈ T
      · rw [hf2, Set.indicator_of_notMem (by simpa using hyT)]
        simp
      · have hK' : L < K y := by
          by_contra hcon
          exact hyT ⟨hy, not_lt.1 hcon⟩
        rw [hf2, Set.indicator_of_mem (show y ∈ Tᶜ from hyT)]
        rw [hF, Set.indicator_of_mem (show y ∈ {y : Euc d | L < K y} from hK'), ← ENNReal.ofReal_mul hb]
        exact ENNReal.ofReal_le_ofReal (by rw [Real.norm_eq_abs]; exact hf y hy)
    have h1 := norm_integral_le_lintegral_norm (μ := κ) f2
    have h2 : ∫⁻ y, ENNReal.ofReal ‖f2 y‖ ∂κ ≤ ENNReal.ofReal (b * (c * Cp * (1 + L) * Real.exp (-(d : ℝ) * L))) := by
      calc ∫⁻ y, ENNReal.ofReal ‖f2 y‖ ∂κ ≤ ∫⁻ y, ENNReal.ofReal b * F y ∂κ := lintegral_mono_ae hpt
        _ = ENNReal.ofReal b * ∫⁻ y, F y ∂κ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal b * ENNReal.ofReal (c * Cp * (1 + L) * Real.exp (-(d : ℝ) * L)) := by
            gcongr
            exact hct ρ hρ hA hκ hCp x hL
        _ = _ := by rw [← ENNReal.ofReal_mul hb]
    rw [← Real.norm_eq_abs]
    refine h1.trans (ENNReal.toReal_le_of_le_ofReal (by positivity) (h2.trans (le_of_eq ?_)))
    congr 1; ring
  have hD : 0 ≤ 2 * (b * (1 + L)) := by positivity
  have h1 := abs_integral_sub_le_of_tv ν π (c := ε) (D := 2 * (b * (1 + L))) hD hTV hf1m (h := f1) (fun z z' => by
    have h1 := abs_le.1 (hf1b z)
    have h2 := abs_le.1 (hf1b z')
    rw [abs_le]; constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2])
  rw [hint ν hν, hint π hπ]
  have e : ∫ y, f1 y ∂ν + ∫ y, f2 y ∂ν - (∫ y, f1 y ∂π + ∫ y, f2 y ∂π)
      = (∫ y, f1 y ∂ν - ∫ y, f1 y ∂π) + ∫ y, f2 y ∂ν - ∫ y, f2 y ∂π := by ring
  rw [e]
  have h3 := htail ν hν
  have h4 := htail π hπ
  have h5 := abs_le.1 h1
  have h6 := abs_le.1 h3
  have h7 := abs_le.1 h4
  rw [abs_le]
  constructor <;> nlinarith [h5.1, h5.2, h6.1, h6.2, h7.1, h7.2, mul_comm ε (2 * (b * (1 + L)))]

end HRS.MS.Wl
