import HRS.MS.SA16RHeat10

/-!
# S.A.16 (SA16R) Heat11: `L¹` continuity of the heat kernel and its gradient in the time parameter

`sa16r_g_L1_cont`, `sa16r_dg_L1_cont`: `a ↦ g_a`, `a ↦ ∂_i g_a` are continuous into `L¹` at every `a₀ > 0`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16

section Heat11
variable {d : ℕ}

lemma sa16r_g_cont_a {a0 : ℝ} (ha0 : 0 < a0) (z : Euc d) :
    ContinuousAt (fun a : ℝ => sa16r_g d a z) a0 := by
  unfold sa16r_g
  have h1 : ContinuousAt (fun a : ℝ => (4 * Real.pi * a) ^ (-((d : ℝ) / 2))) a0 := by
    refine ContinuousAt.rpow_const (by fun_prop) (Or.inl (by positivity))
  have h2 : ContinuousAt (fun a : ℝ => Real.exp (-(1 / (4 * a)) * ‖z‖ ^ 2)) a0 := by
    refine Real.continuous_exp.continuousAt.comp ?_
    refine ContinuousAt.mul ?_ continuousAt_const
    refine ContinuousAt.neg (ContinuousAt.div continuousAt_const (by fun_prop) (by positivity))
  exact h1.mul h2

lemma sa16r_dg_cont_a {a0 : ℝ} (ha0 : 0 < a0) (i : Fin d) (z : Euc d) :
    ContinuousAt (fun a : ℝ => sa16r_dg d a i z) a0 := by
  unfold sa16r_dg
  refine ContinuousAt.mul ?_ (sa16r_g_cont_a ha0 z)
  exact ContinuousAt.div continuousAt_const (by fun_prop) (by positivity)

/-- domination of the heat kernel on `[a₀/2, 2a₀]` -/
lemma sa16r_g_dom {a0 a : ℝ} (ha0 : 0 < a0) (ha1 : a0 / 2 ≤ a) (ha2 : a ≤ 2 * a0) (z : Euc d) :
    sa16r_g d a z ≤ (2 * Real.pi * a0) ^ (-((d : ℝ) / 2)) * Real.exp (-(1 / (8 * a0)) * ‖z‖ ^ 2) := by
  have ha : 0 < a := lt_of_lt_of_le (by positivity) ha1
  unfold sa16r_g
  have h1 : (4 * Real.pi * a) ^ (-((d : ℝ) / 2)) ≤ (2 * Real.pi * a0) ^ (-((d : ℝ) / 2)) := by
    refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by
      have : 0 ≤ (d : ℝ) / 2 := by positivity
      linarith)
    nlinarith [Real.pi_pos]
  have h2 : Real.exp (-(1 / (4 * a)) * ‖z‖ ^ 2) ≤ Real.exp (-(1 / (8 * a0)) * ‖z‖ ^ 2) := by
    refine Real.exp_le_exp.2 ?_
    have : 1 / (8 * a0) ≤ 1 / (4 * a) := by
      refine one_div_le_one_div_of_le (by positivity) (by nlinarith)
    nlinarith [sq_nonneg ‖z‖]
  exact mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)

lemma sa16r_g_L1_cont {a0 : ℝ} (ha0 : 0 < a0) :
    Tendsto (fun a : ℝ => ∫⁻ z : Euc d, ‖sa16r_g d a z - sa16r_g d a0 z‖ₑ) (𝓝 a0) (𝓝 0) := by
  set D : Euc d → ℝ := fun z => 2 * ((2 * Real.pi * a0) ^ (-((d : ℝ) / 2)) *
    Real.exp (-(1 / (8 * a0)) * ‖z‖ ^ 2)) with hD
  have hDint : Integrable D := by
    have := (sa16r_gauss_int (d := d) (b := 1 / (8 * a0)) (by positivity)).const_mul
      ((2 * Real.pi * a0) ^ (-((d : ℝ) / 2)))
    exact this.const_mul 2
  have hbd : ∀ᶠ a in 𝓝 a0, ∀ᵐ z ∂(volume : Measure (Euc d)), ‖sa16r_g d a z - sa16r_g d a0 z‖ₑ ≤
      ENNReal.ofReal (D z) := by
    have hnear : ∀ᶠ a in 𝓝 a0, a0 / 2 ≤ a ∧ a ≤ 2 * a0 := by
      filter_upwards [Icc_mem_nhds (show a0 / 2 < a0 by linarith) (show a0 < 2 * a0 by linarith)] with a h
      exact h
    filter_upwards [hnear] with a ha
    refine Eventually.of_forall fun z => ?_
    have hapos : 0 < a := lt_of_lt_of_le (by positivity) ha.1
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := sa16r_g_dom ha0 ha.1 ha.2 z
    have h2 := sa16r_g_dom ha0 (by linarith) (by linarith) z (a := a0)
    rw [Real.norm_eq_abs, abs_le]
    have := sa16r_g_pos hapos z
    have := sa16r_g_pos ha0 z
    constructor <;> simp only [hD] <;> nlinarith
  have hmeas : ∀ᶠ a in 𝓝 a0, Measurable (fun z : Euc d => ‖sa16r_g d a z - sa16r_g d a0 z‖ₑ) :=
    Eventually.of_forall fun a => (sa16r_g_meas.sub sa16r_g_meas).enorm
  have hfin : ∫⁻ z, ENNReal.ofReal (D z) ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hDint (Eventually.of_forall fun z => by
      simp only [hD]; positivity)]
    exact ENNReal.ofReal_ne_top
  have hlim : ∀ᵐ z ∂(volume : Measure (Euc d)),
      Tendsto (fun a : ℝ => ‖sa16r_g d a z - sa16r_g d a0 z‖ₑ) (𝓝 a0) (𝓝 0) := by
    refine Eventually.of_forall fun z => ?_
    have := ((sa16r_g_cont_a ha0 z).tendsto.sub_const (sa16r_g d a0 z)).enorm
    simpa using this
  have := tendsto_lintegral_filter_of_dominated_convergence (μ := volume) (l := 𝓝 a0)
    (F := fun a z => ‖sa16r_g d a z - sa16r_g d a0 z‖ₑ) (f := fun _ => (0 : ℝ≥0∞))
    (fun z => ENNReal.ofReal (D z)) hmeas hbd hfin hlim
  simpa using this

lemma sa16r_dg_dom {a0 a : ℝ} (ha0 : 0 < a0) (ha1 : a0 / 2 ≤ a) (ha2 : a ≤ 2 * a0) (i : Fin d) (z : Euc d) :
    |sa16r_dg d a i z| ≤ (1 / a0) * (2 * Real.sqrt a0) * ((2 * Real.pi * a0) ^ (-((d : ℝ) / 2)) *
      Real.exp (-(1 / (16 * a0)) * ‖z‖ ^ 2)) := by
  have ha : 0 < a := lt_of_lt_of_le (by positivity) ha1
  have hg := sa16r_g_dom ha0 ha1 ha2 z
  have hgpos := sa16r_g_pos ha z
  have hzi : |z i| ≤ ‖z‖ := by
    have := PiLp.norm_apply_le z i
    simpa [Real.norm_eq_abs] using this
  have hn := sa16r_norm_le_exp ha0 ‖z‖ (norm_nonneg z)
  have hC : 0 < (2 * Real.pi * a0) ^ (-((d : ℝ) / 2)) := Real.rpow_pos_of_pos (by positivity) _
  unfold sa16r_dg
  rw [abs_mul, abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 2 * a), abs_of_pos hgpos]
  have h1 : |z i| / (2 * a) ≤ ‖z‖ / a0 := by
    calc |z i| / (2 * a) ≤ ‖z‖ / (2 * a) := by gcongr
      _ ≤ ‖z‖ / a0 := by
        apply div_le_div_of_nonneg_left (norm_nonneg z) ha0
        linarith
  have h2 : ‖z‖ * Real.exp (-(1 / (8 * a0)) * ‖z‖ ^ 2) ≤
      2 * Real.sqrt a0 * Real.exp (-(1 / (16 * a0)) * ‖z‖ ^ 2) := by
    calc ‖z‖ * Real.exp (-(1 / (8 * a0)) * ‖z‖ ^ 2)
        ≤ (2 * Real.sqrt a0 * Real.exp (‖z‖ ^ 2 / (16 * a0))) * Real.exp (-(1 / (8 * a0)) * ‖z‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hn (Real.exp_pos _).le
      _ = 2 * Real.sqrt a0 * Real.exp (-(1 / (16 * a0)) * ‖z‖ ^ 2) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          field_simp; ring
  calc |z i| / (2 * a) * sa16r_g d a z
      ≤ (‖z‖ / a0) * ((2 * Real.pi * a0) ^ (-((d : ℝ) / 2)) * Real.exp (-(1 / (8 * a0)) * ‖z‖ ^ 2)) :=
        mul_le_mul h1 hg hgpos.le (by positivity)
    _ = (1 / a0) * ((2 * Real.pi * a0) ^ (-((d : ℝ) / 2)) *
          (‖z‖ * Real.exp (-(1 / (8 * a0)) * ‖z‖ ^ 2))) := by ring
    _ ≤ (1 / a0) * ((2 * Real.pi * a0) ^ (-((d : ℝ) / 2)) *
          (2 * Real.sqrt a0 * Real.exp (-(1 / (16 * a0)) * ‖z‖ ^ 2))) := by gcongr
    _ = _ := by ring

lemma sa16r_dg_L1_cont {a0 : ℝ} (ha0 : 0 < a0) (i : Fin d) :
    Tendsto (fun a : ℝ => ∫⁻ z : Euc d, ‖sa16r_dg d a i z - sa16r_dg d a0 i z‖ₑ) (𝓝 a0) (𝓝 0) := by
  set D : Euc d → ℝ := fun z => 2 * ((1 / a0) * (2 * Real.sqrt a0) * ((2 * Real.pi * a0) ^ (-((d : ℝ) / 2)) *
      Real.exp (-(1 / (16 * a0)) * ‖z‖ ^ 2))) with hD
  have hDint : Integrable D := by
    have := (sa16r_gauss_int (d := d) (b := 1 / (16 * a0)) (by positivity)).const_mul
      ((2 * Real.pi * a0) ^ (-((d : ℝ) / 2)))
    exact (this.const_mul ((1 / a0) * (2 * Real.sqrt a0))).const_mul 2
  have hbd : ∀ᶠ a in 𝓝 a0, ∀ᵐ z ∂(volume : Measure (Euc d)), ‖sa16r_dg d a i z - sa16r_dg d a0 i z‖ₑ ≤
      ENNReal.ofReal (D z) := by
    have hnear : ∀ᶠ a in 𝓝 a0, a0 / 2 ≤ a ∧ a ≤ 2 * a0 := by
      filter_upwards [Icc_mem_nhds (show a0 / 2 < a0 by linarith) (show a0 < 2 * a0 by linarith)] with a h
      exact h
    filter_upwards [hnear] with a ha
    refine Eventually.of_forall fun z => ?_
    rw [← ofReal_norm]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := sa16r_dg_dom ha0 ha.1 ha.2 i z
    have h2 := sa16r_dg_dom ha0 (by linarith) (by linarith) i z (a := a0)
    rw [Real.norm_eq_abs]
    refine (abs_sub _ _).trans ?_
    simp only [hD]
    linarith
  have hmeas : ∀ᶠ a in 𝓝 a0, Measurable (fun z : Euc d => ‖sa16r_dg d a i z - sa16r_dg d a0 i z‖ₑ) :=
    Eventually.of_forall fun a => ((sa16r_dg_cont a i).measurable.sub (sa16r_dg_cont a0 i).measurable).enorm
  have hfin : ∫⁻ z, ENNReal.ofReal (D z) ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hDint (Eventually.of_forall fun z => by
      simp only [hD]; positivity)]
    exact ENNReal.ofReal_ne_top
  have hlim : ∀ᵐ z ∂(volume : Measure (Euc d)),
      Tendsto (fun a : ℝ => ‖sa16r_dg d a i z - sa16r_dg d a0 i z‖ₑ) (𝓝 a0) (𝓝 0) := by
    refine Eventually.of_forall fun z => ?_
    have := ((sa16r_dg_cont_a ha0 i z).tendsto.sub_const (sa16r_dg d a0 i z)).enorm
    simpa using this
  have := tendsto_lintegral_filter_of_dominated_convergence (μ := volume) (l := 𝓝 a0)
    (F := fun a z => ‖sa16r_dg d a i z - sa16r_dg d a0 i z‖ₑ) (f := fun _ => (0 : ℝ≥0∞))
    (fun z => ENNReal.ofReal (D z)) hmeas hbd hfin hlim
  simpa using this

end Heat11

end HRS.Whole.AppendixA.Phase2SA16R
