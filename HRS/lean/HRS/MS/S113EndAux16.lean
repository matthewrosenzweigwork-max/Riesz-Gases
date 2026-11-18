import HRS.MS.S113EndAux15

/-!
# S11.3 endpoint (worker S11X), part 16: time derivatives of the potential `g * ρ_τ` and of `∬ g dμ_τ dμ_τ`

Gaussian family `S113XGauss`: `ρ_τ`, `D_τ = ∂_τ ρ_τ` Gaussian-bounded uniformly in `τ > 0`.  Then (dominated differentiation)
* `s113x_conv_bound`: `|∫ g(z) φ(x - z) dz| ≤ B (A₀ + A₁ ‖x‖)` for `|φ| ≤ B e^{-c‖·‖²}`;
* `s113x_Gamma_hasDerivAt`: `∂_τ (g * ρ_τ)(x) = (g * D_τ)(x)`;
* `s113x_A_hasDerivAt`: `∂_τ ∫ ρ_τ (g * ρ_τ) = ∫ D_τ (g * ρ_τ) + ∫ ρ_τ (g * D_τ)`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113BD

open HRS HRS.Whole

variable {d : ℕ}

theorem s113x_convMeasure_eq {ρ : Euc d → ℝ} (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (g : Euc d → ℝ) (x : Euc d) :
    HRS.Whole.convMeasure g (HRS.Whole.withDensityReal ρ) x = ∫ z, g z * ρ (x - z) := by
  unfold HRS.Whole.convMeasure
  rw [HRS.MP.RdRem.mrr_integral_withDensityReal ρ hρm hρ0]
  rw [← integral_sub_left_eq_self (fun y => ρ y * g (x - y)) volume x]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only [sub_sub_cancel]
  ring

section Bound

variable {s : ℝ}

theorem s113x_conv_dom (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {c : ℝ} (hc : 0 < c) :
    ∃ A0 A1 : ℝ, 0 ≤ A0 ∧ 0 ≤ A1 ∧ AEStronglyMeasurable (rieszKernel d s) volume ∧ ∀ x : Euc d,
      ∃ Ψ : Euc d → ℝ, Integrable Ψ ∧ ∫ z, Ψ z = A0 + A1 * ‖x‖ ∧
        ∀ᵐ z : Euc d, ∀ (B : ℝ) (φ : Euc d → ℝ), 0 ≤ B → (∀ y, |φ y| ≤ B * Real.exp (-c * ‖y‖ ^ 2)) →
          ‖rieszKernel d s z * φ (x - z)‖ ≤ B * Ψ z := by
  have hdR : (-(d : ℝ)) < -movtr_sp s := by
    have := movtr_sp_lt (d := d) hsd hd
    linarith
  have hI1 := movtr_integrable_rpow_gauss (d := d) hd (α := -movtr_sp s) hdR hc
  have hG0 := movtr_integrable_rpow_gauss (d := d) hd (α := 0) (c := c) (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith) hc
  have hG1 := movtr_integrable_rpow_gauss (d := d) hd (α := 1) (c := c) (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith) hc
  simp only [Real.rpow_zero, one_mul, Real.rpow_one] at hG0 hG1
  set I1 : ℝ := ∫ z : Euc d, ‖z‖ ^ (-movtr_sp s) * Real.exp (-c * ‖z‖ ^ 2) with hI1d
  set G0 : ℝ := ∫ z : Euc d, Real.exp (-c * ‖z‖ ^ 2) with hG0d
  set G1 : ℝ := ∫ z : Euc d, ‖z‖ * Real.exp (-c * ‖z‖ ^ 2) with hG1d
  have hI1nn : 0 ≤ I1 := integral_nonneg fun z => mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.exp_pos _).le
  have hG0nn : 0 ≤ G0 := integral_nonneg fun z => (Real.exp_pos _).le
  have hG1nn : 0 ≤ G1 := integral_nonneg fun z => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  obtain ⟨hgm, hgb, -⟩ := HRS.MS.MovForce.mv1_g_data (d := d) hd hs0 hsd hc
  refine ⟨2 * Real.exp c * I1 + 3 * G0 + G1, G0, by positivity, hG0nn, hgm, fun x => ?_⟩
  -- the dominating function
  set Ψ : Euc d → ℝ := fun z => 2 * Real.exp c * (‖z‖ ^ (-movtr_sp s) * Real.exp (-c * ‖z‖ ^ 2)) +
    (3 + ‖x‖) * Real.exp (-c * ‖x - z‖ ^ 2) + ‖x - z‖ * Real.exp (-c * ‖x - z‖ ^ 2) with hΨ
  have hw1 : Integrable (fun z : Euc d => Real.exp (-c * ‖x - z‖ ^ 2)) := by
    have := (hG0.comp_sub_left x)
    exact this
  have hw2 : Integrable (fun z : Euc d => ‖x - z‖ * Real.exp (-c * ‖x - z‖ ^ 2)) := hG1.comp_sub_left x
  have hΨi : Integrable Ψ := ((hI1.const_mul (2 * Real.exp c)).add (hw1.const_mul (3 + ‖x‖))).add hw2
  -- pointwise domination
  have hpt : ∀ z : Euc d, (2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1) * Real.exp (-c * ‖x - z‖ ^ 2) ≤ Ψ z := by
    intro z
    have hw : Real.exp (-c * ‖x - z‖ ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg ‖x - z‖]
    have hw0 : 0 < Real.exp (-c * ‖x - z‖ ^ 2) := Real.exp_pos _
    have hzn : ‖z‖ ≤ ‖x‖ + ‖x - z‖ := by
      calc ‖z‖ = ‖x - (x - z)‖ := by simp
        _ ≤ ‖x‖ + ‖x - z‖ := norm_sub_le _ _
    have hrp : 0 ≤ ‖z‖ ^ (-movtr_sp s) := Real.rpow_nonneg (norm_nonneg _) _
    have hrz : ‖z‖ ^ (-movtr_sp s) ≤ Real.exp c * (‖z‖ ^ (-movtr_sp s) * Real.exp (-c * ‖z‖ ^ 2)) + 1 := by
      by_cases hz1 : ‖z‖ ≤ 1
      · have : 1 ≤ Real.exp c * Real.exp (-c * ‖z‖ ^ 2) := by
          rw [← Real.exp_add]
          apply Real.one_le_exp
          have : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
          nlinarith
        calc ‖z‖ ^ (-movtr_sp s) = ‖z‖ ^ (-movtr_sp s) * 1 := by ring
          _ ≤ ‖z‖ ^ (-movtr_sp s) * (Real.exp c * Real.exp (-c * ‖z‖ ^ 2)) := mul_le_mul_of_nonneg_left this hrp
          _ ≤ _ := by nlinarith
      · push_neg at hz1
        have hsp : 0 ≤ movtr_sp s := by unfold movtr_sp; split_ifs <;> linarith
        have : ‖z‖ ^ (-movtr_sp s) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hz1.le (by linarith)
        have h2 : 0 ≤ Real.exp c * (‖z‖ ^ (-movtr_sp s) * Real.exp (-c * ‖z‖ ^ 2)) :=
          mul_nonneg (Real.exp_pos _).le (mul_nonneg hrp (Real.exp_pos _).le)
        linarith
    simp only [hΨ]
    have hexp_le : 2 * ‖z‖ ^ (-movtr_sp s) * Real.exp (-c * ‖x - z‖ ^ 2) ≤
        2 * (Real.exp c * (‖z‖ ^ (-movtr_sp s) * Real.exp (-c * ‖z‖ ^ 2))) + 2 * Real.exp (-c * ‖x - z‖ ^ 2) := by
      have := mul_le_mul_of_nonneg_right hrz hw0.le
      have h3 : Real.exp c * (‖z‖ ^ (-movtr_sp s) * Real.exp (-c * ‖z‖ ^ 2)) * Real.exp (-c * ‖x - z‖ ^ 2) ≤
          Real.exp c * (‖z‖ ^ (-movtr_sp s) * Real.exp (-c * ‖z‖ ^ 2)) := by
        have h2 : 0 ≤ Real.exp c * (‖z‖ ^ (-movtr_sp s) * Real.exp (-c * ‖z‖ ^ 2)) :=
          mul_nonneg (Real.exp_pos _).le (mul_nonneg hrp (Real.exp_pos _).le)
        exact mul_le_of_le_one_right h2 hw
      nlinarith
    have hlin : (‖z‖ + 1) * Real.exp (-c * ‖x - z‖ ^ 2) ≤
        (1 + ‖x‖) * Real.exp (-c * ‖x - z‖ ^ 2) + ‖x - z‖ * Real.exp (-c * ‖x - z‖ ^ 2) := by
      nlinarith
    nlinarith
  refine ⟨Ψ, hΨi, ?_, ?_⟩
  · have e1 : ∫ z : Euc d, Real.exp (-c * ‖x - z‖ ^ 2) = G0 := integral_sub_left_eq_self (fun z : Euc d => Real.exp (-c * ‖z‖ ^ 2)) volume x
    have e2 : ∫ z : Euc d, ‖x - z‖ * Real.exp (-c * ‖x - z‖ ^ 2) = G1 := integral_sub_left_eq_self (fun z : Euc d => ‖z‖ * Real.exp (-c * ‖z‖ ^ 2)) volume x
    simp only [hΨ]
    have hA : Integrable (fun z : Euc d => 2 * Real.exp c * (‖z‖ ^ (-movtr_sp s) * Real.exp (-c * ‖z‖ ^ 2))) :=
      hI1.const_mul _
    have hB1 : Integrable (fun z : Euc d => (3 + ‖x‖) * Real.exp (-c * ‖x - z‖ ^ 2)) := hw1.const_mul _
    have hAB : Integrable (fun z : Euc d => 2 * Real.exp c * (‖z‖ ^ (-movtr_sp s) * Real.exp (-c * ‖z‖ ^ 2)) +
        (3 + ‖x‖) * Real.exp (-c * ‖x - z‖ ^ 2)) := hA.add hB1
    rw [integral_add hAB hw2, integral_add hA hB1, integral_const_mul, integral_const_mul, e1, e2]
    ring
  · filter_upwards [hgb] with z hz B φ hB hφ
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |rieszKernel d s z| * |φ (x - z)| ≤ (2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1) * (B * Real.exp (-c * ‖x - z‖ ^ 2)) :=
          mul_le_mul hz (hφ _) (abs_nonneg _) (by positivity)
      _ = B * ((2 * ‖z‖ ^ (-movtr_sp s) + ‖z‖ + 1) * Real.exp (-c * ‖x - z‖ ^ 2)) := by ring
      _ ≤ B * Ψ z := mul_le_mul_of_nonneg_left (hpt z) hB

theorem s113x_conv_bound (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {c : ℝ} (hc : 0 < c) :
    ∃ A0 A1 : ℝ, 0 ≤ A0 ∧ 0 ≤ A1 ∧ ∀ (B : ℝ) (φ : Euc d → ℝ), 0 ≤ B → Continuous φ →
      (∀ y, |φ y| ≤ B * Real.exp (-c * ‖y‖ ^ 2)) → ∀ x : Euc d,
      Integrable (fun z => rieszKernel d s z * φ (x - z)) ∧
        |∫ z, rieszKernel d s z * φ (x - z)| ≤ B * (A0 + A1 * ‖x‖) := by
  obtain ⟨A0, A1, hA0, hA1, hgm, hΨ⟩ := s113x_conv_dom hd hs0 hsd hc
  refine ⟨A0, A1, hA0, hA1, fun B φ hB hφc hφ x => ?_⟩
  obtain ⟨Ψ, hΨi, hΨint, hdom⟩ := hΨ x
  have hmeas : AEStronglyMeasurable (fun z => rieszKernel d s z * φ (x - z)) volume :=
    hgm.mul (hφc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hdom' : ∀ᵐ z : Euc d, ‖rieszKernel d s z * φ (x - z)‖ ≤ B * Ψ z := by
    filter_upwards [hdom] with z hz using hz B φ hB hφ
  have hint : Integrable (fun z => rieszKernel d s z * φ (x - z)) := (hΨi.const_mul B).mono' hmeas hdom'
  refine ⟨hint, ?_⟩
  have h1 : |∫ z, rieszKernel d s z * φ (x - z)| ≤ ∫ z, B * Ψ z := by
    rw [← Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le (hΨi.const_mul B) hdom'
  refine h1.trans (le_of_eq ?_)
  rw [integral_const_mul, hΨint]

end Bound

section Time

/-- The Gaussian family: `ρ_τ` and `D_τ = ∂_τ ρ_τ` are continuous, `ρ_τ ≥ 0`, and uniformly Gaussian-bounded for `τ > 0`. -/
structure S113XGauss (ρ D : ℝ → Euc d → ℝ) (c B : ℝ) : Prop where
  hc : 0 < c
  hB : 0 ≤ B
  rho_nn : ∀ t, 0 < t → ∀ y, 0 ≤ ρ t y
  rho_cont : ∀ t, 0 < t → Continuous (ρ t)
  D_cont : ∀ t, 0 < t → Continuous (D t)
  rho_le : ∀ t, 0 < t → ∀ y, |ρ t y| ≤ B * Real.exp (-c * ‖y‖ ^ 2)
  D_le : ∀ t, 0 < t → ∀ y, |D t y| ≤ B * Real.exp (-c * ‖y‖ ^ 2)
  deriv : ∀ t, 0 < t → ∀ y, HasDerivAt (fun τ => ρ τ y) (D t y) t

variable {s : ℝ}

theorem s113x_ball_pos {t : ℝ} (ht : 0 < t) {τ : ℝ} (hτ : τ ∈ Metric.ball t (t / 2)) : 0 < τ := by
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hτ
  linarith [hτ.1]

theorem s113x_Gamma_hasDerivAt (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ρ D : ℝ → Euc d → ℝ} {c B : ℝ}
    (H : S113XGauss ρ D c B) {t : ℝ} (ht : 0 < t) (x : Euc d) :
    HasDerivAt (fun τ => ∫ z, rieszKernel d s z * ρ τ (x - z)) (∫ z, rieszKernel d s z * D t (x - z)) t := by
  obtain ⟨A0, A1, hA0, hA1, hgm, hΨ⟩ := s113x_conv_dom hd hs0 hsd H.hc
  obtain ⟨Ψ, hΨi, -, hdom⟩ := hΨ x
  obtain ⟨A0', A1', hA0', hA1', hbd⟩ := s113x_conv_bound hd hs0 hsd (s := s) H.hc
  have hball : Metric.ball t (t / 2) ∈ 𝓝 t := Metric.ball_mem_nhds t (by positivity)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun τ z => rieszKernel d s z * ρ τ (x - z)) (F' := fun τ z => rieszKernel d s z * D τ (x - z))
    (bound := fun z => B * Ψ z) hball ?_ ?_ ?_ ?_ (hΨi.const_mul B) ?_).2
  · filter_upwards [hball] with τ hτ
    exact (hbd B (ρ τ) H.hB (H.rho_cont τ (s113x_ball_pos ht hτ)) (H.rho_le τ (s113x_ball_pos ht hτ)) x).1.aestronglyMeasurable
  · exact (hbd B (ρ t) H.hB (H.rho_cont t ht) (H.rho_le t ht) x).1
  · exact (hbd B (D t) H.hB (H.D_cont t ht) (H.D_le t ht) x).1.aestronglyMeasurable
  · filter_upwards [hdom] with z hz τ hτ
    exact hz B (D τ) H.hB (H.D_le τ (s113x_ball_pos ht hτ))
  · refine Filter.Eventually.of_forall fun z τ hτ => ?_
    exact (H.deriv τ (s113x_ball_pos ht hτ) (x - z)).const_mul (rieszKernel d s z)

theorem s113x_Gamma_continuous (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {φ : Euc d → ℝ} {c B : ℝ} (hc : 0 < c)
    (hB : 0 ≤ B) (hφc : Continuous φ) (hφ : ∀ y, |φ y| ≤ B * Real.exp (-c * ‖y‖ ^ 2)) :
    Continuous (fun x => ∫ z, rieszKernel d s z * φ (x - z)) := by
  obtain ⟨hgm, hgb, hBint⟩ := HRS.MS.MovForce.mv1_g_data (d := d) hd hs0 hsd hc
  exact HRS.MS.MovForce.mv1_continuous_conv hc hgm hgb hBint hB hφc hφ

theorem s113x_poly_gauss_integrable (hd : 1 ≤ d) {c : ℝ} (hc : 0 < c) (A0 A1 : ℝ) :
    Integrable (fun x : Euc d => (A0 + A1 * ‖x‖) * Real.exp (-c * ‖x‖ ^ 2)) := by
  have h1d : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have h0 := movtr_integrable_rpow_gauss (d := d) hd (α := 0) (c := c) (by linarith) hc
  have h1 := movtr_integrable_rpow_gauss (d := d) hd (α := 1) (c := c) (by linarith) hc
  simp only [Real.rpow_zero, one_mul, Real.rpow_one] at h0 h1
  refine ((h0.const_mul A0).add (h1.const_mul A1)).congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply]
  ring

theorem s113x_A_hasDerivAt (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ρ D : ℝ → Euc d → ℝ} {c B : ℝ}
    (H : S113XGauss ρ D c B) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun τ => ∫ x, ρ τ x * ∫ z, rieszKernel d s z * ρ τ (x - z))
      (∫ x, (D t x * (∫ z, rieszKernel d s z * ρ t (x - z)) + ρ t x * ∫ z, rieszKernel d s z * D t (x - z))) t := by
  obtain ⟨A0, A1, hA0, hA1, hbd⟩ := s113x_conv_bound hd hs0 hsd (s := s) H.hc
  have hB0 : 0 ≤ B := H.hB
  have hball : Metric.ball t (t / 2) ∈ 𝓝 t := Metric.ball_mem_nhds t (by positivity)
  have hGp : ∀ τ, 0 < τ → Continuous (fun x => ∫ z, rieszKernel d s z * ρ τ (x - z)) := fun τ hτ =>
    s113x_Gamma_continuous hd hs0 hsd H.hc H.hB (H.rho_cont τ hτ) (H.rho_le τ hτ)
  have hGD : ∀ τ, 0 < τ → Continuous (fun x => ∫ z, rieszKernel d s z * D τ (x - z)) := fun τ hτ =>
    s113x_Gamma_continuous hd hs0 hsd H.hc H.hB (H.D_cont τ hτ) (H.D_le τ hτ)
  have hGb : ∀ τ, 0 < τ → ∀ x, |∫ z, rieszKernel d s z * ρ τ (x - z)| ≤ B * (A0 + A1 * ‖x‖) := fun τ hτ x =>
    (hbd B (ρ τ) H.hB (H.rho_cont τ hτ) (H.rho_le τ hτ) x).2
  have hGDb : ∀ τ, 0 < τ → ∀ x, |∫ z, rieszKernel d s z * D τ (x - z)| ≤ B * (A0 + A1 * ‖x‖) := fun τ hτ x =>
    (hbd B (D τ) H.hB (H.D_cont τ hτ) (H.D_le τ hτ) x).2
  set bd : Euc d → ℝ := fun x => 2 * B * B * ((A0 + A1 * ‖x‖) * Real.exp (-c * ‖x‖ ^ 2)) with hbdd
  have hbdi : Integrable bd := (s113x_poly_gauss_integrable hd H.hc A0 A1).const_mul (2 * B * B)
  have hnn : ∀ x : Euc d, 0 ≤ A0 + A1 * ‖x‖ := fun x => by positivity
  have hF'b : ∀ τ, 0 < τ → ∀ x : Euc d, ‖D τ x * (∫ z, rieszKernel d s z * ρ τ (x - z)) +
      ρ τ x * ∫ z, rieszKernel d s z * D τ (x - z)‖ ≤ bd x := by
    intro τ hτ x
    have h1 : ‖D τ x * (∫ z, rieszKernel d s z * ρ τ (x - z))‖ ≤ B * Real.exp (-c * ‖x‖ ^ 2) * (B * (A0 + A1 * ‖x‖)) := by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul (H.D_le τ hτ x) (hGb τ hτ x) (abs_nonneg _) (by positivity)
    have h2 : ‖ρ τ x * ∫ z, rieszKernel d s z * D τ (x - z)‖ ≤ B * Real.exp (-c * ‖x‖ ^ 2) * (B * (A0 + A1 * ‖x‖)) := by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul (H.rho_le τ hτ x) (hGDb τ hτ x) (abs_nonneg _) (by positivity)
    refine (norm_add_le _ _).trans ?_
    simp only [hbdd]
    nlinarith
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (F := fun τ x => ρ τ x * ∫ z, rieszKernel d s z * ρ τ (x - z))
    (F' := fun τ x => D τ x * (∫ z, rieszKernel d s z * ρ τ (x - z)) + ρ τ x * ∫ z, rieszKernel d s z * D τ (x - z))
    (bound := bd) hball ?_ ?_ ?_ ?_ hbdi ?_).2
  · filter_upwards [hball] with τ hτ
    exact ((H.rho_cont τ (s113x_ball_pos ht hτ)).mul (hGp τ (s113x_ball_pos ht hτ))).aestronglyMeasurable
  · refine hbdi.mono' ((H.rho_cont t ht).mul (hGp t ht)).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    calc |ρ t x| * |∫ z, rieszKernel d s z * ρ t (x - z)| ≤ B * Real.exp (-c * ‖x‖ ^ 2) * (B * (A0 + A1 * ‖x‖)) :=
          mul_le_mul (H.rho_le t ht x) (hGb t ht x) (abs_nonneg _) (by positivity)
      _ ≤ bd x := by
          simp only [hbdd]
          have : 0 ≤ B * B * ((A0 + A1 * ‖x‖) * Real.exp (-c * ‖x‖ ^ 2)) := by positivity
          nlinarith
  · exact (((H.D_cont t ht).mul (hGp t ht)).add ((H.rho_cont t ht).mul (hGD t ht))).aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun x τ hτ => hF'b τ (s113x_ball_pos ht hτ) x
  · refine Filter.Eventually.of_forall fun x τ hτ => ?_
    exact (H.deriv τ (s113x_ball_pos ht hτ) x).mul (s113x_Gamma_hasDerivAt hd hs0 hsd H (s113x_ball_pos ht hτ) x)

end Time

end HRS.MS.S113BD

end
