import HRS.MS.SA12NN2F
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# S.A.12 N2 (SA12N), part G: integration by parts in frequency space against a Lipschitz symbol

For a symbol `m` that is `C¹` off the origin, vanishes linearly at `0`, has bounded `∂_l m`, and
`C¹` functions `F₁, F₂ : ℝ^d → ℂ` with the displayed integrability:
`‖∫ m (∂_l F₁ · conj F₂ + F₁ · conj ∂_l F₂)‖ ≤ Λ ∫ ‖F₁ conj F₂‖`.
Proof: integrate by parts against `m Φ_ε` (the bump of `UniqN1a`) and let `ε → 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff ComplexConjugate

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.MS.UniqN1a

variable {d : ℕ}

theorem sa12n_hasFDerivAt_conj {F : Euc d → ℂ} {F' : Euc d →L[ℝ] ℂ} {ξ : Euc d}
    (h : HasFDerivAt F F' ξ) :
    HasFDerivAt (fun ξ => conj (F ξ)) (Complex.conjCLE.toContinuousLinearMap.comp F') ξ :=
  Complex.conjCLE.hasFDerivAt.comp ξ h

theorem sa12n_hasFDerivAt_ofReal {f : Euc d → ℝ} {f' : Euc d →L[ℝ] ℝ} {ξ : Euc d}
    (h : HasFDerivAt f f' ξ) :
    HasFDerivAt (fun ξ => ((f ξ : ℝ) : ℂ)) (Complex.ofRealCLM.comp f') ξ :=
  Complex.ofRealCLM.hasFDerivAt.comp ξ h

/-- Derivative of the cut-off symbol `m Φ_ε`. -/
theorem sa12n_cut_symbol {m : Euc d → ℝ} (hmd : ∀ ξ : Euc d, ξ ≠ 0 → DifferentiableAt ℝ m ξ)
    {ε : ℝ} (hε : 0 < ε) (ξ : Euc d) :
    DifferentiableAt ℝ (fun ξ => m ξ * n1aΦ ε ξ) ξ := by
  by_cases hξ : ‖ξ‖ < ε
  · have hev : (fun ξ => m ξ * n1aΦ ε ξ) =ᶠ[𝓝 ξ] fun _ => 0 := by
      filter_upwards [isOpen_lt continuous_norm continuous_const |>.mem_nhds hξ] with w hw
      rw [n1aΦ_zero hε (le_of_lt hw), mul_zero]
    exact (differentiableAt_const (0 : ℝ)).congr_of_eventuallyEq hev
  · have hξ0 : ξ ≠ 0 := by
      intro h; rw [h, norm_zero] at hξ; exact hξ hε
    exact (hmd ξ hξ0).mul ((((n1aΦ_contDiff (d := d) ε).of_le (by exact_mod_cast le_top)).differentiable
      one_ne_zero) ξ)

theorem sa12n_fderiv_W {F1 F2 : Euc d → ℂ} (hF1 : Differentiable ℝ F1) (hF2 : Differentiable ℝ F2)
    (ξ e : Euc d) :
    DifferentiableAt ℝ (fun ξ => F1 ξ * conj (F2 ξ)) ξ ∧
      fderiv ℝ (fun ξ => F1 ξ * conj (F2 ξ)) ξ e =
        fderiv ℝ F1 ξ e * conj (F2 ξ) + F1 ξ * conj (fderiv ℝ F2 ξ e) := by
  have h1 := (hF1 ξ).hasFDerivAt
  have h2 := sa12n_hasFDerivAt_conj (hF2 ξ).hasFDerivAt
  have h3 := h1.fun_mul h2
  refine ⟨h3.differentiableAt, ?_⟩
  rw [h3.fderiv]
  simp [mul_comm, add_comm]

theorem sa12n_freq_ibp (hd : 1 ≤ d) (l : Fin d) {m : Euc d → ℝ} {Λ M0 : ℝ} (hΛ : 0 ≤ Λ)
    (hM0 : 0 ≤ M0) (hmm : Continuous m)
    (hmd : ∀ ξ : Euc d, ξ ≠ 0 → DifferentiableAt ℝ m ξ)
    (hmb : ∀ ξ : Euc d, ξ ≠ 0 → |fderiv ℝ m ξ (EuclideanSpace.single l 1)| ≤ Λ)
    (hm0 : ∀ ξ : Euc d, |m ξ| ≤ M0 * ‖ξ‖)
    {F1 F2 : Euc d → ℂ} (hF1 : Differentiable ℝ F1) (hF2 : Differentiable ℝ F2)
    (hI1 : Integrable (fun ξ => (m ξ : ℂ) * (fderiv ℝ F1 ξ (EuclideanSpace.single l 1) *
      conj (F2 ξ))) volume)
    (hI2 : Integrable (fun ξ => (m ξ : ℂ) * (F1 ξ *
      conj (fderiv ℝ F2 ξ (EuclideanSpace.single l 1)))) volume)
    (hI3 : Integrable (fun ξ => (m ξ : ℂ) * (F1 ξ * conj (F2 ξ))) volume)
    (hI4 : Integrable (fun ξ => F1 ξ * conj (F2 ξ)) volume) :
    ‖∫ ξ, (m ξ : ℂ) * (fderiv ℝ F1 ξ (EuclideanSpace.single l 1) * conj (F2 ξ) +
        F1 ξ * conj (fderiv ℝ F2 ξ (EuclideanSpace.single l 1)))‖ ≤
      Λ * ∫ ξ, ‖F1 ξ * conj (F2 ξ)‖ := by
  set e : Euc d := EuclideanSpace.single l (1 : ℝ) with he
  set W : Euc d → ℂ := fun ξ => F1 ξ * conj (F2 ξ) with hW
  have hWc : Continuous W := hF1.continuous.mul (Complex.continuous_conj.comp hF2.continuous)
  have hWd : ∀ ξ, DifferentiableAt ℝ W ξ ∧ fderiv ℝ W ξ e =
      fderiv ℝ F1 ξ e * conj (F2 ξ) + F1 ξ * conj (fderiv ℝ F2 ξ e) := fun ξ =>
    sa12n_fderiv_W hF1 hF2 ξ e
  have hfmeas : AEStronglyMeasurable (fun ξ => fderiv ℝ W ξ e) volume :=
    (measurable_fderiv_apply_const ℝ W e).aestronglyMeasurable
  obtain ⟨Lb, hLb0, hLb⟩ := n1a_bump_fderiv_bound (d := d)
  set Λ' : ℝ := Λ + 2 * M0 * Lb with hΛ'
  have hΛ'0 : 0 ≤ Λ' := by positivity
  -- derivative bound of the cut-off symbol
  have hderiv : ∀ ε : ℝ, 0 < ε → ∀ ξ : Euc d,
      |fderiv ℝ (fun ξ => m ξ * n1aΦ ε ξ) ξ e| ≤ Λ' := by
    intro ε hε ξ
    by_cases hξ : ‖ξ‖ < ε
    · have hev : (fun ξ => m ξ * n1aΦ ε ξ) =ᶠ[𝓝 ξ] fun _ => 0 := by
        filter_upwards [isOpen_lt continuous_norm continuous_const |>.mem_nhds hξ] with w hw
        rw [n1aΦ_zero hε (le_of_lt hw), mul_zero]
      rw [hev.fderiv_eq]
      simpa using hΛ'0
    · have hξ0 : ξ ≠ 0 := by
        intro h; rw [h, norm_zero] at hξ; exact hξ hε
      have hΦd : DifferentiableAt ℝ (n1aΦ (d := d) ε) ξ :=
        ((n1aΦ_contDiff (d := d) ε).of_le (by exact_mod_cast le_top)).differentiable one_ne_zero ξ
      rw [fderiv_fun_mul (hmd ξ hξ0) hΦd]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      have h1 : |m ξ * fderiv ℝ (n1aΦ ε) ξ e| ≤ 2 * M0 * Lb := by
        by_cases h2 : 2 * ε < ‖ξ‖
        · rw [n1aΦ_fderiv_zero_out hε h2]
          simp only [ContinuousLinearMap.zero_apply, mul_zero, abs_zero]
          positivity
        · have h2' : ‖ξ‖ ≤ 2 * ε := not_lt.1 h2
          have hD : |fderiv ℝ (n1aΦ ε) ξ e| ≤ Lb * ε⁻¹ := by
            rw [← Real.norm_eq_abs]
            refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
            have := n1aΦ_fderiv_bound hLb hε ξ
            simpa [he] using this
          rw [abs_mul]
          calc |m ξ| * |fderiv ℝ (n1aΦ ε) ξ e| ≤ (M0 * (2 * ε)) * (Lb * ε⁻¹) := by
                refine mul_le_mul ?_ hD (abs_nonneg _) (by positivity)
                exact (hm0 ξ).trans (mul_le_mul_of_nonneg_left h2' hM0)
            _ = 2 * M0 * Lb := by field_simp
      have h3 : |n1aΦ ε ξ * fderiv ℝ m ξ e| ≤ Λ := by
        rw [abs_mul, abs_of_nonneg (n1aΦ_nonneg ε ξ)]
        calc n1aΦ ε ξ * |fderiv ℝ m ξ e| ≤ 1 * Λ :=
              mul_le_mul (n1aΦ_le_one ε ξ) (hmb ξ hξ0) (abs_nonneg _) zero_le_one
          _ = Λ := one_mul Λ
      calc |m ξ * fderiv ℝ (n1aΦ ε) ξ e + n1aΦ ε ξ * fderiv ℝ m ξ e|
          ≤ |m ξ * fderiv ℝ (n1aΦ ε) ξ e| + |n1aΦ ε ξ * fderiv ℝ m ξ e| := abs_add_le _ _
        _ ≤ Λ' := by rw [hΛ']; linarith
  -- the integration by parts for each fixed ε
  have hΦc : ∀ ε : ℝ, Continuous (n1aΦ (d := d) ε) := fun ε => (n1aΦ_contDiff (d := d) ε).continuous
  have hfc : ∀ ε : ℝ, Continuous (fun ξ => ((m ξ * n1aΦ ε ξ : ℝ) : ℂ)) := fun ε =>
    Complex.continuous_ofReal.comp (hmm.mul (hΦc ε))
  have hfd : ∀ ε : ℝ, 0 < ε → ∀ ξ : Euc d,
      HasFDerivAt (fun ξ => ((m ξ * n1aΦ ε ξ : ℝ) : ℂ))
        (Complex.ofRealCLM.comp (fderiv ℝ (fun ξ => m ξ * n1aΦ ε ξ) ξ)) ξ := fun ε hε ξ =>
    sa12n_hasFDerivAt_ofReal (sa12n_cut_symbol hmd hε ξ).hasFDerivAt
  have hfde : ∀ ε : ℝ, 0 < ε → ∀ ξ : Euc d,
      fderiv ℝ (fun ξ => ((m ξ * n1aΦ ε ξ : ℝ) : ℂ)) ξ e =
        ((fderiv ℝ (fun ξ => m ξ * n1aΦ ε ξ) ξ e : ℝ) : ℂ) := by
    intro ε hε ξ
    rw [(hfd ε hε ξ).fderiv]
    simp
  have hsum : Integrable (fun ξ => (m ξ : ℂ) * fderiv ℝ W ξ e) volume := by
    have := hI1.add hI2
    refine this.congr (Eventually.of_forall fun ξ => ?_)
    simp only [Pi.add_apply]
    rw [(hWd ξ).2, mul_add]
  have hibp : ∀ ε : ℝ, 0 < ε →
      ∫ ξ, ((m ξ * n1aΦ ε ξ : ℝ) : ℂ) * fderiv ℝ W ξ e =
        -∫ ξ, ((fderiv ℝ (fun ξ => m ξ * n1aΦ ε ξ) ξ e : ℝ) : ℂ) * W ξ := by
    intro ε hε
    have hfe : ∀ ξ, ‖((m ξ * n1aΦ ε ξ : ℝ) : ℂ)‖ ≤ ‖(m ξ : ℂ)‖ := by
      intro ξ
      rw [Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (n1aΦ_nonneg ε ξ)]
      exact mul_le_of_le_one_right (abs_nonneg _) (n1aΦ_le_one ε ξ)
    have i1 : Integrable (fun ξ => fderiv ℝ (fun ξ => ((m ξ * n1aΦ ε ξ : ℝ) : ℂ)) ξ e * W ξ)
        volume := by
      refine (hI4.norm.const_mul Λ').mono' ?_ (Eventually.of_forall fun ξ => ?_)
      · have : (fun ξ => fderiv ℝ (fun ξ => ((m ξ * n1aΦ ε ξ : ℝ) : ℂ)) ξ e * W ξ) =
            fun ξ => ((fderiv ℝ (fun ξ => m ξ * n1aΦ ε ξ) ξ e : ℝ) : ℂ) * W ξ :=
          funext fun ξ => by rw [hfde ε hε ξ]
        rw [this]
        exact (Complex.measurable_ofReal.comp
          (measurable_fderiv_apply_const ℝ (fun ξ => m ξ * n1aΦ ε ξ) e)).aestronglyMeasurable.mul
          hWc.aestronglyMeasurable
      · rw [hfde ε hε ξ, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hderiv ε hε ξ) (norm_nonneg _)
    have i2 : Integrable (fun ξ => ((m ξ * n1aΦ ε ξ : ℝ) : ℂ) * fderiv ℝ W ξ e) volume := by
      refine hsum.norm.mono' ?_ (Eventually.of_forall fun ξ => ?_)
      · exact (hfc ε).aestronglyMeasurable.mul hfmeas
      · rw [norm_mul, norm_mul]
        exact mul_le_mul_of_nonneg_right (hfe ξ) (norm_nonneg _)
    have i3 : Integrable (fun ξ => ((m ξ * n1aΦ ε ξ : ℝ) : ℂ) * W ξ) volume := by
      refine hI3.norm.mono' ?_ (Eventually.of_forall fun ξ => ?_)
      · exact (hfc ε).aestronglyMeasurable.mul hWc.aestronglyMeasurable
      · rw [norm_mul]
        calc ‖((m ξ * n1aΦ ε ξ : ℝ) : ℂ)‖ * ‖W ξ‖ ≤ ‖(m ξ : ℂ)‖ * ‖W ξ‖ :=
              mul_le_mul_of_nonneg_right (hfe ξ) (norm_nonneg _)
          _ = ‖(m ξ : ℂ) * (F1 ξ * conj (F2 ξ))‖ := (norm_mul _ _).symm
    have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
      (f := fun ξ => ((m ξ * n1aΦ ε ξ : ℝ) : ℂ)) (g := W) (v := e) i1 i2 i3
      (fun ξ _ => (hfd ε hε ξ).differentiableAt) (fun ξ _ => (hWd ξ).1)
    simp only [hfde ε hε] at key
    exact key
  -- the limit ε → 0
  have hae := HRS.MH.Screened.k3_ae_ne hd (0 : Euc d)
  have T1 : Tendsto (fun ε : ℝ => ∫ ξ, ((m ξ * n1aΦ ε ξ : ℝ) : ℂ) * fderiv ℝ W ξ e)
      (𝓝[>] 0) (𝓝 (∫ ξ, (m ξ : ℂ) * fderiv ℝ W ξ e)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun ξ => ‖(m ξ : ℂ) * fderiv ℝ W ξ e‖)
      (Eventually.of_forall fun ε => ?_) (Eventually.of_forall fun ε => Eventually.of_forall fun ξ => ?_)
      hsum.norm ?_
    · exact (hfc ε).aestronglyMeasurable.mul hfmeas
    · rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_mul, abs_of_nonneg (n1aΦ_nonneg ε ξ)]
      exact mul_le_mul_of_nonneg_right (mul_le_of_le_one_right (abs_nonneg _) (n1aΦ_le_one ε ξ))
        (norm_nonneg _)
    · filter_upwards [hae] with ξ hξ
      have hξ' : ξ ≠ 0 := hξ
      have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ'
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < ‖ξ‖ / 2 by positivity)] with ε hε
      rw [n1aΦ_one hε.1 (by linarith [hε.2])]
      simp
  have T2 : Tendsto (fun ε : ℝ => ∫ ξ, ((fderiv ℝ (fun ξ => m ξ * n1aΦ ε ξ) ξ e : ℝ) : ℂ) * W ξ)
      (𝓝[>] 0) (𝓝 (∫ ξ, ((fderiv ℝ m ξ e : ℝ) : ℂ) * W ξ)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun ξ => Λ' * ‖W ξ‖)
      ?_ ?_ (hI4.norm.const_mul Λ') ?_
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      exact (Complex.measurable_ofReal.comp
          (measurable_fderiv_apply_const ℝ (fun ξ => m ξ * n1aΦ ε ξ) e)).aestronglyMeasurable.mul
          hWc.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      refine Eventually.of_forall fun ξ => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hderiv ε hε ξ) (norm_nonneg _)
    · filter_upwards [hae] with ξ hξ
      have hξ' : ξ ≠ 0 := hξ
      have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ'
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < ‖ξ‖ / 4 by positivity)] with ε hε
      have hev : (fun ξ => m ξ * n1aΦ ε ξ) =ᶠ[𝓝 ξ] m := by
        filter_upwards [isOpen_lt continuous_const continuous_norm |>.mem_nhds
          (show 2 * ε < ‖ξ‖ by linarith [hε.2])] with w hw
        rw [n1aΦ_one hε.1 (le_of_lt hw), mul_one]
      rw [hev.fderiv_eq]
  have T3 : Tendsto (fun ε : ℝ => ∫ ξ, ((m ξ * n1aΦ ε ξ : ℝ) : ℂ) * fderiv ℝ W ξ e)
      (𝓝[>] 0) (𝓝 (-∫ ξ, ((fderiv ℝ m ξ e : ℝ) : ℂ) * W ξ)) := by
    refine T2.neg.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hibp ε hε).symm
  have hid := tendsto_nhds_unique T1 T3
  have e1 : (fun ξ => (m ξ : ℂ) * (fderiv ℝ F1 ξ e * conj (F2 ξ) + F1 ξ * conj (fderiv ℝ F2 ξ e))) =
      fun ξ => (m ξ : ℂ) * fderiv ℝ W ξ e := funext fun ξ => by rw [(hWd ξ).2]
  rw [e1, hid, norm_neg]
  have hΛint : Integrable (fun ξ => Λ * ‖W ξ‖) volume := hI4.norm.const_mul Λ
  calc ‖∫ ξ, ((fderiv ℝ m ξ e : ℝ) : ℂ) * W ξ‖ ≤ ∫ ξ, Λ * ‖W ξ‖ := by
        refine norm_integral_le_of_norm_le hΛint ?_
        filter_upwards [hae] with ξ hξ
        have hξ' : ξ ≠ 0 := hξ
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hmb ξ hξ') (norm_nonneg _)
    _ = Λ * ∫ ξ, ‖W ξ‖ := integral_const_mul _ _

end HRS.MH.AdjointRd.Phase2SA12Near
