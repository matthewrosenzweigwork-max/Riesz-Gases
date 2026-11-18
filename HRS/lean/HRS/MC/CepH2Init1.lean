import HRS.MC.CepH2Ent4

/-!
# CEPH2, C4 (a): convolution on the cell and the Jensen bound for `u log u`
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

theorem h2_g_neg (v : ℝ) (w : Ch N) : h2_g v (-w) = h2_g v w := by
  unfold h2_g; rw [norm_neg]

theorem h2_per_neg_eq (v : ℝ) (w : Ch N) : h2_per v (-w) = h2_per v w := by
  unfold h2_per
  set F : ℤ → ℝ := fun m => h2_g v (w + (m : ℝ) • cep_diag N) with hF
  calc ∑' m : ℤ, h2_g v (-w + (m : ℝ) • cep_diag N) = ∑' m : ℤ, F (Equiv.neg ℤ m) := by
        refine tsum_congr fun m => ?_
        simp only [hF, Equiv.neg_apply, Int.cast_neg]
        rw [← h2_g_neg v (-w + (m : ℝ) • cep_diag N)]
        congr 1
        rw [neg_add, neg_neg, neg_smul, add_comm]
    _ = ∑' m : ℤ, F m := (Equiv.neg ℤ).tsum_eq F

theorem h2_lintegral_cell_per_x {v : ℝ} (hv : 0 < v) (y : Ch N) :
    ∫⁻ x in cep_cell N, ENNReal.ofReal (h2_per v (x - y)) = 1 := by
  have h0 := h2_lintegral_cell_kernel hv (F := fun _ => (1 : ℝ≥0∞)) measurable_const (fun _ => rfl) y
  simp only [mul_one] at h0
  rw [h0]
  have h1 := h2_lintegral_gauss_shift (v := v) (fun _ => (1 : ℝ≥0∞)) y
  simp only [mul_one] at h1
  rw [h1]
  have h := h2_lintegral_gauss_poly (N := N) hv 1 0 zero_le_one le_rfl
  simpa using h

theorem h2_integrableOn_cell_per_x {v : ℝ} (hv : 0 < v) (y : Ch N) :
    Integrable (fun x => h2_per v (x - y)) (volume.restrict (cep_cell N)) := by
  refine ⟨((h2_continuous_per hv).comp (continuous_id.sub continuous_const)).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => h2_per_nonneg hv _), h2_lintegral_cell_per_x hv y]
  exact ENNReal.one_lt_top

theorem h2_integral_cell_per_x {v : ℝ} (hv : 0 < v) (y : Ch N) :
    ∫ x in cep_cell N, h2_per v (x - y) = 1 := by
  have := ofReal_integral_eq_lintegral_ofReal (h2_integrableOn_cell_per_x hv y)
    (ae_of_all _ fun x => h2_per_nonneg hv _)
  rw [h2_lintegral_cell_per_x hv y] at this
  have h0 : 0 ≤ ∫ x in cep_cell N, h2_per v (x - y) :=
    setIntegral_nonneg h2_cell_measurable fun x _ => h2_per_nonneg hv _
  rwa [← ENNReal.ofReal_one, ENNReal.ofReal_eq_ofReal_iff h0 zero_le_one] at this

theorem h2_per_sub_comm (v : ℝ) (x y : Ch N) : h2_per v (x - y) = h2_per v (y - x) := by
  rw [← neg_sub, h2_per_neg_eq]

theorem h2_integrableOn_cell_per_y {v : ℝ} (hv : 0 < v) (x : Ch N) :
    Integrable (fun y => h2_per v (x - y)) (volume.restrict (cep_cell N)) := by
  simp_rw [h2_per_sub_comm v x]
  exact h2_integrableOn_cell_per_x hv x

theorem h2_integral_cell_per_y {v : ℝ} (hv : 0 < v) (x : Ch N) :
    ∫ y in cep_cell N, h2_per v (x - y) = 1 := by
  simp_rw [h2_per_sub_comm v x]
  exact h2_integral_cell_per_x hv x

theorem h2_mu_density {v : ℝ} {ρ : Ch N → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (x : Ch N) :
    h2_mu v (h2_dMeas ρ) x = ∫ y in cep_cell N, h2_per v (x - y) * ρ y := by
  unfold h2_mu h2_dMeas
  rw [integral_withDensity_eq_integral_toReal_smul (f := fun x => ENNReal.ofReal (ρ x)) (ENNReal.measurable_ofReal.comp hρ)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (hρ0 y)]
  ring

theorem h2_tangent {a m : ℝ} (ha : 0 ≤ a) (hm : 0 < m) : a * Real.log m + a - m ≤ a * Real.log a := by
  rcases ha.eq_or_lt with rfl | ha'
  · simp; linarith
  · have h := Real.log_le_sub_one_of_pos (div_pos hm ha')
    rw [Real.log_div hm.ne' ha'.ne'] at h
    have e : a * (m / a - 1) = m - a := by field_simp
    have h2 : a * (Real.log m - Real.log a) ≤ m - a := by
      rw [← e]; exact mul_le_mul_of_nonneg_left h ha'.le
    rw [mul_sub] at h2
    linarith

/-- Convolution with the kernel on the cell preserves the integral. -/
theorem h2_cell_convolve {v : ℝ} (hv : 0 < v) {f : Ch N → ℝ} (hf : Integrable f (volume.restrict (cep_cell N))) :
    ∫ x in cep_cell N, ∫ y in cep_cell N, h2_per v (x - y) * f y = ∫ y in cep_cell N, f y := by
  set μc : Measure (Ch N) := volume.restrict (cep_cell N) with hμc
  have hmeas : AEStronglyMeasurable (Function.uncurry fun x y : Ch N => h2_per v (x - y) * f y) (μc.prod μc) :=
    (((h2_continuous_per hv).comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable).mul
      (hf.aestronglyMeasurable.comp_snd)
  have hint : Integrable (Function.uncurry fun x y : Ch N => h2_per v (x - y) * f y) (μc.prod μc) := by
    refine (integrable_prod_iff' hmeas).2 ⟨Eventually.of_forall fun y => ?_, ?_⟩
    · exact (h2_integrableOn_cell_per_x hv y).mul_const (f y)
    · have e : (fun y => ∫ x, ‖(Function.uncurry fun x y : Ch N => h2_per v (x - y) * f y) (x, y)‖ ∂μc) =
          fun y => ‖f y‖ := by
        funext y
        simp only [Function.uncurry_apply_pair, norm_mul]
        rw [integral_mul_const]
        have : ∫ x, ‖h2_per v (x - y)‖ ∂μc = 1 := by
          rw [← h2_integral_cell_per_x hv y]
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          simp only [Real.norm_of_nonneg (h2_per_nonneg hv _)]
        rw [this, one_mul]
      rw [e]; exact hf.norm
  rw [integral_integral_swap hint]
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  simp only
  rw [integral_mul_const, h2_integral_cell_per_x hv y, one_mul]

/-- Pointwise Jensen / tangent-line bound for the entropy density of the mollification. -/
theorem h2_jensen_pointwise {v : ℝ} (hv : 0 < v) {ρ : Ch N → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : ∫⁻ x in cep_cell N, ENNReal.ofReal (ρ x) = 1)
    (hL : Integrable (fun y => ρ y * Real.log (ρ y)) (volume.restrict (cep_cell N))) (x : Ch N) :
    h2_mu v (h2_dMeas ρ) x * Real.log (h2_mu v (h2_dMeas ρ) x) ≤
      ∫ y in cep_cell N, h2_per v (x - y) * (ρ y * Real.log (ρ y)) := by
  haveI := h2_dMeas_prob hρ1
  have hρi := h2_integrable_of_lintegral hρ hρ0 hρ1
  set m : ℝ := h2_mu v (h2_dMeas ρ) x with hm
  have hm0 : 0 < m := h2_mu_pos hv _ x
  have hmr : m = ∫ y in cep_cell N, h2_per v (x - y) * ρ y := h2_mu_density hρ hρ0 x
  obtain ⟨B, hB0, hB⟩ := h2_per_le (N := N) hv
  have hpc : Continuous fun y => h2_per v (x - y) := (h2_continuous_per hv).comp (continuous_const.sub continuous_id)
  have i1 : Integrable (fun y => h2_per v (x - y) * ρ y) (volume.restrict (cep_cell N)) :=
    hρi.bdd_mul (c := B) hpc.aestronglyMeasurable (ae_of_all _ fun y => (hB (x - y)).1)
  have i2 : Integrable (fun y => h2_per v (x - y) * (ρ y * Real.log (ρ y))) (volume.restrict (cep_cell N)) :=
    hL.bdd_mul (c := B) hpc.aestronglyMeasurable (ae_of_all _ fun y => (hB (x - y)).1)
  have i3 := h2_integrableOn_cell_per_y hv x
  have key : ∀ y, h2_per v (x - y) * (ρ y * Real.log m + ρ y - m) ≤ h2_per v (x - y) * (ρ y * Real.log (ρ y)) :=
    fun y => mul_le_mul_of_nonneg_left (h2_tangent (hρ0 y) hm0) (h2_per_nonneg hv _)
  have iL : Integrable (fun y => h2_per v (x - y) * (ρ y * Real.log m + ρ y - m)) (volume.restrict (cep_cell N)) := by
    have : (fun y => h2_per v (x - y) * (ρ y * Real.log m + ρ y - m)) =
        fun y => Real.log m * (h2_per v (x - y) * ρ y) + h2_per v (x - y) * ρ y - m * h2_per v (x - y) := by
      funext y; ring
    rw [this]
    exact ((i1.const_mul _).add i1).sub (i3.const_mul _)
  have h := integral_mono iL i2 key
  have e : ∫ y in cep_cell N, h2_per v (x - y) * (ρ y * Real.log m + ρ y - m) = m * Real.log m := by
    have : (fun y => h2_per v (x - y) * (ρ y * Real.log m + ρ y - m)) =
        fun y => Real.log m * (h2_per v (x - y) * ρ y) + h2_per v (x - y) * ρ y - m * h2_per v (x - y) := by
      funext y; ring
    have hA : Integrable (fun y => Real.log m * (h2_per v (x - y) * ρ y) + h2_per v (x - y) * ρ y)
        (volume.restrict (cep_cell N)) := (i1.const_mul _).add i1
    have hB' : Integrable (fun y => m * h2_per v (x - y)) (volume.restrict (cep_cell N)) := i3.const_mul _
    have hC' : Integrable (fun y => Real.log m * (h2_per v (x - y) * ρ y)) (volume.restrict (cep_cell N)) :=
      i1.const_mul _
    rw [this, integral_sub hA hB', integral_add hC' i1, integral_const_mul, integral_const_mul, ← hmr,
      h2_integral_cell_per_y hv x]
    ring
  rw [e] at h
  exact h

/-- Jensen: the mollification does not increase `∫ ρ log ρ`. -/
theorem h2_entropy_term_le {v : ℝ} (hv : 0 < v) {ρ : Ch N → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (hρ1 : ∫⁻ x in cep_cell N, ENNReal.ofReal (ρ x) = 1)
    (hL : Integrable (fun y => ρ y * Real.log (ρ y)) (volume.restrict (cep_cell N)))
    (hI : Integrable (fun x => h2_mu v (h2_dMeas ρ) x * Real.log (h2_mu v (h2_dMeas ρ) x))
      (volume.restrict (cep_cell N))) :
    ∫ x in cep_cell N, h2_mu v (h2_dMeas ρ) x * Real.log (h2_mu v (h2_dMeas ρ) x) ≤
      ∫ y in cep_cell N, ρ y * Real.log (ρ y) := by
  have hc := h2_cell_convolve hv hL
  have hint : Integrable (fun x => ∫ y in cep_cell N, h2_per v (x - y) * (ρ y * Real.log (ρ y)))
      (volume.restrict (cep_cell N)) := by
    -- via the Fubini integrability: the outer function is integrable because it is dominated by `hI`-free
    -- argument; we use the product integrability from `h2_cell_convolve`'s proof
    set μc : Measure (Ch N) := volume.restrict (cep_cell N) with hμc
    set f : Ch N → ℝ := fun y => ρ y * Real.log (ρ y) with hf
    have hmeas : AEStronglyMeasurable (Function.uncurry fun x y : Ch N => h2_per v (x - y) * f y) (μc.prod μc) :=
      (((h2_continuous_per hv).comp (continuous_fst.sub continuous_snd)).aestronglyMeasurable).mul
        (hL.aestronglyMeasurable.comp_snd)
    have hint : Integrable (Function.uncurry fun x y : Ch N => h2_per v (x - y) * f y) (μc.prod μc) := by
      refine (integrable_prod_iff' hmeas).2 ⟨Eventually.of_forall fun y => ?_, ?_⟩
      · exact (h2_integrableOn_cell_per_x hv y).mul_const (f y)
      · have e : (fun y => ∫ x, ‖(Function.uncurry fun x y : Ch N => h2_per v (x - y) * f y) (x, y)‖ ∂μc) =
            fun y => ‖f y‖ := by
          funext y
          simp only [Function.uncurry_apply_pair, norm_mul]
          rw [integral_mul_const]
          have : ∫ x, ‖h2_per v (x - y)‖ ∂μc = 1 := by
            rw [← h2_integral_cell_per_x hv y]
            refine integral_congr_ae (ae_of_all _ fun x => ?_)
            simp only [Real.norm_of_nonneg (h2_per_nonneg hv _)]
          rw [this, one_mul]
        rw [e]; exact hL.norm
    exact hint.integral_prod_left
  calc ∫ x in cep_cell N, h2_mu v (h2_dMeas ρ) x * Real.log (h2_mu v (h2_dMeas ρ) x)
      ≤ ∫ x in cep_cell N, ∫ y in cep_cell N, h2_per v (x - y) * (ρ y * Real.log (ρ y)) :=
        integral_mono hI hint (h2_jensen_pointwise hv hρ hρ0 hρ1 hL)
    _ = ∫ y in cep_cell N, ρ y * Real.log (ρ y) := hc

end HRS.MC.CepH2
