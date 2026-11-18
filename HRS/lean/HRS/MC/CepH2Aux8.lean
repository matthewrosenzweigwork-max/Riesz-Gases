import HRS.MC.CepH2Aux7

/-!
# CEPH2, helper 8: unfolding the periodised kernel against periodic weights

`∫_cell Ĝ(x - y) W(x) dx = ∫_{ℝ^N} G(x - y) W(x) dx` for diagonally periodic `W`, and the Tonelli/Fubini versions
for double integrals against a measure in `y`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Pointwise

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ}

theorem h2_periodic_gen {β : Type*} {f : Ch N → β} (hper : ∀ x, f (x + cep_diag N) = f x) (m : ℤ) (x : Ch N) :
    f (x + (m : ℝ) • cep_diag N) = f x := by
  induction m using Int.induction_on generalizing x with
  | zero => simp
  | succ n ih =>
    have : x + (((n : ℤ) + 1 : ℤ) : ℝ) • cep_diag N = (x + ((n : ℤ) : ℝ) • cep_diag N) + cep_diag N := by
      push_cast; rw [add_smul, one_smul, add_assoc]
    rw [this, hper, ih]
  | pred n ih =>
    have h2 := hper (x + ((-(n : ℤ) - 1 : ℤ) : ℝ) • cep_diag N)
    have : x + ((-(n : ℤ) - 1 : ℤ) : ℝ) • cep_diag N + cep_diag N = x + ((-(n : ℤ) : ℤ) : ℝ) • cep_diag N := by
      push_cast; module
    rw [this, ih] at h2
    exact h2.symm

theorem h2_perp_periodic [NeZero N] (x : Ch N) : h2_perp (x + cep_diag N) = h2_perp x := by
  have := h2_perp_add_diag x 1
  simpa using this

section
variable [NeZero N]

theorem h2_ofReal_per {v : ℝ} (hv : 0 < v) (w : Ch N) :
    ENNReal.ofReal (h2_per v w) = ∑' m : ℤ, ENNReal.ofReal (h2_g v (w + (m : ℝ) • cep_diag N)) :=
  ENNReal.ofReal_tsum_of_nonneg (fun m => (h2_g_pos hv _).le) (h2_summable_g_trans hv w)

theorem h2_lintegral_cell_kernel {v : ℝ} (hv : 0 < v) {F : Ch N → ℝ≥0∞} (hF : Measurable F)
    (hper : ∀ x, F (x + cep_diag N) = F x) (y : Ch N) :
    ∫⁻ x in cep_cell N, ENNReal.ofReal (h2_per v (x - y)) * F x = ∫⁻ x, ENNReal.ofReal (h2_g v (x - y)) * F x := by
  have hm : Measurable fun x => ENNReal.ofReal (h2_g v (x - y)) * F x :=
    (ENNReal.measurable_ofReal.comp ((h2_continuous_g v).measurable.comp (measurable_id.sub_const y))).mul hF
  rw [h2_lintegral_unfold hm]
  refine lintegral_congr fun x => ?_
  simp_rw [h2_periodic_gen hper]
  rw [ENNReal.tsum_mul_right, h2_ofReal_per hv (x - y)]
  congr 2
  funext m
  rw [add_sub_right_comm]

theorem h2_lintegral_cell_mu {v : ℝ} (hv : 0 < v) (μ : Measure (Ch N)) [SFinite μ] {W : Ch N → Ch N → ℝ≥0∞}
    (hW : Measurable (Function.uncurry W)) (hper : ∀ x y, W (x + cep_diag N) y = W x y) :
    ∫⁻ x in cep_cell N, ∫⁻ y, ENNReal.ofReal (h2_per v (x - y)) * W x y ∂μ =
      ∫⁻ y, (∫⁻ x, ENNReal.ofReal (h2_g v (x - y)) * W x y) ∂μ := by
  have hm : Measurable (Function.uncurry fun x y : Ch N => ENNReal.ofReal (h2_per v (x - y)) * W x y) := by
    refine Measurable.mul ?_ hW
    exact ENNReal.measurable_ofReal.comp ((h2_continuous_per hv).measurable.comp (measurable_fst.sub measurable_snd))
  rw [lintegral_lintegral_swap hm.aemeasurable]
  refine lintegral_congr fun y => ?_
  exact h2_lintegral_cell_kernel hv (hW.comp (measurable_id.prodMk measurable_const)) (fun x => hper x y) y

theorem h2_integrable_per_sub {v : ℝ} (hv : 0 < v) (μ : Measure (Ch N)) [IsFiniteMeasure μ] (x : Ch N) :
    Integrable (fun y => h2_per v (x - y)) μ := by
  obtain ⟨B, hB, h⟩ := h2_per_le (N := N) hv
  exact (integrable_const B).mono'
    ((h2_continuous_per hv).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
    (ae_of_all _ fun y => (h _).1)

theorem h2_ofReal_mu {v : ℝ} (hv : 0 < v) (μ : Measure (Ch N)) [IsFiniteMeasure μ] (x : Ch N) :
    ENNReal.ofReal (h2_mu v μ x) = ∫⁻ y, ENNReal.ofReal (h2_per v (x - y)) ∂μ :=
  ofReal_integral_eq_lintegral_ofReal (h2_integrable_per_sub hv μ x) (ae_of_all _ fun y => h2_per_nonneg hv _)

theorem h2_lintegral_cell_mu_weight {v : ℝ} (hv : 0 < v) (μ : Measure (Ch N)) [IsFiniteMeasure μ]
    {w : Ch N → ℝ≥0∞} (hw : Measurable w) (hper : ∀ x, w (x + cep_diag N) = w x) :
    ∫⁻ x in cep_cell N, ENNReal.ofReal (h2_mu v μ x) * w x =
      ∫⁻ y, (∫⁻ x, ENNReal.ofReal (h2_g v (x - y)) * w x) ∂μ := by
  have := h2_lintegral_cell_mu hv μ (W := fun x _ => w x) (hw.comp measurable_fst) (fun x y => hper x)
  rw [← this]
  refine lintegral_congr fun x => ?_
  rw [h2_ofReal_mu hv μ x]
  exact (lintegral_mul_const _ ((ENNReal.measurable_ofReal.comp
    ((h2_continuous_per hv).measurable.comp (measurable_const.sub measurable_id))))).symm

/-- Gaussian average of a weight: translation to the origin. -/
theorem h2_lintegral_gauss_shift {v : ℝ} (w : Ch N → ℝ≥0∞) (y : Ch N) :
    ∫⁻ x, ENNReal.ofReal (h2_g v (x - y)) * w x = ∫⁻ z, ENNReal.ofReal (h2_g v z) * w (z + y) := by
  rw [← lintegral_sub_right_eq_self (fun z => ENNReal.ofReal (h2_g v z) * w (z + y)) y]
  simp only [sub_add_cancel]

theorem h2_lintegral_gauss_poly {v : ℝ} (hv : 0 < v) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∫⁻ z : Ch N, ENNReal.ofReal (h2_g v z) * ENNReal.ofReal (a + b * ‖z‖ ^ 2) = ENNReal.ofReal (a + b * (N * v)) := by
  have hi : Integrable (fun z : Ch N => h2_g v z * (a + b * ‖z‖ ^ 2)) := by
    have := (h2_integrable_g (N := N) hv).const_mul a |>.add ((h2_integrable_sq_g (N := N) hv).const_mul b)
    refine this.congr (ae_of_all _ fun z => ?_)
    simp only [Pi.add_apply]; ring
  have h0 : ∀ z : Ch N, 0 ≤ h2_g v z * (a + b * ‖z‖ ^ 2) := fun z =>
    mul_nonneg (h2_g_pos hv z).le (by positivity)
  have e := ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ h0)
  have e2 : ∀ z : Ch N, ENNReal.ofReal (h2_g v z * (a + b * ‖z‖ ^ 2)) =
      ENNReal.ofReal (h2_g v z) * ENNReal.ofReal (a + b * ‖z‖ ^ 2) := fun z =>
    ENNReal.ofReal_mul (h2_g_pos hv z).le
  simp_rw [e2] at e
  rw [← e]
  congr 1
  have : ∫ z : Ch N, h2_g v z * (a + b * ‖z‖ ^ 2) = a * (∫ z : Ch N, h2_g v z) + b * (∫ z : Ch N, ‖z‖ ^ 2 * h2_g v z) := by
    have e3 : (fun z : Ch N => h2_g v z * (a + b * ‖z‖ ^ 2)) = fun z => a * h2_g v z + b * (‖z‖ ^ 2 * h2_g v z) := by
      funext z; ring
    rw [e3, integral_add ((h2_integrable_g hv).const_mul a) ((h2_integrable_sq_g hv).const_mul b),
      integral_const_mul, integral_const_mul]
  rw [this, h2_g_integral (N := N) hv, h2_g_second (N := N) hv]
  ring

end

end HRS.MC.CepH2
