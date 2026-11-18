import HRS.Commutator.Whole.INHOMAux10

/-!
# CMX-INHOM auxiliary 11: convolutions with a band-limited bounded kernel
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff Convolution

namespace HRS.Commutator.Whole

open HRS HRS.Whole

variable {d : ℕ}

/-- the Fourier support is preserved by convolution with an `L¹` function. -/
theorem inhom_fs_conv {R : ℝ} {u : Euc d → ℝ} (hu : FourierSuppIn R u) (hum : Continuous u) {B : ℝ}
    (hB : ∀ x, |u x| ≤ B) {a : Euc d → ℝ} (hac : Continuous a) (ha : Integrable a volume) :
    FourierSuppIn R (fun x => ∫ y, a y * u (x - y)) := by
  intro θ hθ
  have hθi : Integrable (fun x => ‖θ x‖) volume := θ.integrable.norm
  have hint : Integrable (fun p : Euc d × Euc d =>
      ((a p.2 : ℝ) : ℂ) * ((u (p.1 - p.2) : ℝ) : ℂ) * θ p.1) (volume.prod volume) := by
    refine ((hθi.mul_prod ha.norm).const_mul B).mono' ?_ (Eventually.of_forall fun p => ?_)
    · have h1 : Continuous fun p : Euc d × Euc d =>
        ((a p.2 : ℝ) : ℂ) * ((u (p.1 - p.2) : ℝ) : ℂ) * θ p.1 := by
        have := Complex.continuous_ofReal
        fun_prop
      exact h1.aestronglyMeasurable
    · simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have := hB (p.1 - p.2)
      calc |a p.2| * |u (p.1 - p.2)| * ‖θ p.1‖ ≤ |a p.2| * B * ‖θ p.1‖ := by gcongr
        _ = B * (‖θ p.1‖ * ‖a p.2‖) := by rw [Real.norm_eq_abs]; ring
  have hsec : ∀ y : Euc d, ∫ x, ((a y : ℝ) : ℂ) * ((u (x - y) : ℝ) : ℂ) * θ x = 0 := by
    intro y
    have h0 := lowv_fs_translate hu y θ hθ
    have e : ∀ x : Euc d, ((a y : ℝ) : ℂ) * ((u (x - y) : ℝ) : ℂ) * θ x =
        ((a y : ℝ) : ℂ) * (((u (x - y) : ℝ) : ℂ) * θ x) := fun x => by ring
    simp_rw [e]
    rw [integral_const_mul, h0, mul_zero]
  have e : ∀ x : Euc d, ((∫ y, a y * u (x - y) : ℝ) : ℂ) * θ x =
      ∫ y, ((a y : ℝ) : ℂ) * ((u (x - y) : ℝ) : ℂ) * θ x := by
    intro x
    rw [← integral_complex_ofReal, ← integral_mul_const]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    push_cast; ring
  simp_rw [e]
  rw [integral_integral_swap hint]
  simp_rw [hsec]
  simp

lemma inhom_conv_comp {H : Euc d → Euc d} {a : Euc d → ℝ} (x : Euc d) (i : Fin d)
    (h : Integrable (fun y => a y • H (x - y)) volume) :
    inhom_conv H a x i = ∫ y, a y * H (x - y) i := by
  unfold inhom_conv
  have := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).integral_comp_comm h
  simpa using this.symm

lemma inhom_conv_continuous {H : Euc d → Euc d} (hH : Continuous H) {B : ℝ} (hB : ∀ x, ‖H x‖ ≤ B)
    {a : Euc d → ℝ} (ha : Integrable a volume) : Continuous (inhom_conv H a) := by
  have hbdd : BddAbove (Set.range fun x => ‖H x‖) := ⟨B, by rintro _ ⟨y, rfl⟩; exact hB y⟩
  have h := hbdd.continuous_convolution_right_of_integrable (ContinuousLinearMap.lsmul ℝ ℝ) ha hH
  convert h using 1
  funext x
  unfold inhom_conv
  rw [convolution_def]
  rfl

end HRS.Commutator.Whole
