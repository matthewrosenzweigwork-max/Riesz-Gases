import HRS.MH.ScreenedFarAux1
import HRS.MH.ScreenedK4Aux1
import HRS.MH.ScreenedA3b

/-! Helper lemmas for the assembly `screened_comm_cell_proof` (S.B.4(iv), cell-sum part):
monotonicity of the cell sums, the splitting of the second commutator kernel into a near and a far piece,
and the resulting integrability and `L²` estimate. -/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform

namespace HRS.MH.Screened

open HRS HRS.Whole

variable {d : ℕ}

/-- `(a+b)² ≤ 2A + 2B` from `a² ≤ A`, `b² ≤ B`. -/
lemma acc_sq_add (a b A B : ℝ≥0∞) (ha : a ^ 2 ≤ A) (hb : b ^ 2 ≤ B) : (a + b) ^ 2 ≤ 2 * A + 2 * B := by
  have h := ENNReal.rpow_add_le_mul_rpow_add_rpow a b (p := 2) (by norm_num)
  rw [ENNReal.rpow_two, ENNReal.rpow_two, ENNReal.rpow_two] at h
  have h2 : (2 : ℝ≥0∞) ^ ((2 : ℝ) - 1) = 2 := by norm_num
  rw [h2] at h
  calc (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := h
    _ ≤ 2 * (A + B) := by gcongr
    _ = 2 * A + 2 * B := by ring

/-- Monotonicity of the weighted cell sums in the constant and in the coefficients. -/
lemma acc_mono (c c' : ℝ) (hcc : c ≤ c') (A B N : (Fin d → ℤ) → ℝ≥0∞) (hAB : ∀ z', A z' ≤ B z') :
    ENNReal.ofReal c * ∑' z', A z' * N z' ≤ ENNReal.ofReal c' * ∑' z', B z' * N z' :=
  mul_le_mul' (ENNReal.ofReal_le_ofReal hcc) (ENNReal.tsum_le_tsum fun z' => mul_le_mul' (hAB z') le_rfl)

lemma acc_four (a : ℝ) (S : ℝ≥0∞) :
    2 * (ENNReal.ofReal a * S) + 2 * (ENNReal.ofReal a * S) = ENNReal.ofReal (4 * a) * S := by
  rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  have h4 : ENNReal.ofReal 4 = 4 := by simp
  rw [h4]
  ring

lemma acc_split_pt (cz ch : Euc d → ℝ) (hz : ∀ y, cz y * (1 - ch y) = 0) (a Kx : Euc d → ℝ) (cx : ℝ) (y : Euc d) :
    (cx - cz y) * a y * Kx y = ch y * ((cx - cz y) * a y) * Kx y + cx * (Kx y * ((1 - ch y) * a y)) := by
  have := hz y
  linear_combination (-(a y) * Kx y) * this

/-- Component of the vector convolution as a scalar integral when all components are integrable. -/
lemma acc_grad_comp {s : ℝ} (h : Euc d → ℝ) (x : Euc d) (i : Fin d)
    (hint : ∀ j, Integrable (fun y => rieszKernelGrad d s (x - y) j * h y)) :
    gradGConvPlain d s h x i = ∫ y, rieszKernelGrad d s (x - y) i * h y := by
  have hv : ∀ j, Integrable (fun y => (h y • rieszKernelGrad d s (x - y)) j) := by
    intro j
    have := hint j
    simpa [mul_comm] using this
  unfold gradGConvPlain
  rw [eval_integral_piLp (f := fun y => h y • rieszKernelGrad d s (x - y)) hv i]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [mul_comm]

/-- The second kernel `(χ_z(x) - χ_z(y)) K(x-y)` splits into the near and far pieces. -/
lemma acc_k2 {s : ℝ} (cz ch a : Euc d → ℝ) (i : Fin d)
    (hcz01 : ∀ x, 0 ≤ cz x ∧ cz x ≤ 1) (hczm : Measurable cz) (hz : ∀ y, cz y * (1 - ch y) = 0)
    (P Q : ℝ≥0∞)
    (hN : ∀ᵐ x ∂volume, x ∈ tsupport cz →
      Integrable (fun y => ch y * ((cz x - cz y) * a y) * rieszKernelGrad d s (x - y) i))
    (hF : ∀ x ∈ tsupport cz, ∀ j,
      Integrable (fun y => rieszKernelGrad d s (x - y) j * ((1 - ch y) * a y)))
    (hFm : AEStronglyMeasurable (fun x => cz x *
      gradGConvPlain d s (fun y => (1 - ch y) * a y) x i) volume)
    (hNb : (eLpNorm (fun x => cz x *
      ∫ y, ch y * ((cz x - cz y) * a y) * rieszKernelGrad d s (x - y) i) 2 volume) ^ 2 ≤ P)
    (hFb : (eLpNorm (fun x => cz x *
      gradGConvPlain d s (fun y => (1 - ch y) * a y) x i) 2 volume) ^ 2 ≤ Q) :
    (∀ᵐ x ∂volume, x ∈ tsupport cz →
      Integrable (fun y => (cz x - cz y) * a y * rieszKernelGrad d s (x - y) i)) ∧
    (eLpNorm (fun x => cz x * ∫ y, (cz x - cz y) * a y * rieszKernelGrad d s (x - y) i) 2 volume) ^ 2 ≤
      2 * P + 2 * Q := by
  refine ⟨?_, ?_⟩
  · filter_upwards [hN] with x hx hxt
    have h1 := hx hxt
    have h2 : Integrable (fun y => cz x * (rieszKernelGrad d s (x - y) i * ((1 - ch y) * a y))) :=
      (hF x hxt i).const_mul _
    exact (h1.add h2).congr (Filter.Eventually.of_forall fun y =>
      (acc_split_pt cz ch hz a (fun y => rieszKernelGrad d s (x - y) i) (cz x) y).symm)
  · have hEq : (fun x => cz x * ∫ y, (cz x - cz y) * a y * rieszKernelGrad d s (x - y) i) =ᵐ[volume]
        fun x => (cz x * ∫ y, ch y * ((cz x - cz y) * a y) * rieszKernelGrad d s (x - y) i) +
          cz x * (cz x * gradGConvPlain d s (fun y => (1 - ch y) * a y) x i) := by
      filter_upwards [hN] with x hx
      by_cases hxt : x ∈ tsupport cz
      · have h1 := hx hxt
        have h2 : Integrable (fun y => cz x * (rieszKernelGrad d s (x - y) i * ((1 - ch y) * a y))) :=
          (hF x hxt i).const_mul _
        have e : (fun y => (cz x - cz y) * a y * rieszKernelGrad d s (x - y) i) =
            fun y => ch y * ((cz x - cz y) * a y) * rieszKernelGrad d s (x - y) i +
              cz x * (rieszKernelGrad d s (x - y) i * ((1 - ch y) * a y)) :=
          funext fun y => acc_split_pt cz ch hz a (fun y => rieszKernelGrad d s (x - y) i) (cz x) y
        rw [e, integral_add h1 h2, integral_const_mul, acc_grad_comp _ x i (hF x hxt)]
        ring
      · have h0 : cz x = 0 := image_eq_zero_of_notMem_tsupport hxt
        simp [h0]
    have hczF : AEStronglyMeasurable (fun x => cz x * (cz x *
        gradGConvPlain d s (fun y => (1 - ch y) * a y) x i)) volume :=
      hczm.aestronglyMeasurable.mul hFm
    have hle : eLpNorm (fun x => cz x * (cz x * gradGConvPlain d s (fun y => (1 - ch y) * a y) x i)) 2 volume ≤
        eLpNorm (fun x => cz x * gradGConvPlain d s (fun y => (1 - ch y) * a y) x i) 2 volume := by
      refine eLpNorm_mono hczF fun x => ?_
      rw [norm_mul]
      calc ‖cz x‖ * ‖cz x * gradGConvPlain d s (fun y => (1 - ch y) * a y) x i‖
          ≤ 1 * ‖cz x * gradGConvPlain d s (fun y => (1 - ch y) * a y) x i‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            rw [Real.norm_eq_abs, abs_of_nonneg (hcz01 x).1]
            exact (hcz01 x).2
        _ = _ := one_mul _
    rw [eLpNorm_congr_ae hEq]
    have hadd := eLpNorm_add_le (f := fun x => cz x *
      ∫ y, ch y * ((cz x - cz y) * a y) * rieszKernelGrad d s (x - y) i) (g := fun x => cz x * (cz x *
        gradGConvPlain d s (fun y => (1 - ch y) * a y) x i)) (p := 2) (μ := volume) (by norm_num)
    have hsq := acc_sq_add _ _ _ _ hNb (le_trans (pow_le_pow_left' hle 2) hFb)
    exact le_trans (pow_le_pow_left' hadd 2) hsq

lemma acc_meas_far {s : ℝ} (cz ch D ψ : Euc d → ℝ) (hcz : Measurable cz) (hch : Measurable ch)
    (hD : Measurable D) (hψ : Measurable ψ) (i : Fin d) :
    AEStronglyMeasurable (fun x => cz x *
      gradGConvPlain d s (fun y => (1 - ch y) * (D y * ψ y)) x i) volume :=
  (hcz.stronglyMeasurable.mul (far_meas_grad (s := s) _
    ((measurable_const.sub hch).mul (hD.mul hψ)) i)).aestronglyMeasurable

end HRS.MH.Screened
