import HRS.Torus.Basic
import HRS.PDE.Toolbox

/-!
# Packet L2C-3a, helper 1: a Young/Schur inequality on the torus

For `k ≥ 0` integrable and bounded measurable `a, b ≥ 0`,
`∫ (∫ k(z) a(x - z) dz) b(x) dx ≤ (∫ k) ‖a‖₂ ‖b‖₂`.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.MC.L2C3a

variable {d : ℕ}

/-- AM-GM optimisation: `I ≤ ½(λP + Q/λ)` for all `λ > 0` gives `I ≤ √P √Q`. -/
theorem l2c3a_amgm {I P Q : ℝ} (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (h : ∀ l : ℝ, 0 < l → I ≤ (l * P + Q / l) / 2) : I ≤ Real.sqrt P * Real.sqrt Q := by
  have hp := Real.sqrt_nonneg P
  have hq := Real.sqrt_nonneg Q
  have hP2 := Real.sq_sqrt hP
  have hQ2 := Real.sq_sqrt hQ
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set δ := ε / (Real.sqrt P + Real.sqrt Q + 1) with hδdef
  have hδ : 0 < δ := div_pos hε (by linarith)
  have hδε : δ * (Real.sqrt P + Real.sqrt Q + 1) = ε := by
    rw [hδdef]; field_simp
  have hpd : 0 < Real.sqrt P + δ := by linarith
  have hqd : 0 < Real.sqrt Q + δ := by linarith
  have h1 := h ((Real.sqrt Q + δ) / (Real.sqrt P + δ)) (div_pos hqd hpd)
  have e1 : (Real.sqrt Q + δ) / (Real.sqrt P + δ) * P ≤ (Real.sqrt Q + δ) * Real.sqrt P := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hpd]
    have : P = Real.sqrt P * Real.sqrt P := by nlinarith
    calc (Real.sqrt Q + δ) * P = (Real.sqrt Q + δ) * (Real.sqrt P * Real.sqrt P) := by rw [← this]
      _ ≤ (Real.sqrt Q + δ) * Real.sqrt P * (Real.sqrt P + δ) := by
        have : 0 ≤ (Real.sqrt Q + δ) * Real.sqrt P * δ := by positivity
        nlinarith
  have e2 : Q / ((Real.sqrt Q + δ) / (Real.sqrt P + δ)) ≤ (Real.sqrt P + δ) * Real.sqrt Q := by
    rw [div_div_eq_mul_div, div_le_iff₀ hqd]
    have : Q = Real.sqrt Q * Real.sqrt Q := by nlinarith
    calc Q * (Real.sqrt P + δ) = (Real.sqrt P + δ) * (Real.sqrt Q * Real.sqrt Q) := by
          rw [← this]; ring
      _ ≤ (Real.sqrt P + δ) * Real.sqrt Q * (Real.sqrt Q + δ) := by
        have : 0 ≤ (Real.sqrt P + δ) * Real.sqrt Q * δ := by positivity
        nlinarith
  nlinarith [mul_nonneg hδ.le hp, mul_nonneg hδ.le hq]

theorem l2c3a_integrable_of_bdd {f : Torus d → ℝ} (hf : Measurable f) {B : ℝ} (hB : ∀ x, |f x| ≤ B) :
    Integrable f :=
  Integrable.of_bound hf.aestronglyMeasurable B (Filter.Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs]; exact hB x)

/-- Cauchy-Schwarz for bounded measurable functions. -/
theorem l2c3a_cs {a b : Torus d → ℝ} (ha : Measurable a) (hb : Measurable b) {A B : ℝ}
    (hA : ∀ x, |a x| ≤ A) (hB : ∀ x, |b x| ≤ B) :
    ∫ x, a x * b x ≤ Real.sqrt (∫ x, a x ^ 2) * Real.sqrt (∫ x, b x ^ 2) := by
  have ia2 : Integrable (fun x => a x ^ 2) := l2c3a_integrable_of_bdd (ha.pow_const 2)
    (B := A ^ 2) fun x => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hA x) 2
  have ib2 : Integrable (fun x => b x ^ 2) := l2c3a_integrable_of_bdd (hb.pow_const 2)
    (B := B ^ 2) fun x => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hB x) 2
  have iab : Integrable (fun x => a x * b x) := l2c3a_integrable_of_bdd (ha.mul hb)
    (B := A * B) fun x => by
      rw [abs_mul]; exact mul_le_mul (hA x) (hB x) (abs_nonneg _) ((abs_nonneg _).trans (hA x))
  refine l2c3a_amgm (integral_nonneg fun x => sq_nonneg _) (integral_nonneg fun x => sq_nonneg _)
    fun l hl => ?_
  have : ∫ x, a x * b x ≤ ∫ x, (l * a x ^ 2 + b x ^ 2 / l) / 2 := by
    refine integral_mono iab ((ia2.const_mul l |>.add (ib2.div_const l)).div_const 2) fun x => ?_
    simp only
    have : 2 * (a x * b x) ≤ l * a x ^ 2 + b x ^ 2 / l := by
      have h0 : 0 ≤ (Real.sqrt l * a x - b x / Real.sqrt l) ^ 2 := sq_nonneg _
      have hs : Real.sqrt l ^ 2 = l := Real.sq_sqrt hl.le
      have hs0 : 0 < Real.sqrt l := Real.sqrt_pos.2 hl
      have : (Real.sqrt l * a x - b x / Real.sqrt l) ^ 2 =
          l * a x ^ 2 - 2 * (a x * b x) + b x ^ 2 / l := by
        field_simp
        rw [hs]; ring
      linarith
    linarith
  refine this.trans (le_of_eq ?_)
  rw [integral_div, integral_add (ia2.const_mul l) (ib2.div_const l), integral_const_mul,
    integral_div]

theorem l2c3a_conv_meas {k a : Torus d → ℝ} (hk : Integrable k) (ha : Measurable a) :
    AEStronglyMeasurable (fun x => ∫ z, k z * a (x - z)) volume := by
  have := (hk.aestronglyMeasurable).convolution (ContinuousLinearMap.mul ℝ ℝ)
    ha.aestronglyMeasurable (μ := volume)
  have e : convolution k a (ContinuousLinearMap.mul ℝ ℝ) volume =
      fun x => ∫ z, k z * a (x - z) := by
    funext x; rw [convolution_def]; rfl
  rw [e] at this
  exact this

theorem l2c3a_conv_bd {k a : Torus d → ℝ} (hk : Integrable k) (hk0 : ∀ z, 0 ≤ k z) {A : ℝ}
    (hA : ∀ x, |a x| ≤ A) (x : Torus d) : |∫ z, k z * a (x - z)| ≤ (∫ z, k z) * A := by
  have : ‖∫ z, k z * a (x - z)‖ ≤ ∫ z, k z * A := by
    refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun z => norm_nonneg _) (hk.mul_const A)
      (Filter.Eventually.of_forall fun z => ?_))
    show ‖k z * a (x - z)‖ ≤ k z * A
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hk0 z)]
    exact mul_le_mul_of_nonneg_left (hA _) (hk0 z)
  rw [integral_mul_const] at this
  rwa [Real.norm_eq_abs] at this

theorem l2c3a_conv_mul_integrable {k a b : Torus d → ℝ} (hk : Integrable k) (hk0 : ∀ z, 0 ≤ k z)
    (ha : Measurable a) (hb : Measurable b) {A B : ℝ}
    (hA : ∀ x, |a x| ≤ A) (hB : ∀ x, |b x| ≤ B) :
    Integrable (fun x => (∫ z, k z * a (x - z)) * b x) := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA (0 : Torus d))
  have hN0 : 0 ≤ ∫ z, k z := integral_nonneg hk0
  refine Integrable.of_bound ((l2c3a_conv_meas hk ha).mul hb.aestronglyMeasurable)
    ((∫ z, k z) * A * B) (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul (l2c3a_conv_bd hk hk0 hA x) (hB x) (abs_nonneg _) (by positivity)

/-- The Schur/Young inequality `‖k ⋆ a‖ ≤ ‖k‖₁ ‖a‖` tested against `b`. -/
theorem l2c3a_schur {k a b : Torus d → ℝ} (hk : Integrable k) (hk0 : ∀ z, 0 ≤ k z)
    (ha : Measurable a) (hb : Measurable b) {A B : ℝ}
    (hA : ∀ x, |a x| ≤ A) (hB : ∀ x, |b x| ≤ B) :
    ∫ x, (∫ z, k z * a (x - z)) * b x ≤
      (∫ z, k z) * (Real.sqrt (∫ x, a x ^ 2) * Real.sqrt (∫ x, b x ^ 2)) := by
  set N := ∫ z, k z with hN
  have hN0 : 0 ≤ N := integral_nonneg hk0
  have ia2 : Integrable (fun x => a x ^ 2) := l2c3a_integrable_of_bdd (ha.pow_const 2)
    (B := A ^ 2) fun x => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hA x) 2
  have ib2 : Integrable (fun x => b x ^ 2) := l2c3a_integrable_of_bdd (hb.pow_const 2)
    (B := B ^ 2) fun x => by
      rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hB x) 2
  have hub := l2c3a_conv_mul_integrable hk hk0 ha hb hA hB
  set L := ContinuousLinearMap.mul ℝ ℝ with hL
  have conv_eq : ∀ (f : Torus d → ℝ) x, convolution k f L volume x = ∫ z, k z * f (x - z) := by
    intro f x; rw [convolution_def]; rfl
  have hcv2 : Integrable (fun x => ∫ z, k z * a (x - z) ^ 2) := by
    have := hk.integrable_convolution L ia2
    simpa [funext (conv_eq (fun x => a x ^ 2))] using this
  have hcv2int : ∫ x, (∫ z, k z * a (x - z) ^ 2) = N * ∫ x, a x ^ 2 := by
    have := integral_convolution L (μ := (volume : Measure (Torus d))) (ν := volume) hk ia2
    simp only [funext (conv_eq (fun x => a x ^ 2))] at this
    rw [this]; rfl
  have hint_z : ∀ (f : Torus d → ℝ), Measurable f → ∀ {Bf : ℝ}, (∀ x, |f x| ≤ Bf) → ∀ x,
      Integrable (fun z => k z * f (x - z)) := by
    intro f hf Bf hBf x
    refine Integrable.mono' (hk.norm.mul_const Bf) ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact hk.aestronglyMeasurable.mul (hf.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
    · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hBf _) (abs_nonneg _)
  have key : ∀ l : ℝ, 0 < l → ∫ x, (∫ z, k z * a (x - z)) * b x ≤
      (l * (N * ∫ x, a x ^ 2) + (N * ∫ x, b x ^ 2) / l) / 2 := by
    intro l hl
    have hpt : ∀ x, (∫ z, k z * a (x - z)) * b x ≤
        (l * (∫ z, k z * a (x - z) ^ 2) + N * b x ^ 2 / l) / 2 := by
      intro x
      have i1 := hint_z a ha hA x
      have i2 := hint_z (fun x => a x ^ 2) (ha.pow_const 2) (Bf := A ^ 2) (fun x => by
        rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hA x) 2) x
      rw [← integral_mul_const]
      have : ∫ z, k z * a (x - z) * b x ≤ ∫ z, (l * (k z * a (x - z) ^ 2) + k z * b x ^ 2 / l) / 2 := by
        refine integral_mono (i1.mul_const _) (((i2.const_mul l).add ((hk.mul_const _).div_const l)).div_const 2)
          fun z => ?_
        simp only
        have h0 := hk0 z
        have : 2 * (a (x - z) * b x) ≤ l * a (x - z) ^ 2 + b x ^ 2 / l := by
          have hs : Real.sqrt l ^ 2 = l := Real.sq_sqrt hl.le
          have hs0 : 0 < Real.sqrt l := Real.sqrt_pos.2 hl
          have e : (Real.sqrt l * a (x - z) - b x / Real.sqrt l) ^ 2 =
              l * a (x - z) ^ 2 - 2 * (a (x - z) * b x) + b x ^ 2 / l := by
            field_simp
            rw [hs]; ring
          nlinarith [sq_nonneg (Real.sqrt l * a (x - z) - b x / Real.sqrt l)]
        have := mul_le_mul_of_nonneg_left this h0
        have e2 : k z * (b x ^ 2 / l) = k z * b x ^ 2 / l := by ring
        nlinarith
      refine this.trans (le_of_eq ?_)
      rw [integral_div, integral_add (i2.const_mul l) ((hk.mul_const _).div_const l),
        integral_const_mul, integral_div, integral_mul_const]
    have hrhs : Integrable (fun x => (l * (∫ z, k z * a (x - z) ^ 2) + N * b x ^ 2 / l) / 2) :=
      ((hcv2.const_mul l).add ((ib2.const_mul N).div_const l)).div_const 2
    refine (integral_mono hub hrhs hpt).trans (le_of_eq ?_)
    rw [integral_div, integral_add (hcv2.const_mul l) ((ib2.const_mul N).div_const l),
      integral_const_mul, hcv2int, integral_div, integral_const_mul]
  have hP : 0 ≤ N * ∫ x, a x ^ 2 := mul_nonneg hN0 (integral_nonneg fun x => sq_nonneg _)
  have hQ : 0 ≤ N * ∫ x, b x ^ 2 := mul_nonneg hN0 (integral_nonneg fun x => sq_nonneg _)
  refine (l2c3a_amgm hP hQ key).trans (le_of_eq ?_)
  rw [Real.sqrt_mul hN0, Real.sqrt_mul hN0, mul_mul_mul_comm, Real.mul_self_sqrt hN0]

end HRS.MC.L2C3a
