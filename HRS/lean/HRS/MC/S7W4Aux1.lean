import Mathlib
import HRS.Equilibrium.QuadraticLimit.ChaosAuxA

/-!
# Packet `s7_W4_gaussian_quadratic_clt`, scalar part

Pointwise Taylor bound for `e^{ix}`, the moments of `Y = g^2 - 1` for a standard Gaussian `g`, and the
estimate `|E e^{iuY} - e^{-u^2}| <= C |u|^3` for `|u| <= 1` (prefix `s7w4_`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.W4

/-- Second order Taylor bound for the complex exponential on the imaginary axis. -/
lemma s7w4_taylor (x : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - (1 + (x : ℂ) * Complex.I - ((x ^ 2 / 2 : ℝ) : ℂ))‖
      ≤ 4 * |x| ^ 3 := by
  by_cases hx : |x| ≤ 1
  · have hz : ‖(x : ℂ) * Complex.I‖ ≤ 1 := by simpa using hx
    have h := Complex.exp_bound hz (n := 3) (by norm_num)
    have e : ∑ m ∈ Finset.range 3, ((x : ℂ) * Complex.I) ^ m / (m.factorial : ℂ) =
        1 + (x : ℂ) * Complex.I - ((x ^ 2 / 2 : ℝ) : ℂ) := by
      simp [Finset.sum_range_succ, Nat.factorial, mul_pow]
      push_cast; ring
    rw [e] at h
    refine h.trans ?_
    simp only [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]
    norm_num [Nat.factorial]
    have : 0 ≤ |x| ^ 3 := by positivity
    nlinarith
  · push_neg at hx
    have h1 : ‖Complex.exp ((x : ℂ) * Complex.I)‖ = 1 := by
      simpa using Complex.norm_exp_ofReal_mul_I x
    calc _ ≤ ‖Complex.exp ((x : ℂ) * Complex.I)‖ + ‖(1 + (x : ℂ) * Complex.I - ((x ^ 2 / 2 : ℝ) : ℂ))‖ :=
          norm_sub_le _ _
      _ ≤ 1 + (1 + |x| + x ^ 2 / 2) := by
          rw [h1]
          gcongr
          calc _ ≤ ‖(1 : ℂ) + (x : ℂ) * Complex.I‖ + ‖((x ^ 2 / 2 : ℝ) : ℂ)‖ := norm_sub_le _ _
            _ ≤ (‖(1 : ℂ)‖ + ‖(x : ℂ) * Complex.I‖) + ‖((x ^ 2 / 2 : ℝ) : ℂ)‖ := by
                gcongr; exact norm_add_le _ _
            _ = 1 + |x| + x ^ 2 / 2 := by
                simp [abs_of_nonneg (by positivity : (0:ℝ) ≤ x ^ 2 / 2), sq_abs]
      _ ≤ 4 * |x| ^ 3 := by
          have h1 : 1 < |x| := hx
          have h2 : |x| ^ 2 = x ^ 2 := sq_abs x
          nlinarith [mul_pos (by linarith : (0:ℝ) < |x| - 1) (by linarith : (0:ℝ) < |x|),
            sq_nonneg (|x| - 1), mul_pos (by linarith : (0:ℝ) < |x| - 1) (by positivity : (0:ℝ) < |x| ^ 2)]

/-- the law of one standard Gaussian -/
abbrev s7w4_γ : Measure ℝ := gaussianReal 0 1

lemma s7w4_int_pow (k : ℕ) : Integrable (fun y : ℝ => y ^ k) s7w4_γ := by
  by_cases hk : k = 0
  · subst hk; simp
  · have h := (memLp_id_gaussianReal (μ := 0) (v := 1) (k : ℝ≥0)).integrable_norm_pow (p := k) hk
    refine h.mono' (by fun_prop) (Filter.Eventually.of_forall fun y => ?_)
    simp

lemma s7w4_gauss_two : ∫ y, y ^ 2 ∂s7w4_γ = 1 := by
  simpa using HRS.Q08.q08c_ch_gauss_two 1

lemma s7w4_gauss_four : ∫ y, y ^ 4 ∂s7w4_γ = 3 := by
  simpa using HRS.Q08.q08c_ch_gauss_four 1

lemma s7w4_intY : ∫ y, (y ^ 2 - 1) ∂s7w4_γ = 0 := by
  rw [integral_sub (s7w4_int_pow 2) (integrable_const _), s7w4_gauss_two]; simp

lemma s7w4_intY2 : ∫ y, (y ^ 2 - 1) ^ 2 ∂s7w4_γ = 2 := by
  have : ∀ y : ℝ, (y ^ 2 - 1) ^ 2 = y ^ 4 - 2 * y ^ 2 + 1 := fun y => by ring
  simp_rw [this]
  have hA : Integrable (fun y : ℝ => y ^ 4 - 2 * y ^ 2) s7w4_γ :=
    (s7w4_int_pow 4).sub ((s7w4_int_pow 2).const_mul 2)
  have hB : Integrable (fun y : ℝ => 2 * y ^ 2) s7w4_γ := (s7w4_int_pow 2).const_mul 2
  rw [integral_add hA (integrable_const _), integral_sub (s7w4_int_pow 4) hB, integral_const_mul,
    s7w4_gauss_four, s7w4_gauss_two]
  simp; norm_num

lemma s7w4_integrable_abs3 : Integrable (fun y : ℝ => |y ^ 2 - 1| ^ 3) s7w4_γ := by
  have hb : Integrable (fun y : ℝ => y ^ 6 + 3 * y ^ 4 + 3 * y ^ 2 + 1) s7w4_γ :=
    (((s7w4_int_pow 6).add ((s7w4_int_pow 4).const_mul 3)).add
      ((s7w4_int_pow 2).const_mul 3)).add (integrable_const _)
  refine hb.mono' (by fun_prop) (Filter.Eventually.of_forall fun y => ?_)
  have h0 : 0 ≤ |y ^ 2 - 1| := abs_nonneg _
  have h1 : |y ^ 2 - 1| ≤ y ^ 2 + 1 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg y]
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc |y ^ 2 - 1| ^ 3 ≤ (y ^ 2 + 1) ^ 3 := by gcongr
    _ = _ := by ring

/-- the third absolute moment of `g^2 - 1` -/
def s7w4_K : ℝ := ∫ y, |y ^ 2 - 1| ^ 3 ∂s7w4_γ

lemma s7w4_K_nonneg : 0 ≤ s7w4_K := integral_nonneg fun y => by positivity

/-- the characteristic function of `g^2 - 1` -/
def s7w4_phi (u : ℝ) : ℂ := ∫ y, Complex.exp (((u * (y ^ 2 - 1) : ℝ) : ℂ) * Complex.I) ∂s7w4_γ

lemma s7w4_phi_norm (u : ℝ) : ‖s7w4_phi u‖ ≤ 1 := by
  unfold s7w4_phi
  refine (norm_integral_le_of_norm_le_const (C := 1) (Filter.Eventually.of_forall fun y => ?_)).trans ?_
  · rw [Complex.norm_exp_ofReal_mul_I]
  · simp

lemma s7w4_phi_approx (u : ℝ) :
    ‖s7w4_phi u - ((1 - u ^ 2 : ℝ) : ℂ)‖ ≤ 4 * s7w4_K * |u| ^ 3 := by
  set p : ℝ → ℂ := fun y => 1 + ((u * (y ^ 2 - 1) : ℝ) : ℂ) * Complex.I -
    (((u * (y ^ 2 - 1)) ^ 2 / 2 : ℝ) : ℂ) with hp
  have hi1 : Integrable (fun y : ℝ => y ^ 2 - 1) s7w4_γ := (s7w4_int_pow 2).sub (integrable_const _)
  have hi2 : Integrable (fun y : ℝ => (y ^ 2 - 1) ^ 2) s7w4_γ := by
    have : ∀ y : ℝ, (y ^ 2 - 1) ^ 2 = y ^ 4 - 2 * y ^ 2 + 1 := fun y => by ring
    simp_rw [this]
    exact ((s7w4_int_pow 4).sub ((s7w4_int_pow 2).const_mul 2)).add (integrable_const _)
  have e : ∀ y : ℝ, p y = (((1 - (u ^ 2 / 2) * (y ^ 2 - 1) ^ 2 : ℝ)) : ℂ) +
      ((u * (y ^ 2 - 1) : ℝ) : ℂ) * Complex.I := by
    intro y; simp only [hp]; push_cast; ring
  have h1 : Integrable (fun y : ℝ => (((1 - (u ^ 2 / 2) * (y ^ 2 - 1) ^ 2 : ℝ)) : ℂ)) s7w4_γ :=
    (((integrable_const (1 : ℝ)).sub (hi2.const_mul (u ^ 2 / 2)))).ofReal
  have h2 : Integrable (fun y : ℝ => ((u * (y ^ 2 - 1) : ℝ) : ℂ) * Complex.I) s7w4_γ :=
    (((hi1.const_mul u)).ofReal).mul_const _
  have hpi : Integrable p s7w4_γ := by
    have : p = fun y => (((1 - (u ^ 2 / 2) * (y ^ 2 - 1) ^ 2 : ℝ)) : ℂ) +
        ((u * (y ^ 2 - 1) : ℝ) : ℂ) * Complex.I := funext e
    rw [this]; exact h1.add h2
  have hint : ∫ y, p y ∂s7w4_γ = ((1 - u ^ 2 : ℝ) : ℂ) := by
    simp_rw [e]
    rw [integral_add h1 h2, integral_mul_const, integral_complex_ofReal, integral_complex_ofReal,
      integral_sub (integrable_const _) (hi2.const_mul _), integral_const_mul, integral_const_mul,
      s7w4_intY, s7w4_intY2]
    simp
  have hdiff : s7w4_phi u - ((1 - u ^ 2 : ℝ) : ℂ) = ∫ y, (Complex.exp (((u * (y ^ 2 - 1) : ℝ) : ℂ) *
      Complex.I) - p y) ∂s7w4_γ := by
    have hex : Integrable (fun y : ℝ => Complex.exp (((u * (y ^ 2 - 1) : ℝ) : ℂ) * Complex.I)) s7w4_γ := by
      refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (Filter.Eventually.of_forall fun y => ?_)
      rw [Complex.norm_exp_ofReal_mul_I]
    unfold s7w4_phi
    rw [integral_sub hex hpi, hint]
  rw [hdiff]
  refine (norm_integral_le_of_norm_le (g := fun y => 4 * |u| ^ 3 * |y ^ 2 - 1| ^ 3)
    (s7w4_integrable_abs3.const_mul _) (Filter.Eventually.of_forall fun y => ?_)).trans ?_
  · have := s7w4_taylor (u * (y ^ 2 - 1))
    simp only [hp]
    refine this.trans (le_of_eq ?_)
    rw [abs_mul, mul_pow]; ring
  · rw [integral_const_mul]; unfold s7w4_K; nlinarith [le_refl (4 * |u| ^ 3 * ∫ y, |y ^ 2 - 1| ^ 3 ∂s7w4_γ)]

end HRS.MC.Sec7.W4
