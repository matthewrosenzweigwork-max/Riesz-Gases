import HRS.Energy.StaticLimitAux

/-!
# Fourier coefficients of spectral kernels (work package STAT-4.21)
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.StaticLimitAux

open HRS Torus

variable {d : ℕ} {a : Lattice d → ℝ}

theorem mode_apply_zero (k : Lattice d) : mode k (0 : Torus d) = 1 := by
  have h := mode_add_arg' k (0 : Torus d) 0
  rw [add_zero] at h
  have hn : ‖mode k (0 : Torus d)‖ = 1 := norm_mode k 0
  have hne : mode k (0 : Torus d) ≠ 0 := by
    intro h0; rw [h0] at hn; simp at hn
  have := mul_left_cancel₀ hne (show mode k 0 * mode k 0 = mode k 0 * 1 by rw [mul_one, ← h])
  exact this

theorem cosMode_neg_arg (k : Lattice d) (x : Torus d) : cosMode k (-x) = cosMode k x := by
  have h := cosMode_sub' k 0 x
  rw [zero_sub] at h
  rw [h]
  have h1 : cosMode k (0 : Torus d) = 1 := by simp [cosMode, mode_apply_zero]
  have h2 : sinMode k (0 : Torus d) = 0 := by simp [sinMode, mode_apply_zero]
  rw [h1, h2]; ring

theorem ofReal_cosMode (j : Lattice d) (x : Torus d) :
    ((cosMode j x : ℝ) : ℂ) = (mode j x + mode (-j) x) / 2 := by
  rw [mode_neg]
  unfold cosMode
  have := Complex.add_conj (mode j x)
  rw [this]; push_cast; ring

theorem integral_mode_mul_cos (k j : Lattice d) :
    ∫ x, mode (-k) x * ((cosMode j x : ℝ) : ℂ) =
      ((if j = k then 1 else 0) + (if j = -k then 1 else 0) : ℂ) / 2 := by
  simp_rw [ofReal_cosMode, mul_div_assoc', mul_add]
  rw [integral_div, integral_add (integrable_mode_mul _ _) (integrable_mode_mul _ _),
    integral_mode_mul, integral_mode_mul]
  have e1 : (-k + j = 0) ↔ j = k := by
    constructor <;> intro h
    · exact (neg_add_eq_zero.mp h).symm
    · rw [h]; simp
  have e2 : (-k + -j = 0) ↔ j = -k := by
    constructor <;> intro h
    · have : -(k + j) = 0 := by rw [← h]; abel
      have := neg_eq_zero.mp this
      exact eq_neg_of_add_eq_zero_right this
    · rw [h]; simp
  simp only [e1, e2]

theorem fcoef_specKernel (ha0 : ∀ k, 0 ≤ a k) (has : Summable a)
    (hsymm : ∀ k, a (-k) = a k) (k : Lattice d) :
    fcoef (specKernel a) k = a k := by
  unfold fcoef specKernel
  have hF : ∀ j, ∫ x, mode (-k) x * ((a j * cosMode j x : ℝ) : ℂ) =
      (a j : ℂ) * (((if j = k then 1 else 0) + (if j = -k then 1 else 0) : ℂ) / 2) := by
    intro j
    simp_rw [Complex.ofReal_mul]
    simp_rw [show ∀ x, mode (-k) x * ((a j : ℂ) * ((cosMode j x : ℝ) : ℂ)) =
      (a j : ℂ) * (mode (-k) x * ((cosMode j x : ℝ) : ℂ)) from fun x => by ring]
    rw [integral_const_mul, integral_mode_mul_cos]
  have hint : ∀ j, Integrable (fun x => mode (-k) x * ((a j * cosMode j x : ℝ) : ℂ)) :=
    fun j => ((continuous_mode _).mul
      (Complex.continuous_ofReal.comp (continuous_const.mul (continuous_cosMode j)))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hnorm : Summable fun j => ∫ x, ‖mode (-k) x * ((a j * cosMode j x : ℝ) : ℂ)‖ := by
    refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun x => norm_nonneg _)
      (fun j => ?_) has
    have : ∀ x, ‖mode (-k) x * ((a j * cosMode j x : ℝ) : ℂ)‖ ≤ a j := by
      intro x
      rw [norm_mul, norm_mode, one_mul, Complex.norm_real, Real.norm_eq_abs]
      exact norm_mul_cos_le ha0 j x
    calc ∫ x, ‖mode (-k) x * ((a j * cosMode j x : ℝ) : ℂ)‖ ≤ ∫ x, a j := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _)
            (integrable_const _) (Filter.Eventually.of_forall this)
      _ = a j := by simp
  have h1 := integral_tsum_of_summable_integral_norm hint hnorm
  have e : ∀ x, mode (-k) x * (((∑' j, a j * cosMode j x : ℝ)) : ℂ) =
      ∑' j, mode (-k) x * ((a j * cosMode j x : ℝ) : ℂ) := by
    intro x
    have hs : Summable fun j => a j * cosMode j x :=
      Summable.of_norm_bounded has fun j => norm_mul_cos_le ha0 j x
    rw [Complex.ofReal_tsum, ← tsum_mul_left]
  simp_rw [e]
  rw [← h1]
  simp_rw [hF]
  have : ∀ j, (a j : ℂ) * (((if j = k then 1 else 0) + (if j = -k then 1 else 0) : ℂ) / 2)
      = ((a j / 2 * (if j = k then 1 else 0) + a j / 2 * (if j = -k then 1 else 0) : ℝ) : ℂ) := by
    intro j
    split_ifs <;> push_cast <;> ring
  simp_rw [this]
  have s1 : Summable fun b => a b / 2 * (if b = k then (1:ℝ) else 0) :=
    Summable.of_nonneg_of_le (fun b => by have := ha0 b; split_ifs <;> positivity)
      (fun b => by have := ha0 b; split_ifs <;> nlinarith) (has.div_const 2)
  have s2 : Summable fun b => a b / 2 * (if b = -k then (1:ℝ) else 0) :=
    Summable.of_nonneg_of_le (fun b => by have := ha0 b; split_ifs <;> positivity)
      (fun b => by have := ha0 b; split_ifs <;> nlinarith) (has.div_const 2)
  have t1 : ∑' b, a b / 2 * (if b = k then (1:ℝ) else 0) = a k / 2 := by
    rw [tsum_eq_single k]
    · simp
    · intro b hb; simp [hb]
  have t2 : ∑' b, a b / 2 * (if b = -k then (1:ℝ) else 0) = a k / 2 := by
    rw [tsum_eq_single (-k)]
    · simp [hsymm]
    · intro b hb; simp [hb]
  rw [← Complex.ofReal_tsum, Summable.tsum_add s1 s2, t1, t2]
  push_cast; ring

end HRS.StaticLimitAux
