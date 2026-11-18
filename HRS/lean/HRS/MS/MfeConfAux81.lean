import HRS.MS.MfeConfAux80

/-!
# S.B.1, packet F8 (part 13): weighted-Lipschitz calculus

`Sb1WL f D`: `|f x - f y| ≤ D |x-y| (1+|x|+|y|)`.  Lipschitz functions, sums, constant multiples, and products
`f g` with `f` bounded Lipschitz and `g` of linear growth and Lipschitz are weighted Lipschitz.
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.MfeConf

variable {E : Type*} [NormedAddCommGroup E]

def Sb1WL (f : E → ℝ) (D : ℝ) : Prop := ∀ x y, |f x - f y| ≤ D * ‖x - y‖ * (1 + ‖x‖ + ‖y‖)

theorem Sb1WL.of_lip {f : E → ℝ} {L : ℝ} (hL : 0 ≤ L) (h : ∀ x y, |f x - f y| ≤ L * ‖x - y‖) : Sb1WL f L := by
  intro x y
  refine (h x y).trans ?_
  have : 0 ≤ L * ‖x - y‖ := by positivity
  nlinarith [norm_nonneg x, norm_nonneg y]

theorem Sb1WL.mono {f : E → ℝ} {D D' : ℝ} (h : Sb1WL f D) (hD : D ≤ D') : Sb1WL f D' := fun x y =>
  (h x y).trans (by gcongr)

theorem Sb1WL.add {f g : E → ℝ} {D D' : ℝ} (hf : Sb1WL f D) (hg : Sb1WL g D') : Sb1WL (fun x => f x + g x) (D + D') := by
  intro x y
  have := abs_add_le (f x - f y) (g x - g y)
  have e : f x + g x - (f y + g y) = (f x - f y) + (g x - g y) := by ring
  rw [e]
  have h1 := hf x y
  have h2 := hg x y
  nlinarith

theorem Sb1WL.sub {f g : E → ℝ} {D D' : ℝ} (hf : Sb1WL f D) (hg : Sb1WL g D') : Sb1WL (fun x => f x - g x) (D + D') := by
  intro x y
  have := abs_sub (f x - f y) (g x - g y)
  have e : f x - g x - (f y - g y) = (f x - f y) - (g x - g y) := by ring
  rw [e]
  have h1 := hf x y
  have h2 := hg x y
  nlinarith

theorem Sb1WL.const_mul {f : E → ℝ} {D : ℝ} (hf : Sb1WL f D) (c : ℝ) : Sb1WL (fun x => c * f x) (|c| * D) := by
  intro x y
  rw [← mul_sub, abs_mul]
  have := mul_le_mul_of_nonneg_left (hf x y) (abs_nonneg c)
  linarith

theorem Sb1WL.sum {ι : Type*} (s : Finset ι) {f : ι → E → ℝ} {D : ι → ℝ} (h : ∀ i ∈ s, Sb1WL (f i) (D i)) :
    Sb1WL (fun x => ∑ i ∈ s, f i x) (∑ i ∈ s, D i) := by
  intro x y
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [Finset.sum_mul, Finset.sum_mul]
  refine (Finset.sum_le_sum fun i hi => h i hi x y).trans (le_of_eq rfl)

theorem Sb1WL.mul {f g : E → ℝ} {Af Lf Bg Cg Lg' : ℝ} (hAf : 0 ≤ Af) (hLf : 0 ≤ Lf) (hBg : 0 ≤ Bg) (hCg : 0 ≤ Cg)
    (hLg : 0 ≤ Lg') (hfb : ∀ x, |f x| ≤ Af) (hfl : ∀ x y, |f x - f y| ≤ Lf * ‖x - y‖)
    (hgb : ∀ x, |g x| ≤ Bg + Cg * ‖x‖) (hgl : ∀ x y, |g x - g y| ≤ Lg' * ‖x - y‖) :
    Sb1WL (fun x => f x * g x) (Lf * (Bg + Cg) + Af * Lg') := by
  intro x y
  have e : f x * g x - f y * g y = (f x - f y) * g x + f y * (g x - g y) := by ring
  rw [e]
  have hx := norm_nonneg x
  have hy := norm_nonneg y
  have hd := norm_nonneg (x - y)
  have h1 : |(f x - f y) * g x| ≤ Lf * (Bg + Cg) * (‖x - y‖ * (1 + ‖x‖ + ‖y‖)) := by
    rw [abs_mul]
    calc |f x - f y| * |g x| ≤ (Lf * ‖x - y‖) * (Bg + Cg * ‖x‖) :=
          mul_le_mul (hfl x y) (hgb x) (abs_nonneg _) (by positivity)
      _ ≤ _ := by nlinarith [mul_nonneg hd hx, mul_nonneg hLf hd, mul_nonneg (mul_nonneg hLf hd) hBg,
          mul_nonneg (mul_nonneg hLf hd) (mul_nonneg hCg hx), mul_nonneg (mul_nonneg hLf hd) (mul_nonneg hCg hy),
          mul_nonneg (mul_nonneg hLf hd) (mul_nonneg hBg hx), mul_nonneg (mul_nonneg hLf hd) (mul_nonneg hBg hy)]
  have h2 : |f y * (g x - g y)| ≤ Af * Lg' * (‖x - y‖ * (1 + ‖x‖ + ‖y‖)) := by
    rw [abs_mul]
    calc |f y| * |g x - g y| ≤ Af * (Lg' * ‖x - y‖) := mul_le_mul (hfb y) (hgl x y) (abs_nonneg _) hAf
      _ ≤ _ := by nlinarith [mul_nonneg hd hx, mul_nonneg hd hy, mul_nonneg (mul_nonneg hAf hLg) hd,
          mul_nonneg (mul_nonneg hAf hLg) (mul_nonneg hd hx), mul_nonneg (mul_nonneg hAf hLg) (mul_nonneg hd hy)]
  calc |(f x - f y) * g x + f y * (g x - g y)| ≤ |(f x - f y) * g x| + |f y * (g x - g y)| := abs_add_le _ _
    _ ≤ _ := by nlinarith

end HRS.MS.MfeConf
