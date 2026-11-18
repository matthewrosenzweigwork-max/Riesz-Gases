import Mathlib
import HRS.MS.PoisMaxAux1

open Filter Topology Set intervalIntegral
open scoped ContDiff

/-!
# POIS-MAXP (part 2): the comparison function `f` of the doubling argument (D1)

Constants of the packet (`Kc = q + Mb + 1`, `R = 1 + 4 Mb/q`):
`pm_kappa = exp(-(Kc+1)(R+1)²/2)`, `pm_c0 = pm_kappa * min 1 (q/2)`, and the drift coefficient
`pm_c r = Kc r` for `r < R`, `-q r/2` for `r ≥ R`.

Constant algebra (flag F1, re-checked).  With `f' = exp(-a g)`, `a = (Kc+1)/4`, one has
`4 f'' = -(Kc+1) g' f'`, and `g' ≥ r` on `[0, R]` gives `4f'' + Kc r f' ≤ -r f'` on `r < R`; this is the
consistent choice `(Kc+1)/4` (the value `(K+1)/8` of the plan does not close).  Adjustments with respect
to the sketch (documented, harmless since the constants are only used existentially downstream):
* The cutoff `η` is replaced by the explicit smooth bounded function
  `g r = 2N² r²/(N²+r²)`, `N = R+1` (so `g' = 4N⁴ r/(N²+r²)² ≥ r` for `0 ≤ r ≤ N`, `0 ≤ g ≤ 2N²`).
  This makes `f` smooth (`ContDiff ℝ ∞`) on all of `ℝ` and the inequality true on ALL of `r ≥ 0`
  (including `r = R`), not only off `r = R`.
* The lower bound `κ` is `exp(-(Kc+1)(R+1)²/2)` instead of `exp(-(Kc+1)R²/8)`: with a `C²` cutoff
  that equals `1` on `[0,R]`, the exact `R²/8` constant is not attainable by `f' = exp(-(Kc+1)G/4)`.
* The hypothesis `0 ≤ Mb` is added (so `Kc > 0`, `R ≥ 1`); for `Mb < 0` all downstream hypotheses are void.
-/

namespace HRS.MS.PoisMax

/-- `K_c = q + Mb + 1`. -/
noncomputable def pm_Kc (q Mb : ℝ) : ℝ := q + Mb + 1
/-- `R = 1 + 4 Mb / q`. -/
noncomputable def pm_R (q Mb : ℝ) : ℝ := 1 + 4 * Mb / q
/-- `κ`. -/
noncomputable def pm_kappa (q Mb : ℝ) : ℝ :=
  Real.exp (-((pm_Kc q Mb + 1) * (pm_R q Mb + 1) ^ 2 / 2))
/-- `c0 = κ min(1, q/2)`. -/
noncomputable def pm_c0 (q Mb : ℝ) : ℝ := pm_kappa q Mb * min 1 (q / 2)
/-- the drift coefficient `c(r)` of the radial inequality. -/
noncomputable def pm_c (q Mb r : ℝ) : ℝ :=
  if r < pm_R q Mb then pm_Kc q Mb * r else -(q * r / 2)

/-- the bounded profile `g r = 2N² r²/(N²+r²)`. -/
noncomputable def pm_g (N r : ℝ) : ℝ := 2 * N ^ 2 * r ^ 2 / (N ^ 2 + r ^ 2)

theorem pm_g_hasDerivAt {N : ℝ} (hN : 0 < N) (r : ℝ) :
    HasDerivAt (pm_g N) (4 * N ^ 4 * r / (N ^ 2 + r ^ 2) ^ 2) r := by
  have hpos : N ^ 2 + r ^ 2 ≠ 0 := by positivity
  have h1 : HasDerivAt (fun r : ℝ => 2 * N ^ 2 * r ^ 2) (2 * N ^ 2 * (2 * r)) r := by
    simpa using ((hasDerivAt_pow 2 r).const_mul (2 * N ^ 2))
  have h2 : HasDerivAt (fun r : ℝ => N ^ 2 + r ^ 2) (2 * r) r := by
    simpa using ((hasDerivAt_pow 2 r).const_add (N ^ 2))
  have h3 := h1.div h2 hpos
  have e : pm_g N = (fun r : ℝ => 2 * N ^ 2 * r ^ 2) / (fun r : ℝ => N ^ 2 + r ^ 2) := by
    funext r; simp [pm_g]
  rw [e]
  convert h3 using 1
  field_simp
  ring

theorem pm_g_nonneg (N r : ℝ) : 0 ≤ pm_g N r := by unfold pm_g; positivity

theorem pm_g_le {N : ℝ} (hN : 0 < N) (r : ℝ) : pm_g N r ≤ 2 * N ^ 2 := by
  unfold pm_g
  rw [div_le_iff₀ (by positivity)]
  nlinarith [sq_nonneg N, sq_nonneg r, mul_nonneg (sq_nonneg N) (sq_nonneg r)]

theorem pm_g_contDiff {N : ℝ} (hN : 0 < N) : ContDiff ℝ ∞ (pm_g N) := by
  unfold pm_g
  refine ContDiff.div (by fun_prop) (by fun_prop) fun r => by positivity

theorem pm_g_deriv_ge {N r : ℝ} (hN : 0 < N) (hr0 : 0 ≤ r) (hrN : r ≤ N) :
    r ≤ 4 * N ^ 4 * r / (N ^ 2 + r ^ 2) ^ 2 := by
  rw [le_div_iff₀ (by positivity)]
  have h1 : (N ^ 2 + r ^ 2) ^ 2 ≤ 4 * N ^ 4 := by
    nlinarith [mul_nonneg (sq_nonneg N) (sq_nonneg r), sq_nonneg r, pow_le_pow_left₀ hr0 hrN 2]
  nlinarith [mul_le_mul_of_nonneg_left h1 hr0]

theorem pm_g_deriv_nonneg {N r : ℝ} (hN : 0 < N) (hr0 : 0 ≤ r) :
    0 ≤ 4 * N ^ 4 * r / (N ^ 2 + r ^ 2) ^ 2 := by positivity

/-- D1: the comparison function of the doubling-of-variables argument.  `f` is smooth, `f 0 = 0`,
`κ ≤ f' ≤ 1`, `κ r ≤ f r ≤ r` on `r ≥ 0`, and `4 f'' + c f' ≤ -c0 f` for ALL `r ≥ 0`. -/
theorem pm_ffun {q Mb : ℝ} (hq : 0 < q) (hMb : 0 ≤ Mb) :
    ∃ f : ℝ → ℝ, ContDiff ℝ ∞ f ∧ f 0 = 0 ∧
      (∀ r : ℝ, 0 ≤ r → pm_kappa q Mb ≤ deriv f r ∧ deriv f r ≤ 1) ∧
      (∀ r : ℝ, 0 ≤ r → pm_kappa q Mb * r ≤ f r ∧ f r ≤ r) ∧
      ∀ r : ℝ, 0 ≤ r →
        4 * deriv (deriv f) r + pm_c q Mb r * deriv f r ≤ -(pm_c0 q Mb * f r) := by
  have hKc : 0 < pm_Kc q Mb := by unfold pm_Kc; linarith
  have hR : 0 ≤ pm_R q Mb := by
    unfold pm_R
    have : 0 ≤ 4 * Mb / q := by positivity
    linarith
  set N : ℝ := pm_R q Mb + 1 with hNdef
  have hN : 0 < N := by rw [hNdef]; linarith
  set a : ℝ := (pm_Kc q Mb + 1) / 4 with hadef
  have ha : 0 < a := by rw [hadef]; linarith
  set φ : ℝ → ℝ := fun r => Real.exp (-(a * pm_g N r)) with hφdef
  have hφc : ContDiff ℝ ∞ φ :=
    Real.contDiff_exp.comp (((contDiff_const.mul (pm_g_contDiff hN))).neg)
  have hφ' : ∀ r, HasDerivAt φ (-(a * (4 * N ^ 4 * r / (N ^ 2 + r ^ 2) ^ 2)) * φ r) r := by
    intro r
    have := (((pm_g_hasDerivAt hN r).const_mul a).neg).exp
    simpa [hφdef, mul_comm] using this
  set f : ℝ → ℝ := fun r => ∫ s in (0:ℝ)..r, φ s with hfdef
  have hf' : ∀ r, HasDerivAt f (φ r) r := fun r =>
    (hφc.continuous.integral_hasStrictDerivAt 0 r).hasDerivAt
  have hdf : deriv f = φ := funext fun r => (hf' r).deriv
  have hfc : ContDiff ℝ ∞ f := by
    rw [contDiff_infty_iff_deriv]
    exact ⟨fun r => (hf' r).differentiableAt, by rw [hdf]; exact hφc⟩
  have hφpos : ∀ r, 0 < φ r := fun r => Real.exp_pos _
  have hφle : ∀ r, φ r ≤ 1 := fun r => by
    rw [hφdef]; simp only
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.2 (by nlinarith [pm_g_nonneg N r])
  have hφge : ∀ r, pm_kappa q Mb ≤ φ r := fun r => by
    rw [hφdef]; simp only [pm_kappa]
    refine Real.exp_le_exp.2 ?_
    have := pm_g_le hN r
    have h2 : a * pm_g N r ≤ a * (2 * N ^ 2) := mul_le_mul_of_nonneg_left this ha.le
    have h3 : a * (2 * N ^ 2) = (pm_Kc q Mb + 1) * (pm_R q Mb + 1) ^ 2 / 2 := by
      rw [hadef, hNdef]; ring
    linarith
  have hκpos : 0 < pm_kappa q Mb := Real.exp_pos _
  have hκle : pm_kappa q Mb ≤ 1 := by
    simp only [pm_kappa]
    refine Real.exp_le_one_iff.2 ?_
    have : 0 ≤ (pm_Kc q Mb + 1) * (pm_R q Mb + 1) ^ 2 / 2 := by positivity
    linarith
  have hint : ∀ r, 0 ≤ r → pm_kappa q Mb * r ≤ f r ∧ f r ≤ r := by
    intro r hr
    have hcI : ∀ h : ℝ → ℝ, Continuous h → IntervalIntegrable h MeasureTheory.volume 0 r :=
      fun h hh => hh.intervalIntegrable _ _
    constructor
    · have := intervalIntegral.integral_mono_on hr (hcI (fun _ => pm_kappa q Mb) continuous_const)
        (hcI φ hφc.continuous) (fun s _ => hφge s)
      simpa [hfdef, mul_comm] using this
    · have := intervalIntegral.integral_mono_on hr (hcI φ hφc.continuous)
        (hcI (fun _ => (1:ℝ)) continuous_const) (fun s _ => hφle s)
      simpa [hfdef] using this
  refine ⟨f, hfc, by simp [hfdef], ?_, hint, ?_⟩
  · intro r hr; rw [hdf]; exact ⟨hφge r, hφle r⟩
  · intro r hr
    have hd2 : deriv (deriv f) r = -(a * (4 * N ^ 4 * r / (N ^ 2 + r ^ 2) ^ 2)) * φ r := by
      rw [hdf]; exact (hφ' r).deriv
    rw [hd2, hdf]
    obtain ⟨hf1, hf2⟩ := hint r hr
    have hf0 : 0 ≤ f r := le_trans (by positivity) hf1
    have hc0κ : pm_c0 q Mb ≤ pm_kappa q Mb := by
      simp only [pm_c0]
      nlinarith [min_le_left (1:ℝ) (q / 2)]
    have hc0q : pm_c0 q Mb ≤ pm_kappa q Mb * (q / 2) := by
      simp only [pm_c0]
      nlinarith [min_le_right (1:ℝ) (q / 2)]
    have hg' := pm_g_deriv_nonneg (N := N) (r := r) hN hr
    have hφr := hφpos r
    have hφκ := hφge r
    unfold pm_c
    split_ifs with hrR
    · have hrN : r ≤ N := by rw [hNdef]; linarith
      have hge := pm_g_deriv_ge hN hr hrN
      have key : 4 * (-(a * (4 * N ^ 4 * r / (N ^ 2 + r ^ 2) ^ 2)) * φ r) + pm_Kc q Mb * r * φ r
          ≤ -(r * φ r) := by
        have : (4 * a) * (4 * N ^ 4 * r / (N ^ 2 + r ^ 2) ^ 2) ≥ (pm_Kc q Mb + 1) * r := by
          rw [show 4 * a = pm_Kc q Mb + 1 by rw [hadef]; ring]
          exact mul_le_mul_of_nonneg_left hge (by linarith)
        nlinarith [mul_le_mul_of_nonneg_right this hφr.le]
      have h2 : pm_kappa q Mb * r ≤ r * φ r := by nlinarith
      have h3 : pm_c0 q Mb * f r ≤ pm_kappa q Mb * r := by
        nlinarith [mul_le_mul_of_nonneg_right hc0κ hf0, mul_le_mul_of_nonneg_left hf2 hκpos.le]
      nlinarith
    · have key : 4 * (-(a * (4 * N ^ 4 * r / (N ^ 2 + r ^ 2) ^ 2)) * φ r) + -(q * r / 2) * φ r
          ≤ -(q * r / 2 * φ r) := by
        have : 0 ≤ a * (4 * N ^ 4 * r / (N ^ 2 + r ^ 2) ^ 2) := by positivity
        nlinarith [mul_nonneg this hφr.le]
      have h2 : pm_kappa q Mb * (q / 2) * r ≤ q * r / 2 * φ r := by
        nlinarith [mul_le_mul_of_nonneg_left hφκ (show 0 ≤ q * r / 2 by positivity)]
      have h3 : pm_c0 q Mb * f r ≤ pm_kappa q Mb * (q / 2) * r := by
        nlinarith [mul_le_mul_of_nonneg_right hc0q hf0,
          mul_le_mul_of_nonneg_left hf2 (show 0 ≤ pm_kappa q Mb * (q / 2) by positivity)]
      nlinarith

end HRS.MS.PoisMax
