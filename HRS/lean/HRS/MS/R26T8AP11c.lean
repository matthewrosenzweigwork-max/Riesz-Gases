import HRS.MS.R26T8AP11a
import HRS.MS.R26T8AP01
import HRS.MS.R26T8APot3

/-!
# S8.2 nonlocal layer, packets T8A.P11c/P11d: single annulus, kernel near the shell
Common estimate for `|z| <= 4R` (`r26t8a_p11_near`): the relative derivatives are moved to the annular source
(`r26t8a_near_conv`), bounded by P01, and the kernel mass over `ball 0 (7R)` is bounded by P11a.
P11c (`2|z| <= R/2`) and P11d (`R/4 <= |z| <= 4R`) are corollaries (P11d is in `R26T8AP11d`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

/-- The smooth global source of the annular potential. -/
def r26t8a_p11_src (chi : Euc d → ℝ) (R : ℝ) (F : Euc d → Euc d → ℝ) (Yw : Euc d × Euc d) : ℝ :=
  r26t8a_annulus chi R Yw.2 * (r26t8a_psiCut chi R Yw.2 * midPair F Yw.1 Yw.2)

theorem r26t8a_p11_src_eq {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {R : ℝ} (hR : 0 < R)
    (F : Euc d → Euc d → ℝ) (Y w : Euc d) :
    r26t8a_annulus chi R w * midPair F Y w = r26t8a_p11_src chi R F (Y, w) := by
  unfold r26t8a_p11_src
  by_cases h : ‖w‖ ≤ R / 2
  · simp only [r26t8a_annulus_zero_small hchi hR h, zero_mul]
  · push Not at h
    simp only [r26t8a_psiCut_one hchi hR (by linarith : R / 4 ≤ ‖w‖), one_mul]

theorem r26t8a_p11_src_contDiff {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {R : ℝ} (hR : 0 < R)
    {F : Euc d → Euc d → ℝ} {k : ℕ} (hF : ContDiffOn ℝ k (Function.uncurry F) {p | p.1 ≠ p.2}) :
    ContDiff ℝ k (r26t8a_p11_src chi R F) := by
  have ha : ContDiff ℝ (k : WithTop ℕ∞) (fun Yw : Euc d × Euc d => r26t8a_annulus chi R Yw.2) :=
    ((r26t8a_annulus_contDiff hchi hR).of_le (by exact_mod_cast le_top)).comp contDiff_snd
  exact ha.mul (r26t8a_gtilde_contDiff hchi hR hF)

theorem r26t8a_p11_src_vanish {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {R : ℝ} (hR : 0 < R)
    (F : Euc d → Euc d → ℝ) (Y w : Euc d) (hw : 2 * R < ‖w‖) : r26t8a_p11_src chi R F (Y, w) = 0 := by
  unfold r26t8a_p11_src
  rw [r26t8a_annulus_zero_large hchi hR hw.le, zero_mul]

theorem r26t8a_p11_src_nest {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {R : ℝ} (hR : 0 < R)
    (F : Euc d → Euc d → ℝ) (p q : ℕ) (X z : Euc d) :
    iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (fun w => r26t8a_annulus chi R w * midPair F Y w) z) X =
      r26t8a_nest p q (r26t8a_p11_src chi R F) X z := by
  unfold r26t8a_nest
  congr 1
  funext Y
  congr 1
  funext w
  exact r26t8a_p11_src_eq hchi hR F Y w

theorem r26t8a_p11_conv_form {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {R : ℝ} (hR : 0 < R)
    (alpha : ℝ) (F : Euc d → Euc d → ℝ) (Y z : Euc d) :
    r26t8a_annularRiesz alpha chi R F Y z =
      ∫ u, ‖u‖ ^ (alpha - (d : ℝ)) * r26t8a_p11_src chi R F (Y, z - u) := by
  unfold r26t8a_annularRiesz
  rw [← integral_sub_left_eq_self (fun u : Euc d => ‖u‖ ^ (alpha - (d : ℝ)) *
    r26t8a_p11_src chi R F (Y, z - u)) volume z]
  congr 1
  funext v
  rw [sub_sub_cancel, mul_assoc, r26t8a_p11_src_eq hchi hR]

theorem r26t8a_p11_near (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (alpha M sigma : ℝ)
    (halpha : 0 < alpha) (had : alpha < d) (hM : 0 ≤ M) (hsigma : 0 ≤ sigma)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A →
      Conormal k b M sigma A F → ∀ R : ℝ, 0 < R → R ≤ 1 → ∀ X z : Euc d, ‖z‖ ≤ 4 * R →
      ∀ p q : ℕ, p + q ≤ k →
        ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
          (r26t8a_annularRiesz alpha chi R F Y) z) X‖ ≤
          C * A * jbracket X ^ (2 * M) * (R ^ (alpha - sigma - q)) * (1 + |Real.log R|) ^ b := by
  obtain ⟨CK, hCK0, -, -, hKm⟩ := r26t8a_riesz_potential_jets d hd alpha halpha had 0
  obtain ⟨C1, hC10, hP1⟩ := r26t8a_annular_source k b M sigma hM hsigma chi hchi
  refine ⟨C1 * 3 ^ (2 * M) * CK * 7 ^ alpha, by positivity, ?_⟩
  intro F A hA hF R hR hR1 X z hz p q hpq
  obtain ⟨-, hbd⟩ := hP1 A hA F hF R hR hR1
  have hSd : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (r26t8a_p11_src chi R F) :=
    (r26t8a_p11_src_contDiff hchi hR hF.1).of_le (by exact_mod_cast hpq)
  have hfun : (fun Y => iteratedFDeriv ℝ q (r26t8a_annularRiesz alpha chi R F Y) z) =
      fun Y => iteratedFDeriv ℝ q (fun z' => ∫ u, ‖u‖ ^ (alpha - (d : ℝ)) *
        r26t8a_p11_src chi R F (Y, z' - u)) z := by
    funext Y
    congr 1
    funext z'
    exact r26t8a_p11_conv_form hchi hR alpha F Y z'
  rw [hfun]
  change ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => ∫ u, ‖u‖ ^ (alpha - (d : ℝ)) *
    r26t8a_p11_src chi R F (Yw.1, Yw.2 - u)) X z‖ ≤ _
  set L : ℝ := (1 + |Real.log R|) ^ b with hL
  have hL0 : 0 ≤ L := by positivity
  have hRq : 0 ≤ R ^ (-(sigma + (q : ℝ))) := Real.rpow_nonneg hR.le _
  have hjb0 : 0 ≤ jbracket X ^ (2 * M) := Real.rpow_nonneg (s83_jb_pos X).le _
  set B : ℝ := C1 * A * (3 ^ (2 * M) * jbracket X ^ (2 * M)) * R ^ (-(sigma + (q : ℝ))) * L with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hBd : ∀ i ≤ p, ∀ j ≤ q, ∀ Y : Euc d, ‖Y - X‖ < 1 → ∀ w : Euc d,
      ‖r26t8a_nest i j (r26t8a_p11_src chi R F) Y w‖ ≤ B := by
    intro i hi j hj Y hY w
    have h1 := hbd i j (by omega) Y w
    rw [r26t8a_p11_src_nest hchi hR F i j Y w] at h1
    refine h1.trans ?_
    have hj1 : R ^ (-(sigma + (j : ℝ))) ≤ R ^ (-(sigma + (q : ℝ))) :=
      Real.rpow_le_rpow_of_exponent_ge hR hR1 (by
        have : (j : ℝ) ≤ q := by exact_mod_cast hj
        linarith)
    have hjb : jbracket Y ≤ 3 * jbracket X := by
      have := r26t8a_p01_jb_shift (x := X) (y := Y - X) (by simpa using hY.le)
      simpa using this
    have hjb2 : jbracket Y ^ (2 * M) ≤ 3 ^ (2 * M) * jbracket X ^ (2 * M) := by
      rw [← Real.mul_rpow (by norm_num) (s83_jb_pos X).le]
      exact Real.rpow_le_rpow (s83_jb_pos Y).le hjb (by positivity)
    rw [hB]
    have hY0 : 0 ≤ jbracket Y ^ (2 * M) := Real.rpow_nonneg (s83_jb_pos Y).le _
    have h1 : C1 * A * jbracket Y ^ (2 * M) ≤ C1 * A * (3 ^ (2 * M) * jbracket X ^ (2 * M)) :=
      mul_le_mul_of_nonneg_left hjb2 (by positivity)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul h1 hj1 (Real.rpow_nonneg hR.le _) (by positivity)) hL0
  have hKi : ∀ r : ℝ, IntegrableOn (fun u : Euc d => ‖u‖ ^ (alpha - (d : ℝ))) (ball (0 : Euc d) r) := by
    intro r
    by_cases hr : 0 < r
    · exact (hKm r hr).1
    · rw [ball_eq_empty.2 (not_lt.1 hr)]
      exact integrableOn_empty
  have hρ7 : ‖z‖ + 2 * R < 7 * R := by linarith
  have hmain := r26t8a_near_conv (fun u : Euc d => ‖u‖ ^ (alpha - (d : ℝ)))
    (fun u => Real.rpow_nonneg (norm_nonneg _) _) (measurable_norm.pow_const _) hKi p q
    (r26t8a_p11_src chi R F) hSd (2 * R) (fun Y w hw => r26t8a_p11_src_vanish hchi hR F Y w hw) B X z
    hBd (7 * R) hρ7
  refine hmain.trans ?_
  have hmass := (hKm (7 * R) (by positivity)).2
  have h7 : (7 * R) ^ alpha = 7 ^ alpha * R ^ alpha := Real.mul_rpow (by norm_num) hR.le
  have hexp : R ^ (-(sigma + (q : ℝ))) * R ^ alpha = R ^ (alpha - sigma - q) := by
    rw [← Real.rpow_add hR]; congr 1; ring
  calc B * ∫ u in ball (0 : Euc d) (7 * R), ‖u‖ ^ (alpha - (d : ℝ))
      ≤ B * (CK * (7 * R) ^ alpha) := mul_le_mul_of_nonneg_left hmass hB0
    _ = C1 * 3 ^ (2 * M) * CK * 7 ^ alpha * A * jbracket X ^ (2 * M) * (R ^ (alpha - sigma - q)) * L := by
        rw [hB, h7, ← hexp]; ring

theorem r26t8a_p11c (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (alpha M sigma : ℝ)
    (halpha : 0 < alpha) (had : alpha < d) (hM : 0 ≤ M) (hsigma : 0 ≤ sigma) (hsd : sigma < d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A →
      Conormal k b M sigma A F → ∀ R : ℝ, 0 < R → R ≤ 1 → ∀ X z, z ≠ 0 → 2 * ‖z‖ ≤ R / 2 →
      ∀ p q : ℕ, p + q ≤ k →
        ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
          (r26t8a_annularRiesz alpha chi R F Y) z) X‖ ≤
          C * A * jbracket X ^ (2 * M) * (R ^ (alpha - sigma - q)) * (1 + |Real.log R|) ^ b := by
  obtain ⟨C, hC0, hC⟩ := r26t8a_p11_near d hd k b alpha M sigma halpha had hM hsigma chi hchi
  exact ⟨C, hC0, fun F A hA hF R hR hR1 X z _ hz p q hpq =>
    hC F A hA hF R hR hR1 X z (by linarith) p q hpq⟩

end HRS.MS.R26T8A
