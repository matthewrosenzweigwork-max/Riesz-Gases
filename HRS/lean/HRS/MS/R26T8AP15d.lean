import HRS.MS.R26T8AP15c
import HRS.MS.R26T8AG1
import HRS.MS.R26T8AP11a2

/-!
# S8.2 T8A P15d: three small conormal tools
* `r26t8a_conormal_far`: a conormal pair function that vanishes on `0 < |x - y| < 1` is conormal of any order and degree (same `A`);
* `r26t8a_conormal_mono_M`: weights are monotone;
* `r26t8a_conormal_const_mul`: constant multiples.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_one_le_jb (x : Euc d) : 1 ≤ jbracket x := by
  unfold jbracket
  exact Real.one_le_sqrt.2 (by nlinarith [sq_nonneg ‖x‖])

theorem r26t8a_pairWeight_nonneg (M : ℝ) (x y : Euc d) : 0 ≤ HRS.MS.Phase2S82.pairWeight M x y := by
  simp only [HRS.MS.Phase2S82.pairWeight]
  exact mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _) (Real.rpow_nonneg (s83_jb_pos _).le _)

theorem r26t8a_conormal_far {k b b' : ℕ} {M σ σ' A : ℝ} (hA : 0 ≤ A) {H : Euc d → Euc d → ℝ}
    (hH : Conormal k b M σ A H) (hz : ∀ x y : Euc d, x ≠ y → ‖x - y‖ < 1 → H x y = 0) :
    Conormal k b' M σ' A H := by
  refine ⟨hH.1, fun p q hpq X z hz0 => ?_⟩
  have hzn : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have hW := r26t8a_pairWeight_nonneg M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z)
  by_cases h1 : ‖z‖ < 1
  · have hmj : mixedJet p q H X z = 0 := by
      have e : r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair H Yw.1 Yw.2) X z =
          r26t8a_nest p q (fun _ : Euc d × Euc d => (0 : ℝ)) X z := by
        refine r26t8a_nest_congr_ball p q _ _ (ρ := min (1 - ‖z‖) ‖z‖) (lt_min (by linarith) hzn) X z
          (fun Y w hw => ?_)
        have hw1 : ‖w - z‖ < 1 - ‖z‖ := lt_of_lt_of_le hw (min_le_left _ _)
        have hw2 : ‖w - z‖ < ‖z‖ := lt_of_lt_of_le hw (min_le_right _ _)
        have : ‖w‖ < 1 := by
          have h3 := norm_sub_norm_le w z
          linarith
        have hw0 : w ≠ 0 := by
          intro h0
          rw [h0, zero_sub, norm_neg] at hw2
          exact lt_irrefl _ hw2
        have hxy : (Y + (1 / 2 : ℝ) • w) - (Y - (1 / 2 : ℝ) • w) = w := by module
        refine hz _ _ (fun h => hw0 ?_) (by rw [hxy]; exact this)
        rw [← hxy, h, sub_self]
      have e0 : r26t8a_nest p q (fun _ : Euc d × Euc d => (0 : ℝ)) X z = 0 := by
        unfold r26t8a_nest
        simp [iteratedFDeriv_fun_zero]
      exact e.trans e0
    rw [hmj, norm_zero]
    have : 0 ≤ (min 1 ‖z‖) ^ (-(σ' + q)) := Real.rpow_nonneg (le_min zero_le_one hzn.le) _
    positivity
  · have hm : min 1 ‖z‖ = 1 := min_eq_left (not_lt.1 h1)
    have := hH.2 p q hpq X z hz0
    rw [hm, Real.log_one] at this ⊢
    simpa using this

theorem r26t8a_conormal_mono_M {k b : ℕ} {M M' σ A : ℝ} (hA : 0 ≤ A) (hM : M ≤ M') {F : Euc d → Euc d → ℝ}
    (hF : Conormal k b M σ A F) : Conormal k b M' σ A F := by
  refine ⟨hF.1, fun p q hpq X z hz => ?_⟩
  refine (hF.2 p q hpq X z hz).trans ?_
  have hz0 : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hr0 : 0 < min 1 ‖z‖ := lt_min one_pos hz0
  have hE : 0 ≤ 1 + (min 1 ‖z‖) ^ (-(σ + (q : ℝ))) * (1 + |Real.log (min 1 ‖z‖)|) ^ b := by positivity
  have hW : HRS.MS.Phase2S82.pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) ≤
      HRS.MS.Phase2S82.pairWeight M' (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) := by
    simp only [HRS.MS.Phase2S82.pairWeight]
    exact mul_le_mul (Real.rpow_le_rpow_of_exponent_le (r26t8a_one_le_jb _) hM)
      (Real.rpow_le_rpow_of_exponent_le (r26t8a_one_le_jb _) hM) (Real.rpow_nonneg (s83_jb_pos _).le _)
      (Real.rpow_nonneg (s83_jb_pos _).le _)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hW hA) hE

theorem r26t8a_conormal_const_mul {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {k b : ℕ} {M σ A : ℝ} (hA : 0 ≤ A)
    (c : ℝ) {G : Euc d → Euc d → ℝ} (hG : Conormal k b M σ A G) :
    Conormal k b M σ (2 ^ k * ((k + 1 : ℝ) ^ 2 * |c| * A)) (fun x y => c * G x y) := by
  refine r26t8a_conormal_mul_x hchi hA (abs_nonneg c) (a := fun _ => c) contDiff_const (fun j hj x => ?_) hG
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · simp
  · rw [iteratedFDeriv_const_of_ne hj0.ne']
    simp

end HRS.MS.R26T8A
