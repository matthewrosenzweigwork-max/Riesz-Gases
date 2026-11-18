import HRS.Equilibrium.QuadraticVariance
import HRS.Energy.Commutator.RenormStjKernel
import HRS.Sections.Sec7Fields

/-!
# FC-B, part 1: the radial profile `Phi` and the comparison `w ≍ Phi(‖z‖)`

`fcbPhi s t = singEnvelope s (min t (1/2))` is a positive nonincreasing profile.  Under `EnvelopeConst s c`
the envelope `w = g + c` is comparable (above and below, off zero) to `fcbPhi s ‖z‖` where `‖z‖` is the sup
norm on the torus.  Packet prefix `fcb`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.Sec7.FCB

open HRS

/-- The radial profile `Phi(t) = 1 + t^{-s}` (`s > 0`), `1 + |log t|` (`s = 0`) for `t ≤ 1/2`, frozen for `t ≥ 1/2`. -/
def fcbPhi (s t : ℝ) : ℝ := singEnvelope s (min t (1 / 2))

theorem fcb_S_anti {s a b : ℝ} (hs : 0 ≤ s) (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1 / 2) :
    singEnvelope s b ≤ singEnvelope s a := by
  unfold singEnvelope
  by_cases h0 : s = 0
  · simp only [h0, if_true]
    have hb0 : 0 < b := ha.trans_le hab
    have h1 : Real.log a ≤ Real.log b := Real.log_le_log ha hab
    have h2 : Real.log b < 0 := Real.log_neg hb0 (by linarith)
    have h3 : Real.log a < 0 := by linarith
    rw [abs_of_neg h2, abs_of_neg h3]; linarith
  · simp only [h0, if_false]
    have := Real.rpow_le_rpow_of_nonpos ha hab (show -s ≤ 0 by linarith)
    linarith

theorem fcb_Phi_ge_one {s : ℝ} (hs : 0 ≤ s) {t : ℝ} (ht : 0 < t) : 1 ≤ fcbPhi s t :=
  (HRS.External.HeatSplit.one_le_singEnvelope (lt_min ht (by norm_num)) (min_le_right _ _) hs).1

theorem fcb_Phi_pos {s : ℝ} (hs : 0 ≤ s) {t : ℝ} (ht : 0 < t) : 0 < fcbPhi s t :=
  lt_of_lt_of_le one_pos (fcb_Phi_ge_one hs ht)

theorem fcb_Phi_anti {s : ℝ} (hs : 0 ≤ s) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    fcbPhi s b ≤ fcbPhi s a :=
  fcb_S_anti hs (lt_min ha (by norm_num)) (min_le_min_right _ hab) (min_le_right _ _)

theorem fcb_Phi_of_le {s t : ℝ} (ht : t ≤ 1 / 2) : fcbPhi s t = singEnvelope s t := by
  unfold fcbPhi; rw [min_eq_left ht]

/-- submultiplicativity of the profile. -/
theorem fcb_S_submul {s a b : ℝ} (hs : 0 ≤ s) (ha : 0 < a) (hb : 0 < b) :
    singEnvelope s (a * b) ≤ singEnvelope s a * singEnvelope s b := by
  unfold singEnvelope
  by_cases h0 : s = 0
  · simp only [h0, if_true]
    rw [Real.log_mul ha.ne' hb.ne']
    have := abs_add_le (Real.log a) (Real.log b)
    nlinarith [abs_nonneg (Real.log a), abs_nonneg (Real.log b)]
  · simp only [h0, if_false]
    rw [Real.mul_rpow ha.le hb.le]
    have h1 : 0 < a ^ (-s) := Real.rpow_pos_of_pos ha _
    have h2 : 0 < b ^ (-s) := Real.rpow_pos_of_pos hb _
    nlinarith

theorem fcb_Phi_submul {s : ℝ} (hs : 0 ≤ s) {t b : ℝ} (ht : 0 < t) (hb : 0 < b) (hb2 : b ≤ 1 / 2) :
    fcbPhi s (t * b) ≤ fcbPhi s t * fcbPhi s b := by
  set m := min t (1 / 2) with hm
  have hm0 : 0 < m := lt_min ht (by norm_num)
  have hmb : m * b ≤ min (t * b) (1 / 2) := by
    refine le_min ?_ ?_
    · exact mul_le_mul_of_nonneg_right (min_le_left _ _) hb.le
    · nlinarith [min_le_right t (1 / 2 : ℝ)]
  have h1 : fcbPhi s (t * b) ≤ singEnvelope s (m * b) := by
    unfold fcbPhi
    exact fcb_S_anti hs (mul_pos hm0 hb) hmb (min_le_right _ _)
  refine h1.trans ?_
  rw [fcb_Phi_of_le hb2]
  exact fcb_S_submul hs hm0 hb

/-- halving the argument costs a constant. -/
theorem fcb_Phi_half {s : ℝ} (hs : 0 ≤ s) {t : ℝ} (ht : 0 < t) :
    fcbPhi s (t / 2) ≤ fcbPhi s (1 / 2) * fcbPhi s t := by
  have := fcb_Phi_submul hs ht (show (0 : ℝ) < 1 / 2 by norm_num) le_rfl
  rw [show t / 2 = t * (1 / 2) by ring]
  linarith

/-- division by a natural number `m ≥ 1`. -/
theorem fcb_Phi_div {s : ℝ} (hs : 0 ≤ s) {t : ℝ} (ht : 0 < t) {m : ℕ} (hm : 2 ≤ m) :
    fcbPhi s (t / m) ≤ fcbPhi s (1 / m) * fcbPhi s t := by
  have hm0 : (0 : ℝ) < m := by positivity
  have hb : (1 : ℝ) / m ≤ 1 / 2 := by
    apply one_div_le_one_div_of_le (by norm_num); exact_mod_cast hm
  have := fcb_Phi_submul hs ht (show (0 : ℝ) < 1 / m by positivity) hb
  rw [show t / m = t * (1 / m) by ring]
  linarith

theorem fcb_selfScale_le {d : ℕ} {s r : ℝ} (hs : 0 ≤ s) (hr : 0 < r) :
    HRS.Commutator.selfScale d s r ≤ fcbPhi s r := by
  unfold HRS.Commutator.selfScale fcbPhi singEnvelope
  by_cases h0 : s = 0
  · simp only [h0, if_true]
    by_cases hr2 : r ≤ 1 / 2
    · rw [min_eq_left hr2]
      have := neg_le_abs (Real.log r); linarith
    · push Not at hr2
      rw [min_eq_right hr2.le]
      have h1 : Real.log (1 / 2) ≤ Real.log r := Real.log_le_log (by norm_num) hr2.le
      have h2 : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
        rw [one_div, Real.log_inv]
      have h4 : |Real.log (1 / 2 : ℝ)| = Real.log 2 := by
        rw [h2, abs_neg, abs_of_pos (Real.log_pos (show (1 : ℝ) < 2 by norm_num))]
      rw [h2] at h1
      rw [h4]
      linarith [Real.log_pos (show (1 : ℝ) < 2 by norm_num), Real.log_two_lt_d9]
  · simp only [h0, if_false]
    have hm0 : 0 < min r (1 / 2) := lt_min hr (by norm_num)
    have := Real.rpow_le_rpow_of_nonpos hm0 (min_le_left r (1 / 2)) (show -s ≤ 0 by linarith)
    linarith

theorem fcb_eucDist_eq_tdist {d : ℕ} (z : Torus d) : Torus.eucDist z 0 = KernelGrad.tdist z 0 := by
  rw [KernelGrad.tdist_zero_right, EuclideanSpace.norm_eq]
  unfold Torus.eucDist
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.zero_apply, sub_zero, KernelGrad.norm_apply_eq]
  simp [Real.norm_eq_abs, sq_abs]

/-- The two-sided comparison of the envelope `w = g + c` with the profile at the Euclidean distance. -/
theorem fcb_w_comp {d : ℕ} (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ)) {c : ℝ}
    (hc : HRS.Sec7.EnvelopeConst (d := d) s c) :
    ∃ c1 c2 : ℝ, 0 < c1 ∧ 0 < c2 ∧ ∀ z : Torus d, z ≠ 0 →
      c1 * fcbPhi s (Torus.eucDist z 0) ≤ periodicRiesz d s z + c ∧
      periodicRiesz d s z + c ≤ c2 * fcbPhi s (Torus.eucDist z 0) := by
  obtain ⟨C1, hC1⟩ := HRS.Quad.periodicRiesz_lower_env (d := d) hd hs0 hs
  obtain ⟨C2, hC20, hC2⟩ := HRS.Commutator.Stj.periodicRiesz_upper (d := d) (by omega) hs0 hs
  set K : ℝ := max (C1 - c) 0 with hK
  have hK0 : 0 ≤ K := le_max_right _ _
  have hS0 : 1 ≤ fcbPhi s (1 / 2) := fcb_Phi_ge_one hs0 (by norm_num)
  refine ⟨1 / max (K + 2) (fcbPhi s (1 / 2)), 1 + C2 + |c|, ?_, ?_, fun z hz => ?_⟩
  · have : 0 < max (K + 2) (fcbPhi s (1 / 2)) := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    positivity
  · positivity
  have hr : 0 < Torus.eucDist z 0 := by
    rw [fcb_eucDist_eq_tdist]; exact KernelGrad.tdist_pos hz
  have hwz := hc z hz
  constructor
  · set r := Torus.eucDist z 0 with hrdef
    set M := max (K + 2) (fcbPhi s (1 / 2)) with hMdef
    have hM : 0 < M := lt_of_lt_of_le (by linarith) (le_max_left _ _)
    have hwz0 : 0 ≤ periodicRiesz d s z + c := by linarith
    rw [one_div, inv_mul_eq_div, div_le_iff₀ hM]
    have hKM : K + 2 ≤ M := le_max_left _ _
    have hSM : fcbPhi s (1 / 2) ≤ M := le_max_right _ _
    by_cases hr2 : r ≤ 1 / 2
    · have hΦ : fcbPhi s r = singEnvelope s r := fcb_Phi_of_le hr2
      have hlow := hC1 z hz
      unfold HRS.Quad.envT at hlow
      rw [← hrdef] at hlow
      rw [hΦ]
      by_cases hcase : singEnvelope s r ≤ K + 1
      · calc singEnvelope s r ≤ (K + 2) * 1 := by linarith
          _ ≤ (K + 2) * (periodicRiesz d s z + c) := by gcongr
          _ ≤ (periodicRiesz d s z + c) * M := by nlinarith
      · push Not at hcase
        have hK' : C1 - c ≤ K := le_max_left _ _
        have h2 : singEnvelope s r - K ≤ periodicRiesz d s z + c := by linarith
        have h3 : singEnvelope s r ≤ (K + 2) * (singEnvelope s r - K) := by nlinarith
        calc singEnvelope s r ≤ (K + 2) * (singEnvelope s r - K) := h3
          _ ≤ (K + 2) * (periodicRiesz d s z + c) := by gcongr
          _ ≤ (periodicRiesz d s z + c) * M := by nlinarith
    · push Not at hr2
      have hΦ : fcbPhi s r = fcbPhi s (1 / 2) := by
        unfold fcbPhi; rw [min_eq_right hr2.le, min_self]
      rw [hΦ]
      calc fcbPhi s (1 / 2) ≤ fcbPhi s (1 / 2) * (periodicRiesz d s z + c) := by nlinarith
        _ ≤ M * (periodicRiesz d s z + c) := by gcongr
        _ = _ := by ring
  · have hup := hC2 z hz
    rw [← fcb_eucDist_eq_tdist] at hup
    have h1 := fcb_selfScale_le (d := d) hs0 hr
    have h2 := fcb_Phi_ge_one hs0 hr
    have h3 := le_abs_self c
    have h4 : (C2 + |c|) * 1 ≤ (C2 + |c|) * fcbPhi s (Torus.eucDist z 0) :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    nlinarith

end HRS.MC.Sec7.FCB
