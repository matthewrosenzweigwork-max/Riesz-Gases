import HRS.MS.R26T8AP07r
import HRS.MS.R26T8AP11wt

/-!
# S8.2 local Newton layer, packet T8A.P07 (part s): mixed jets of the raw Newton integral (`0 <= sigma < d`)
`r26t8a_p07_raw_mid`: `midPair (rawNewton nu chi F) Y w = chi w * N(Y,w)` with `N = sum_n annularNewton (1/2)^n F Y w` for `w != 0`.
`r26t8a_p07_raw_jet`: the weighted mixed-jet bound of `rawNewton nu chi F` of the contract (`Conormal k (b+1) M (sigma-2) (C*A)`, bound part).
-/

set_option autoImplicit false
noncomputable section
open Filter Topology Metric
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

namespace HRS.MS.R26T8A

variable {d : ℕ}

theorem r26t8a_p07_raw_mid_int (nu : ℝ) (chi : Euc d → ℝ) (F : Euc d → Euc d → ℝ) (Y w : Euc d) :
    midPair (rawNewton nu chi F) Y w = chi w * ∫ z, newtonKernel d nu (w - z) * chi z * midPair F Y z := by
  unfold midPair rawNewton
  have e1 : Y + (1 / 2 : ℝ) • w - (Y - (1 / 2 : ℝ) • w) = w := by module
  have e2 : (1 / 2 : ℝ) • (Y + (1 / 2 : ℝ) • w + (Y - (1 / 2 : ℝ) • w)) = Y := by module
  rw [e1, e2]
  rfl

theorem r26t8a_p07_raw_mid (hd : 2 ≤ d) (k b : ℕ) (nu M σ : ℝ) (hnu : 0 < nu) (hM : 0 ≤ M) (hσd : σ < d) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) {A : ℝ} (hA : 0 ≤ A) {F : Euc d → Euc d → ℝ}
    (hF : ConormalP k b M σ A F) (Y w : Euc d) (hw : w ≠ 0) :
    midPair (rawNewton nu chi F) Y w =
      chi w * ∑' n : ℕ, r26t8a_annularNewton nu chi (((1 : ℝ) / 2) ^ n) F Y w := by
  rw [r26t8a_p07_raw_mid_int]
  by_cases h4 : ‖w‖ ≤ 4
  · rw [((r26t8a_p07_series_repr hd k b nu M σ hnu hM hσd hchi hA hF Y w hw).2 h4).tsum_eq]
  · rw [hchi.2.2.2.2 w (by linarith [not_le.1 h4]), zero_mul, zero_mul]

theorem r26t8a_p07_envcmp (b : ℕ) (σ : ℝ) (q : ℕ) {r : ℝ} (hr : 0 < r) (hr2 : r ≤ 2) :
    1 + r ^ (2 - σ - (q : ℝ)) * (1 + |Real.log r|) ^ (b + 1) ≤
      (1 + 2 ^ (2 + |σ|) * 2 ^ (b + 1)) * (1 + (min 1 r) ^ (-((σ - 2) + (q : ℝ))) * (1 + |Real.log (min 1 r)|) ^ (b + 1)) := by
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  rcases le_total r 1 with h1 | h1
  · rw [min_eq_right h1]
    have e : -((σ - 2) + (q : ℝ)) = 2 - σ - (q : ℝ) := by ring
    rw [e]
    have : 0 ≤ r ^ (2 - σ - (q : ℝ)) * (1 + |Real.log r|) ^ (b + 1) := by positivity
    have hT : (0 : ℝ) ≤ 2 ^ (2 + |σ|) * 2 ^ (b + 1) := by positivity
    nlinarith [mul_nonneg hT (by linarith : (0 : ℝ) ≤ 1 + r ^ (2 - σ - (q : ℝ)) * (1 + |Real.log r|) ^ (b + 1))]
  · rw [min_eq_left h1]
    simp only [Real.one_rpow, Real.log_one, abs_zero, add_zero, one_pow, mul_one]
    have hpow : r ^ (2 - σ - (q : ℝ)) ≤ 2 ^ (2 + |σ|) := by
      by_cases he : 0 ≤ 2 - σ - (q : ℝ)
      · calc r ^ (2 - σ - (q : ℝ)) ≤ 2 ^ (2 - σ - (q : ℝ)) := Real.rpow_le_rpow hr.le hr2 he
          _ ≤ 2 ^ (2 + |σ|) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [neg_le_abs σ])
      · exact (Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith)).trans
          (Real.one_le_rpow (by norm_num) (by positivity))
    have hlog : 1 + |Real.log r| ≤ 2 := by
      have h2 : Real.log r ≤ Real.log 2 := Real.log_le_log hr hr2
      have h3 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
      rw [abs_of_nonneg (Real.log_nonneg h1)]; linarith
    have hL : (1 + |Real.log r|) ^ (b + 1) ≤ 2 ^ (b + 1) := pow_le_pow_left₀ (by positivity) hlog _
    have : r ^ (2 - σ - (q : ℝ)) * (1 + |Real.log r|) ^ (b + 1) ≤ 2 ^ (2 + |σ|) * 2 ^ (b + 1) :=
      mul_le_mul hpow hL (by positivity) (by positivity)
    have hT : (0 : ℝ) ≤ 2 ^ (2 + |σ|) * 2 ^ (b + 1) := by positivity
    nlinarith

theorem r26t8a_p07_raw_jet (hd : 2 ≤ d) (k b : ℕ) (nu M σ : ℝ) (hnu : 0 < nu) (hM : 0 ≤ M) (hσd : σ < d) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 0 ≤ A → ∀ F : Euc d → Euc d → ℝ, ConormalP k b M σ A F →
      ∀ p q : ℕ, p + q ≤ k → ∀ X z : Euc d, z ≠ 0 →
        ‖mixedJet p q (rawNewton nu chi F) X z‖ ≤
          C * A * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) *
            (1 + (min 1 ‖z‖) ^ (-((σ - 2) + (q : ℝ))) * (1 + |Real.log (min 1 ‖z‖)|) ^ (b + 1)) := by
  obtain ⟨CN, hCN0, hCN⟩ := r26t8a_p07_N_nest hd k b nu M σ hnu hM hσd hchi
  obtain ⟨B, hB0, hB⟩ := r26t8a_chi_jets hchi k
  set cmp : ℝ := 1 + 2 ^ (2 + |σ|) * 2 ^ (b + 1) with hcmp
  refine ⟨CN * B * 4 ^ k * 3 ^ (2 * M) * cmp, by positivity, fun A hA F hF p q hpq X z hz => ?_⟩
  have hr : 0 < ‖z‖ := norm_pos_iff.2 hz
  have hmj : mixedJet p q (rawNewton nu chi F) X z =
      r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair (rawNewton nu chi F) Yw.1 Yw.2) X z := rfl
  have hjb0 : 0 ≤ jbracket X ^ (2 * M) := Real.rpow_nonneg (s83_jb_pos X).le _
  have hpw0 : 0 ≤ pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) := by
    unfold pairWeight
    exact mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _) (Real.rpow_nonneg (s83_jb_pos _).le _)
  by_cases hz2 : 2 < ‖z‖
  · -- the jet vanishes
    have hz0 : r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair (rawNewton nu chi F) Yw.1 Yw.2) X z =
        r26t8a_nest p q (fun _ => (0 : ℝ)) X z :=
      r26t8a_p07_congr_ball p q _ _ (by linarith : 0 < ‖z‖ - 2) X z fun Y w hw => by
        have h1 : 2 < ‖w‖ := by
          have := norm_sub_norm_le z w
          rw [norm_sub_rev] at this
          linarith
        rw [r26t8a_p07_raw_mid_int, hchi.2.2.2.2 w h1.le]; simp
    rw [hmj, hz0]
    have : r26t8a_nest p q (fun _ : Euc d × Euc d => (0 : ℝ)) X z = 0 := by
      unfold r26t8a_nest
      have : (fun Y : Euc d => iteratedFDeriv ℝ q (fun _ : Euc d => (0 : ℝ)) z) = fun _ => 0 := by
        funext Y; simp
      simp [this]
    rw [this, norm_zero]
    have : 0 ≤ (1 + (min 1 ‖z‖) ^ (-((σ - 2) + (q : ℝ))) * (1 + |Real.log (min 1 ‖z‖)|) ^ (b + 1)) :=
      add_nonneg zero_le_one (mul_nonneg (Real.rpow_nonneg (le_min zero_le_one hr.le) _) (by positivity))
    have : 0 ≤ CN * B * 4 ^ k * 3 ^ (2 * M) * cmp := by positivity
    positivity
  · push Not at hz2
    set r : ℝ := ‖z‖ with hrdef
    have hmid : r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair (rawNewton nu chi F) Yw.1 Yw.2) X z =
        r26t8a_nest p q (fun Yw : Euc d × Euc d =>
          chi Yw.2 * ∑' n : ℕ, r26t8a_annularNewton nu chi (((1 : ℝ) / 2) ^ n) F Yw.1 Yw.2) X z :=
      r26t8a_p07_congr_ball p q _ _ hr X z fun Y w hw => by
        refine r26t8a_p07_raw_mid hd k b nu M σ hnu hM hσd hchi hA hF Y w ?_
        intro h0
        rw [h0, zero_sub, norm_neg] at hw
        exact lt_irrefl _ hw
    rw [hmj, hmid]
    have hNc := (r26t8a_p07_N_contDiffOn hd k b nu M σ hnu hM hσd hchi hA hF).of_le
      (by exact_mod_cast hpq : ((p + q : ℕ) : WithTop ℕ∞) ≤ (k : WithTop ℕ∞))
    refine (r26t8a_p07_local_product p q (hchi.1.of_le (by exact_mod_cast le_top)) hNc X z hr hz2).trans ?_
    set E : ℝ := r ^ (2 - σ - (q : ℝ)) * (1 + |Real.log r|) ^ (b + 1) with hE
    have hE0 : 0 ≤ E := by rw [hE]; positivity
    set H : ℝ := jbracket X ^ (2 * M) with hH
    have hterm : ∀ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * ‖iteratedFDeriv ℝ i chi z‖ *
        ‖r26t8a_nest p (q - i) (fun Yw : Euc d × Euc d =>
          ∑' n : ℕ, r26t8a_annularNewton nu chi (((1 : ℝ) / 2) ^ n) F Yw.1 Yw.2) X z‖ ≤
        (q.choose i : ℝ) * (2 ^ q * (B * (CN * A * H * (1 + E)))) := by
      intro i hi
      have hiq : i ≤ q := by have := Finset.mem_range.1 hi; omega
      have hn := hCN A hA F hF X z hr (by linarith) p (q - i) (by omega)
      have hB1 := hB i (by omega) z
      have hexp : 2 - σ - (((q - i : ℕ) : ℝ)) = (2 - σ - (q : ℝ)) + (i : ℝ) := by
        rw [Nat.cast_sub hiq]; ring
      rw [hexp, Real.rpow_add hr, Real.rpow_natCast] at hn
      have hri : r ^ i ≤ 2 ^ i := pow_le_pow_left₀ hr.le hz2 i
      have hLb : 0 ≤ (1 + |Real.log r|) ^ (b + 1) := by positivity
      have hrp : 0 ≤ r ^ (2 - σ - (q : ℝ)) := Real.rpow_nonneg hr.le _
      have h2i : (2 : ℝ) ^ i ≤ 2 ^ q := pow_le_pow_right₀ (by norm_num) hiq
      have hk1 : 1 + r ^ (2 - σ - (q : ℝ)) * (r ^ i) * (1 + |Real.log r|) ^ (b + 1) ≤ 2 ^ q * (1 + E) := by
        have a1 : r ^ (2 - σ - (q : ℝ)) * (r ^ i) * (1 + |Real.log r|) ^ (b + 1) ≤
            2 ^ q * (r ^ (2 - σ - (q : ℝ)) * (1 + |Real.log r|) ^ (b + 1)) := by
          calc _ = (r ^ (2 - σ - (q : ℝ)) * (1 + |Real.log r|) ^ (b + 1)) * r ^ i := by ring
            _ ≤ (r ^ (2 - σ - (q : ℝ)) * (1 + |Real.log r|) ^ (b + 1)) * 2 ^ q :=
                mul_le_mul_of_nonneg_left (hri.trans h2i) (by positivity)
            _ = _ := by ring
        have a2 : (1 : ℝ) ≤ 2 ^ q := one_le_pow₀ (by norm_num)
        nlinarith
      have hT : 0 ≤ CN * A * H := by positivity
      have hnn : 0 ≤ ‖r26t8a_nest p (q - i) (fun Yw : Euc d × Euc d =>
          ∑' n : ℕ, r26t8a_annularNewton nu chi (((1 : ℝ) / 2) ^ n) F Yw.1 Yw.2) X z‖ := norm_nonneg _
      have hch0 : (0 : ℝ) ≤ q.choose i := Nat.cast_nonneg _
      calc (q.choose i : ℝ) * ‖iteratedFDeriv ℝ i chi z‖ * ‖r26t8a_nest p (q - i) (fun Yw : Euc d × Euc d =>
            ∑' n : ℕ, r26t8a_annularNewton nu chi (((1 : ℝ) / 2) ^ n) F Yw.1 Yw.2) X z‖
          ≤ (q.choose i : ℝ) * B * (CN * A * H * (1 + r ^ (2 - σ - (q : ℝ)) * (r ^ i) * (1 + |Real.log r|) ^ (b + 1))) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hB1 hch0) hn hnn (by positivity)
        _ ≤ (q.choose i : ℝ) * B * (CN * A * H * (2 ^ q * (1 + E))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hk1 hT) (by positivity)
        _ = _ := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_mul]
    have hs : ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) = 2 ^ q := by exact_mod_cast Nat.sum_range_choose q
    rw [hs]
    have hwt := r26t8a_jb_le_pairWeight (d := d) hM X z hz2
    have hec := r26t8a_p07_envcmp b σ q hr hz2
    have h4 : (4 : ℝ) ^ q ≤ 4 ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
    have hpwn : 0 ≤ pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) := hpw0
    have hEn : 0 ≤ (1 + (min 1 ‖z‖) ^ (-((σ - 2) + (q : ℝ))) * (1 + |Real.log (min 1 ‖z‖)|) ^ (b + 1)) :=
      add_nonneg zero_le_one (mul_nonneg (Real.rpow_nonneg (le_min zero_le_one hr.le) _) (by positivity))
    have hcmp0 : 0 ≤ cmp := by rw [hcmp]; positivity
    -- 2^q * (2^q * (B * (CN*A*H*(1+E)))) <= C A pw (1+E')
    have hq4 : (2 : ℝ) ^ q * 2 ^ q = 4 ^ q := by rw [← mul_pow]; norm_num
    calc (2 : ℝ) ^ q * (2 ^ q * (B * (CN * A * H * (1 + E)))) = 4 ^ q * (B * CN * A * (H * (1 + E))) := by
          rw [← hq4]; ring
      _ ≤ 4 ^ k * (B * CN * A * ((3 ^ (2 * M) * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z)) *
            (cmp * (1 + (min 1 ‖z‖) ^ (-((σ - 2) + (q : ℝ))) * (1 + |Real.log (min 1 ‖z‖)|) ^ (b + 1))))) := by
          have hBCA : 0 ≤ B * CN * A := by positivity
          have h5 : H * (1 + E) ≤ (3 ^ (2 * M) * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z)) *
              (cmp * (1 + (min 1 ‖z‖) ^ (-((σ - 2) + (q : ℝ))) * (1 + |Real.log (min 1 ‖z‖)|) ^ (b + 1))) :=
            mul_le_mul hwt hec (by positivity) (by positivity)
          exact mul_le_mul h4 (mul_le_mul_of_nonneg_left h5 hBCA) (by positivity) (by positivity)
      _ = _ := by ring

end HRS.MS.R26T8A
