import HRS.MS.SuppU2Aux10

/-!
# U2 auxiliary 11: glue between `partialDeriv`/`weightedSupE`/`decayNormE` and norms of iterated derivatives
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace HRS.Whole

variable {d : ℕ}

lemma u2_partial_le {f : Euc d → ℝ} (j : ℕ) (I : Fin j → Fin d) (y : Euc d) :
    |partialDeriv I f y| ≤ ‖iteratedFDeriv ℝ j f y‖ := by
  unfold partialDeriv
  have h := (iteratedFDeriv ℝ j f y).le_opNorm (fun l => EuclideanSpace.single (I l) (1 : ℝ))
  have h1 : ∏ l, ‖(EuclideanSpace.single (I l) (1 : ℝ) : Euc d)‖ = 1 := by
    simp
  rw [h1, mul_one] at h
  simpa using h

lemma u2_jb_pos (y : Euc d) : 0 < jbracket y := by
  unfold jbracket; exact Real.sqrt_pos.mpr (by positivity)

lemma u2_jb_le (y : Euc d) : jbracket y ≤ 1 + ‖y‖ := by
  unfold jbracket
  exact Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [norm_nonneg y]⟩

lemma u2_one_add_le_two_jb (y : Euc d) : 1 + ‖y‖ ≤ 2 * jbracket y := by
  have h1 : 1 ≤ jbracket y := by
    unfold jbracket
    exact Real.le_sqrt_of_sq_le (by nlinarith [norm_nonneg y])
  have h2 : ‖y‖ ≤ jbracket y := by
    unfold jbracket
    exact Real.le_sqrt_of_sq_le (by nlinarith [norm_nonneg y])
  linarith

/-- From a bound on all `jbracket^L |∂^I h|` to bounds on the norms of the iterated derivatives. -/
lemma u2_norm_le_of_partial (hd : 1 ≤ d) {k : ℕ} {L : ℝ} (hL : 0 ≤ L) {h : Euc d → ℝ} {Λ : ℝ}
    (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ j ≤ k, ∀ (I : Fin j → Fin d) (x : Euc d), jbracket x ^ L * |partialDeriv I h x| ≤ Λ)
    (m : ℕ) (hm : m ≤ k) (y : Euc d) :
    ‖iteratedFDeriv ℝ m h y‖ ≤ ((d : ℝ) ^ k * 2 ^ L * Λ) * u2Wt L y := by
  have hjb := u2_jb_pos y
  have hcmp : jbracket y ^ (-L) ≤ 2 ^ L * u2Wt L y := by
    have := u2_cmp hjb (by positivity : 0 < 1 + ‖y‖) (u2_one_add_le_two_jb y) hL
    exact this
  have hI : ∀ I : Fin m → Fin d, |partialDeriv I h y| ≤ Λ * (2 ^ L * u2Wt L y) := by
    intro I
    have h1 := hΛ m hm I y
    have h2 : |partialDeriv I h y| ≤ Λ * jbracket y ^ (-L) := by
      rw [Real.rpow_neg hjb.le]
      have hp : 0 < jbracket y ^ L := Real.rpow_pos_of_pos hjb _
      rw [← div_eq_mul_inv, le_div_iff₀ hp]
      linarith
    exact h2.trans (mul_le_mul_of_nonneg_left hcmp hΛ0)
  calc ‖iteratedFDeriv ℝ m h y‖ ≤ ∑ I : Fin m → Fin d,
        |iteratedFDeriv ℝ m h y (fun l => EuclideanSpace.single (I l) (1 : ℝ))| :=
        u2_opnorm_le_sum _
    _ ≤ ∑ I : Fin m → Fin d, Λ * (2 ^ L * u2Wt L y) := Finset.sum_le_sum fun I _ => hI I
    _ = (d : ℝ) ^ m * (Λ * (2 ^ L * u2Wt L y)) := by
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fun]
    _ ≤ (d : ℝ) ^ k * (Λ * (2 ^ L * u2Wt L y)) := by
        refine mul_le_mul_of_nonneg_right ?_ (by have := u2Wt_pos (d := d) L y; positivity)
        exact pow_le_pow_right₀ (by exact_mod_cast hd) hm
    _ = _ := by ring

/-- From `weightedSupE k L h ≤ ofReal Λ` to the bounds of all `jbracket^L |∂^I h|`. -/
lemma u2_wse_bound {k : ℕ} {L : ℝ} {h : Euc d → ℝ} {Λ : ℝ} (hΛ : weightedSupE k L h ≤ ENNReal.ofReal Λ)
    (j : ℕ) (hj : j ≤ k) (I : Fin j → Fin d) (x : Euc d) :
    jbracket x ^ L * |partialDeriv I h x| ≤ max Λ 0 := by
  have h1 : ENNReal.ofReal (jbracket x ^ L * |partialDeriv I h x|) ≤ weightedSupE k L h := by
    unfold weightedSupE derivSupE
    refine le_trans ?_ (le_iSup _ (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (k + 1)))
    refine le_trans ?_ (le_iSup _ I)
    exact le_iSup (fun x => ENNReal.ofReal (jbracket x ^ L * |partialDeriv I h x|)) x
  have h2 := h1.trans hΛ
  rw [ENNReal.ofReal_le_ofReal_iff'] at h2
  rcases h2 with h2 | h2
  · exact h2.trans (le_max_left _ _)
  · have : 0 ≤ jbracket x ^ L * |partialDeriv I h x| :=
      mul_nonneg (Real.rpow_nonneg (u2_jb_pos x).le _) (abs_nonneg _)
    exact (by linarith : jbracket x ^ L * |partialDeriv I h x| ≤ 0).trans (le_max_right _ _)

/-- From norm decay to `decayNormE`. -/
lemma u2_decayNormE_le {k : ℕ} {b : ℝ} (hb : 0 ≤ b) {F : Euc d → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hF : ∀ j ≤ k, ∀ x : Euc d, ‖iteratedFDeriv ℝ j F x‖ ≤ B * (1 + ‖x‖) ^ (-(b + j))) :
    decayNormE k b F ≤ ENNReal.ofReal B := by
  unfold decayNormE derivSupE
  refine iSup_le fun j => iSup_le fun I => iSup_le fun x => ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hj : (j : ℕ) ≤ k := Nat.lt_succ_iff.mp j.2
  have h1 := (u2_partial_le (f := F) (j : ℕ) I x).trans (hF j hj x)
  have hp : 0 ≤ b + ((j : ℕ) : ℝ) := by have : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _; linarith
  have h2 : jbracket x ^ (b + ((j : ℕ) : ℝ)) ≤ (1 + ‖x‖) ^ (b + ((j : ℕ) : ℝ)) :=
    Real.rpow_le_rpow (u2_jb_pos x).le (u2_jb_le x) hp
  have hv : 0 < 1 + ‖x‖ := by positivity
  calc jbracket x ^ (b + ((j : ℕ) : ℝ)) * |partialDeriv I F x|
      ≤ (1 + ‖x‖) ^ (b + ((j : ℕ) : ℝ)) * (B * (1 + ‖x‖) ^ (-(b + ((j : ℕ) : ℝ)))) :=
        mul_le_mul h2 h1 (abs_nonneg _) (Real.rpow_nonneg hv.le _)
    _ = B := by
        rw [mul_left_comm, ← Real.rpow_add hv]
        simp

lemma u2_conv_eq_y (κ g : Euc d → ℝ) (x : Euc d) :
    u2Conv κ g x = ∫ y, g y * κ (x - y) := by
  unfold u2Conv
  have := integral_sub_left_eq_self (fun z => κ z • g (x - z)) (volume : Measure (Euc d)) x
  rw [← this]
  congr 1
  funext y
  simp only [sub_sub_cancel, smul_eq_mul]
  ring

end HRS.Whole
