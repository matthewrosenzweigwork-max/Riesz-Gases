import HRS.MS.R26T8AP06ta
import HRS.MS.R26T8AP11lb

/-!
# S8.2 Taylor split (T): the split `F = (F - P) + P`
`r26t8a_taylor_split` (`σ < 0`, `m < -σ <= m+1`): for `Conormal (k+1+m+1) b M σ A F` there is a `C^(k+1)` function `P` with
`F - P` pure conormal (`ConormalP k b M σ (C A)`) and `‖nest p q (midPair P)‖ <= C A pairWeight` (`p+q <= k`).
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_env_lower (b k q : ℕ) (σ : ℝ) (hq : q ≤ k) (ρ : ℝ) (h1 : 1 / 2 ≤ ρ) (h2 : ρ ≤ 1) :
    1 ≤ 2 ^ (|σ| + (k : ℝ)) * (ρ ^ (-(σ + (q : ℝ))) * (1 + |Real.log ρ|) ^ b) := by
  have hρ : 0 < ρ := by linarith
  have hL : 1 ≤ (1 + |Real.log ρ|) ^ b := one_le_pow₀ (by linarith [abs_nonneg (Real.log ρ)])
  set e : ℝ := -(σ + (q : ℝ)) with he
  have habs : |e| ≤ |σ| + (k : ℝ) := by
    calc |e| = |σ + (q : ℝ)| := abs_neg _
      _ ≤ |σ| + |(q : ℝ)| := abs_add_le _ _
      _ ≤ |σ| + k := by
          rw [Nat.abs_cast]; have : (q : ℝ) ≤ k := by exact_mod_cast hq
          linarith
  have hρe : (1 / 2 : ℝ) ^ |e| ≤ ρ ^ e := by
    rcases le_total 0 e with he0 | he0
    · calc (1 / 2 : ℝ) ^ |e| = (1 / 2 : ℝ) ^ e := by rw [abs_of_nonneg he0]
        _ ≤ ρ ^ e := Real.rpow_le_rpow (by norm_num) h1 he0
    · calc (1 / 2 : ℝ) ^ |e| ≤ 1 := Real.rpow_le_one (by norm_num) (by norm_num) (abs_nonneg _)
        _ ≤ ρ ^ e := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hρ h2 he0
  have hhalf : (1 / 2 : ℝ) ^ (|σ| + (k : ℝ)) ≤ (1 / 2 : ℝ) ^ |e| :=
    Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) habs
  have h2pos : (0 : ℝ) < 2 ^ (|σ| + (k : ℝ)) := by positivity
  have hinv : (2 : ℝ) ^ (|σ| + (k : ℝ)) * (1 / 2 : ℝ) ^ (|σ| + (k : ℝ)) = 1 := by
    rw [← Real.mul_rpow (by norm_num) (by norm_num)]; norm_num
  calc (1 : ℝ) = 2 ^ (|σ| + (k : ℝ)) * (1 / 2 : ℝ) ^ (|σ| + (k : ℝ)) := hinv.symm
    _ ≤ 2 ^ (|σ| + (k : ℝ)) * (ρ ^ e * 1) := by
        refine mul_le_mul_of_nonneg_left ?_ h2pos.le
        rw [mul_one]; exact hhalf.trans hρe
    _ ≤ 2 ^ (|σ| + (k : ℝ)) * (ρ ^ e * (1 + |Real.log ρ|) ^ b) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hL (Real.rpow_nonneg hρ.le _)) h2pos.le


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 3200000 in
theorem r26t8a_taylor_split (hd : 2 ≤ d) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (k b : ℕ) (M σ : ℝ)
    (hM : 0 ≤ M) (hσ : σ < 0) (m : ℕ) (hm : (m : ℝ) < -σ) (hm1 : -σ ≤ (m : ℝ) + 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 0 ≤ A → ∀ F : Euc d → Euc d → ℝ, Conormal (k + 1 + m + 1) b M σ A F →
      ∃ P : Euc d → Euc d → ℝ, ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (Function.uncurry P) ∧
        ConormalP k b M σ (C * A) (fun x y => F x y - P x y) ∧
        ∀ p q : ℕ, p + q ≤ k → ∀ X z : Euc d,
          ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair P Yw.1 Yw.2) X z‖ ≤
            C * A * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) := by
  obtain ⟨C2, hC20, hR⟩ := r26t8a_taylor_remainder hd hchi k b M σ hM hσ m hm hm1
  have hjbpw : ∀ X z : Euc d, ‖z‖ ≤ 2 → jbracket X ^ (2 * M) ≤ 3 ^ (2 * M) * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) :=
    fun X z hz => r26t8a_jb_le_pairWeight hM X z hz
  have hpw0 : ∀ X z : Euc d, 0 ≤ pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) := fun X z =>
    mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _) (Real.rpow_nonneg (s83_jb_pos _).le _)
  set K0 : ℝ := 2 ^ (|σ| + (k : ℝ)) with hK0
  have hK00 : 0 ≤ K0 := by rw [hK0]; positivity
  set T3 : ℝ := 3 ^ (2 * M) with hT3
  have hT30 : 0 ≤ T3 := by rw [hT3]; positivity
  obtain ⟨Dp, hDp0, hDp⟩ := r26t8a_nest_Pm_bound chi hchi m k
  refine ⟨T3 * C2 + K0 * (1 + Dp * C2 * T3) + 1 + Dp * C2 * T3, by positivity, ?_⟩
  intro A hA F hF
  obtain ⟨c, hc1, hc2, hc3⟩ := hR A hA F hF
  have hPxy := r26t8a_Pxy_contDiff chi hchi m k c hc1
  have hmidsub : ∀ Y w : Euc d, midPair (fun x y => F x y - r26t8a_Pxy chi m c x y) Y w =
      midPair F Y w - chi w * r26t8a_Pfull m c Y w := by
    intro Y w
    have := r26t8a_midPair_Pxy chi m c Y w
    unfold midPair at this ⊢
    rw [← this]
  -- jets of the polynomial part
  have hPjet : ∀ p q : ℕ, p + q ≤ k → ∀ X z : Euc d,
      ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => chi Yw.2 * r26t8a_Pfull m c Yw.1 Yw.2) X z‖ ≤
        Dp * C2 * T3 * A * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) := by
    intro p q hpq X z
    by_cases hz : ‖z‖ ≤ 2
    · have h1 := hDp c hc1 p q hpq X z hz (C2 * A * jbracket X ^ (2 * M))
        (fun ℓ hℓ => hc2 ℓ hℓ p (by omega) X)
      refine h1.trans ?_
      have h2 := hjbpw X z hz
      have : Dp * (C2 * A * jbracket X ^ (2 * M)) = Dp * C2 * A * jbracket X ^ (2 * M) := by ring
      rw [this]
      calc Dp * C2 * A * jbracket X ^ (2 * M) ≤ Dp * C2 * A * (T3 * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z)) :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
        _ = Dp * C2 * T3 * A * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) := by ring
    · rw [r26t8a_nest_Pm_far chi hchi p q m c X z (by linarith [not_le.1 hz]), norm_zero]
      have := hpw0 X z
      positivity
  refine ⟨r26t8a_Pxy chi m c, hPxy, And.intro ?_ ?_, ?_⟩
  · have h1 : ContDiffOn ℝ (k : WithTop ℕ∞) (Function.uncurry fun x y => F x y) {p : Euc d × Euc d | p.1 ≠ p.2} :=
      hF.1.of_le (by exact_mod_cast (by omega : k ≤ k + 1 + m + 1))
    exact h1.sub ((hPxy.of_le (by exact_mod_cast Nat.le_succ k)).contDiffOn)
  · intro p q hpq X z hz0
    have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
    have hmj : mixedJet p q (fun x y => F x y - r26t8a_Pxy chi m c x y) X z =
        r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2 - chi Yw.2 * r26t8a_Pfull m c Yw.1 Yw.2) X z := by
      unfold mixedJet r26t8a_nest
      congr 1
      funext Y
      congr 1
      funext w
      exact hmidsub Y w
    rw [hmj]
    have hpw := hpw0 X z
    have hCnn : 0 ≤ T3 * C2 + K0 * (1 + Dp * C2 * T3) + 1 + Dp * C2 * T3 := by positivity
    by_cases hz1 : ‖z‖ ≤ 1 / 2
    · have e : r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2 - chi Yw.2 * r26t8a_Pfull m c Yw.1 Yw.2) X z =
          r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2 - r26t8a_Pfull m c Yw.1 Yw.2) X z := by
        refine r26t8a_nest_congr_ball p q _ _ (ρ := 1 / 4) (by norm_num) X z (fun Y w hw => ?_)
        have h1 : ‖w‖ ≤ 1 := by
          have := norm_le_insert' w z
          linarith
        simp only [hchi.2.2.2.1 w h1, one_mul]
      rw [e]
      have h := hc3 p q hpq X z hzpos hz1
      refine h.trans ?_
      rw [min_eq_right (by linarith : ‖z‖ ≤ 1)]
      have hjb := hjbpw X z (by linarith)
      have eexp : -(σ + (q : ℝ)) = -σ - q := by ring
      rw [eexp]
      have hZ : 0 ≤ ‖z‖ ^ (-σ - (q : ℝ)) * (1 + |Real.log ‖z‖|) ^ b := by positivity
      calc C2 * A * jbracket X ^ (2 * M) * ‖z‖ ^ (-σ - (q : ℝ)) * (1 + |Real.log ‖z‖|) ^ b
          = (C2 * A * jbracket X ^ (2 * M)) * (‖z‖ ^ (-σ - (q : ℝ)) * (1 + |Real.log ‖z‖|) ^ b) := by ring
        _ ≤ (C2 * A * (T3 * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z))) *
              (‖z‖ ^ (-σ - (q : ℝ)) * (1 + |Real.log ‖z‖|) ^ b) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hjb (by positivity)) hZ
        _ ≤ ((T3 * C2 + K0 * (1 + Dp * C2 * T3) + 1 + Dp * C2 * T3) * A *
              pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z)) *
              (‖z‖ ^ (-σ - (q : ℝ)) * (1 + |Real.log ‖z‖|) ^ b) := by
            refine mul_le_mul_of_nonneg_right ?_ hZ
            have hAp : 0 ≤ A * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) := mul_nonneg hA hpw
            have h3 : T3 * C2 ≤ T3 * C2 + K0 * (1 + Dp * C2 * T3) + 1 + Dp * C2 * T3 := by
              have : 0 ≤ K0 * (1 + Dp * C2 * T3) + 1 + Dp * C2 * T3 := by positivity
              linarith
            calc C2 * A * (T3 * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z))
                = (T3 * C2) * (A * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z)) := by ring
              _ ≤ (T3 * C2 + K0 * (1 + Dp * C2 * T3) + 1 + Dp * C2 * T3) *
                    (A * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z)) :=
                  mul_le_mul_of_nonneg_right h3 hAp
              _ = _ := by ring
        _ = _ := by ring
    · push Not at hz1
      have hρ1 : 1 / 2 ≤ min 1 ‖z‖ := le_min (by norm_num) hz1.le
      have hρ2 : min 1 ‖z‖ ≤ 1 := min_le_left _ _
      have hlow := r26t8a_env_lower b k q σ (by omega) (min 1 ‖z‖) hρ1 hρ2
      set Y : ℝ := (min 1 ‖z‖) ^ (-(σ + (q : ℝ))) * (1 + |Real.log (min 1 ‖z‖)|) ^ b with hY
      have hY0 : 0 ≤ Y := by
        rw [hY]; have : 0 < min 1 ‖z‖ := by linarith
        positivity
      -- decomposition of the nest
      set R : ℝ := 2 * ‖z‖ with hR
      have hRpos : 0 < R := by rw [hR]; positivity
      have hFK : Conormal ((k + m + 1) + 1) b M σ A F := by
        have e : k + 1 + m + 1 = (k + m + 1) + 1 := by omega
        rw [e] at hF; exact hF
      have hΨ : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞)
          (fun Yw : Euc d × Euc d => r26t8a_psiCut chi R Yw.2 * midPair F Yw.1 Yw.2) :=
        (r26t8a_gtilde_contDiff hchi hRpos hFK.1).of_le (by exact_mod_cast (by omega : p + q ≤ k + m + 1 + 1))
      have hPf := r26t8a_Pfull_contDiff m c hc1
      have hchic : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) chi := hchi.1.of_le (by exact_mod_cast le_top)
      have hPm : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞)
          (fun Yw : Euc d × Euc d => chi Yw.2 * r26t8a_Pfull m c Yw.1 Yw.2) :=
        ((hchic.comp contDiff_snd).mul hPf).of_le (by exact_mod_cast (by omega : p + q ≤ k + 1))
      have hρ : 0 < ‖z‖ / 2 := by positivity
      have e1 : r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2 - chi Yw.2 * r26t8a_Pfull m c Yw.1 Yw.2) X z =
          r26t8a_nest p q (fun Yw : Euc d × Euc d => r26t8a_psiCut chi R Yw.2 * midPair F Yw.1 Yw.2 -
            chi Yw.2 * r26t8a_Pfull m c Yw.1 Yw.2) X z := by
        refine r26t8a_nest_congr_ball p q _ _ hρ X z (fun Y w hw => ?_)
        have h1 : ‖z‖ - ‖w‖ ≤ ‖z - w‖ := norm_sub_norm_le z w
        rw [norm_sub_rev] at h1
        have : R / 4 ≤ ‖w‖ := by rw [hR]; linarith
        simp only [r26t8a_psiCut_one hchi hRpos this, one_mul]
      have e2 := r26t8a_nest_sub p q z X hΨ hPm
      have e3 : r26t8a_nest p q (fun Yw : Euc d × Euc d => r26t8a_psiCut chi R Yw.2 * midPair F Yw.1 Yw.2) X z =
          mixedJet p q F X z := r26t8a_nest_gtilde hchi hRpos p q X z (by rw [hR]; linarith)
      rw [e1, e2, e3]
      refine (norm_sub_le _ _).trans ?_
      have hF2 := hF.2 p q (by omega) X z hz0
      have hPj := hPjet p q hpq X z
      have hKY : 1 ≤ K0 * Y := hlow
      have hAp : 0 ≤ A * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) := mul_nonneg hA hpw
      have hDC : 0 ≤ Dp * C2 * T3 := by positivity
      calc _ ≤ A * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) * (1 + Y) +
            Dp * C2 * T3 * A * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) := add_le_add hF2 hPj
        _ = (A * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z)) * (1 + Y + Dp * C2 * T3) := by ring
        _ ≤ (A * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z)) *
              ((T3 * C2 + K0 * (1 + Dp * C2 * T3) + 1 + Dp * C2 * T3) * Y) := by
            refine mul_le_mul_of_nonneg_left ?_ hAp
            have h4 : Dp * C2 * T3 ≤ Dp * C2 * T3 * (K0 * Y) := by nlinarith
            have h5 : 0 ≤ T3 * C2 * Y := by positivity
            nlinarith [mul_nonneg hDC hY0, mul_nonneg hK00 hY0]
        _ = _ := by ring
  · intro p q hpq X z
    have hfun : (fun Yw : Euc d × Euc d => midPair (r26t8a_Pxy chi m c) Yw.1 Yw.2) =
        fun Yw => chi Yw.2 * r26t8a_Pfull m c Yw.1 Yw.2 := funext fun Yw => r26t8a_midPair_Pxy chi m c Yw.1 Yw.2
    rw [hfun]
    refine (hPjet p q hpq X z).trans ?_
    have := hpw0 X z
    have h3 : Dp * C2 * T3 ≤ T3 * C2 + K0 * (1 + Dp * C2 * T3) + 1 + Dp * C2 * T3 := by
      have : 0 ≤ T3 * C2 + K0 * (1 + Dp * C2 * T3) + 1 := by positivity
      linarith
    calc Dp * C2 * T3 * A * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z)
        = (Dp * C2 * T3) * (A * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z)) := by ring
      _ ≤ (T3 * C2 + K0 * (1 + Dp * C2 * T3) + 1 + Dp * C2 * T3) * (A * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z)) :=
          mul_le_mul_of_nonneg_right h3 (mul_nonneg hA this)
      _ = _ := by ring

end HRS.MS.R26T8A
