import HRS.MS.R26T8AP11s
import HRS.MS.R26T8AP01p

/-!
# S8.2 nonlocal layer: near-regime annular pieces for the PURE conormal class (any sign of the order)
Verbatim copies of the `Conormal`/`0 <= sigma` versions with `ConormalP` and `r26t8a_annular_sourceP` (the only place the hypotheses enter).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_locW_nearP (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (alpha M sigma : ℝ)
    (halpha : 0 < alpha) (had : alpha < d) (hM : 0 ≤ M)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A →
      ConormalP k b M sigma A F → ∀ R : ℝ, 0 < R → R ≤ 1 → ∀ X z : Euc d, ‖z‖ ≤ 4 * R →
      ∀ p q : ℕ, p + q ≤ k →
        ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => r26t8a_locW alpha chi R F Yw.1 Yw.2)
          (X - (1 / 2 : ℝ) • z) z‖ ≤
          C * A * jbracket X ^ (2 * M) * (R ^ (alpha - sigma - q)) * (1 + |Real.log R|) ^ b := by
  obtain ⟨CK, hCK0, -, -, hKm⟩ := r26t8a_riesz_potential_jets d hd alpha halpha had 0
  obtain ⟨C1, hC10, hP1⟩ := r26t8a_annular_sourceP k b M sigma hM chi hchi
  refine ⟨2 ^ k * C1 * 6 ^ (2 * M) * CK * 7 ^ alpha, by positivity, ?_⟩
  intro F A hA hF R hR hR1 X z hz p q hpq
  obtain ⟨-, hbd⟩ := hP1 A hA F hF R hR hR1
  set src := r26t8a_p11_src chi R F with hsrc
  have hsrc_cd : ContDiff ℝ (k : WithTop ℕ∞) src := r26t8a_p11_src_contDiff hchi hR hF.1
  set S' : Euc d × Euc d → ℝ := fun Yw => src (Yw.1 + (1 / 2 : ℝ) • Yw.2, Yw.2) with hS'
  have hSc : ContDiff ℝ ⊤ (r26t8a_sh_S (E := Euc d) (1 / 2)) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (r26t8a_sh_S (E := Euc d) (1 / 2))
  have hS'cd : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) S' :=
    ((hsrc_cd.of_le (by exact_mod_cast hpq)).comp (hSc.of_le le_top))
  have hSv : ∀ Y w : Euc d, 2 * R < ‖w‖ → S' (Y, w) = 0 := fun Y w hw =>
    r26t8a_p11_src_vanish hchi hR F _ w hw
  set L : ℝ := (1 + |Real.log R|) ^ b with hL
  have hL0 : 0 ≤ L := by positivity
  have hjb0 : 0 ≤ jbracket X ^ (2 * M) := Real.rpow_nonneg (s83_jb_pos X).le _
  have hRq : 0 ≤ R ^ (-(sigma + (q : ℝ))) := Real.rpow_nonneg hR.le _
  set T : ℝ := C1 * A * (6 ^ (2 * M) * jbracket X ^ (2 * M)) * R ^ (-(sigma + (q : ℝ))) * L with hT
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  set B : ℝ := 2 ^ k * T with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hBd : ∀ i ≤ p, ∀ j ≤ q, ∀ Y : Euc d, ‖Y - (X - (1 / 2 : ℝ) • z)‖ < 1 → ∀ w : Euc d,
      ‖r26t8a_nest i j S' Y w‖ ≤ B := by
    intro i hi j hj Y hY w
    by_cases hw : 2 * R < ‖w‖
    · rw [r26t8a_nest_vanish i j S' (2 * R) hSv Y w hw, norm_zero]; exact hB0
    · push Not at hw
      have hΨ : ContDiff ℝ ((i + j : ℕ) : WithTop ℕ∞) src :=
        hsrc_cd.of_le (by exact_mod_cast (by omega : i + j ≤ k))
      have hsh := r26t8a_shear (1 / 2) i j src hΨ Y w
      refine hsh.trans ?_
      have hY'' : jbracket (Y + (1 / 2 : ℝ) • w) ≤ 6 * jbracket X := by
        have h1 : Y + (1 / 2 : ℝ) • w = X + (Y + (1 / 2 : ℝ) • w - X) := by abel
        have h2 : ‖Y + (1 / 2 : ℝ) • w - X‖ ≤ 4 := by
          have e : Y + (1 / 2 : ℝ) • w - X = (Y - (X - (1 / 2 : ℝ) • z)) - (1 / 2 : ℝ) • z + (1 / 2 : ℝ) • w := by
            abel
          rw [e]
          have n1 : ‖(1 / 2 : ℝ) • z‖ ≤ 2 * R := by
            rw [norm_smul]; simp; linarith
          have n2 : ‖(1 / 2 : ℝ) • w‖ ≤ R := by
            rw [norm_smul]; simp; linarith
          calc ‖(Y - (X - (1 / 2 : ℝ) • z)) - (1 / 2 : ℝ) • z + (1 / 2 : ℝ) • w‖
              ≤ ‖(Y - (X - (1 / 2 : ℝ) • z)) - (1 / 2 : ℝ) • z‖ + ‖(1 / 2 : ℝ) • w‖ := norm_add_le _ _
            _ ≤ (‖Y - (X - (1 / 2 : ℝ) • z)‖ + ‖(1 / 2 : ℝ) • z‖) + ‖(1 / 2 : ℝ) • w‖ :=
                add_le_add (norm_sub_le _ _) le_rfl
            _ ≤ 4 := by linarith
        rw [h1]
        refine (r26t8a_jb_shift' X _).trans ?_
        nlinarith [s83_jb_pos X]
      have hterm : ∀ t ∈ Finset.range (j + 1),
          (j.choose t : ℝ) * |(1 / 2 : ℝ)| ^ t *
            ‖r26t8a_nest (i + t) (j - t) src (Y + (1 / 2 : ℝ) • w) w‖ ≤ (j.choose t : ℝ) * T := by
        intro t ht
        have htj : t ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 ht)
        have h1 := hbd (i + t) (j - t) (by omega) (Y + (1 / 2 : ℝ) • w) w
        rw [r26t8a_p11_src_nest hchi hR F] at h1
        have hjb : jbracket (Y + (1 / 2 : ℝ) • w) ^ (2 * M) ≤ 6 ^ (2 * M) * jbracket X ^ (2 * M) := by
          rw [← Real.mul_rpow (by norm_num) (s83_jb_pos X).le]
          exact Real.rpow_le_rpow (s83_jb_pos _).le hY'' (by positivity)
        have hRt : R ^ (-(sigma + ((j - t : ℕ) : ℝ))) ≤ R ^ (-(sigma + (q : ℝ))) :=
          Real.rpow_le_rpow_of_exponent_ge hR hR1 (by
            have : ((j - t : ℕ) : ℝ) ≤ q := by exact_mod_cast (by omega : j - t ≤ q)
            linarith)
        have h2 : C1 * A * jbracket (Y + (1 / 2 : ℝ) • w) ^ (2 * M) * R ^ (-(sigma + ((j - t : ℕ) : ℝ))) * L ≤ T := by
          rw [hT]
          have hj0 : 0 ≤ jbracket (Y + (1 / 2 : ℝ) • w) ^ (2 * M) := Real.rpow_nonneg (s83_jb_pos _).le _
          have h3 : C1 * A * jbracket (Y + (1 / 2 : ℝ) • w) ^ (2 * M) ≤ C1 * A * (6 ^ (2 * M) * jbracket X ^ (2 * M)) :=
            mul_le_mul_of_nonneg_left hjb (by positivity)
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul h3 hRt (Real.rpow_nonneg hR.le _) (by positivity)) hL0
        have hch : (0 : ℝ) ≤ j.choose t := Nat.cast_nonneg _
        have hhalf : |(1 / 2 : ℝ)| ^ t ≤ 1 := pow_le_one₀ (abs_nonneg _) (by norm_num [abs_of_pos])
        calc (j.choose t : ℝ) * |(1 / 2 : ℝ)| ^ t * ‖r26t8a_nest (i + t) (j - t) src (Y + (1 / 2 : ℝ) • w) w‖
            ≤ (j.choose t : ℝ) * 1 * T :=
              mul_le_mul (mul_le_mul_of_nonneg_left hhalf hch) (h1.trans h2) (norm_nonneg _) (by positivity)
          _ = (j.choose t : ℝ) * T := by ring
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [← Finset.sum_mul]
      have hsum : (∑ t ∈ Finset.range (j + 1), (j.choose t : ℝ)) = 2 ^ j := by
        exact_mod_cast Nat.sum_range_choose j
      rw [hsum]
      calc (2 : ℝ) ^ j * T ≤ 2 ^ k * T :=
            mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hT0
        _ = B := rfl
  have hKi : ∀ r : ℝ, IntegrableOn (fun u : Euc d => ‖u‖ ^ (alpha - (d : ℝ))) (ball (0 : Euc d) r) := by
    intro r
    by_cases hr : 0 < r
    · exact (hKm r hr).1
    · rw [ball_eq_empty.2 (not_lt.1 hr)]
      exact integrableOn_empty
  have hρ7 : ‖z‖ + 2 * R < 7 * R := by linarith
  have hmain := r26t8a_near_conv (fun u : Euc d => ‖u‖ ^ (alpha - (d : ℝ)))
    (fun u => Real.rpow_nonneg (norm_nonneg _) _) (measurable_norm.pow_const _) hKi p q
    S' hS'cd (2 * R) hSv B (X - (1 / 2 : ℝ) • z) z hBd (7 * R) hρ7
  have hfun : (fun Yw : Euc d × Euc d => r26t8a_locW alpha chi R F Yw.1 Yw.2) =
      fun Yw : Euc d × Euc d => ∫ u, ‖u‖ ^ (alpha - (d : ℝ)) * S' (Yw.1, Yw.2 - u) := by
    funext Yw
    exact r26t8a_locW_conv alpha chi R F Yw.1 Yw.2
  rw [hfun]
  refine hmain.trans ?_
  have hmass := (hKm (7 * R) (by positivity)).2
  have h7 : (7 * R) ^ alpha = 7 ^ alpha * R ^ alpha := Real.mul_rpow (by norm_num) hR.le
  have hexp : R ^ (-(sigma + (q : ℝ))) * R ^ alpha = R ^ (alpha - sigma - q) := by
    rw [← Real.rpow_add hR]; congr 1; ring
  calc B * ∫ u in ball (0 : Euc d) (7 * R), ‖u‖ ^ (alpha - (d : ℝ))
      ≤ B * (CK * (7 * R) ^ alpha) := mul_le_mul_of_nonneg_left hmass hB0
    _ = 2 ^ k * C1 * 6 ^ (2 * M) * CK * 7 ^ alpha * A * jbracket X ^ (2 * M) *
          (R ^ (alpha - sigma - q)) * L := by
        rw [hB, hT, h7, ← hexp]; ring

theorem r26t8a_locV_nearP (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (alpha M sigma : ℝ)
    (halpha : 0 < alpha) (had : alpha < d) (hM : 0 ≤ M)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A →
      ConormalP k b M sigma A F → ∀ R : ℝ, 0 < R → R ≤ 1 → ∀ X z : Euc d, ‖z‖ ≤ 4 * R →
      ∀ p q : ℕ, p + q ≤ k →
        ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => r26t8a_locV alpha chi R F Yw.1 Yw.2) X z‖ ≤
          C * A * jbracket X ^ (2 * M) * (R ^ (alpha - sigma - q)) * (1 + |Real.log R|) ^ b := by
  obtain ⟨C0, hC0, hW⟩ := r26t8a_locW_nearP d hd k b alpha M sigma halpha had hM chi hchi
  refine ⟨2 ^ k * C0, by positivity, ?_⟩
  intro F A hA hF R hR hR1 X z hz p q hpq
  have hΨ : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞)
      (fun Yw : Euc d × Euc d => r26t8a_locW alpha chi R F Yw.1 Yw.2) :=
    r26t8a_locW_contDiff d hd alpha halpha had chi hchi hR F
      (hF.1.of_le (by exact_mod_cast hpq))
  have hsh := r26t8a_shear (-(1 / 2 : ℝ)) p q _ hΨ X z
  have e : (fun Yw : Euc d × Euc d => r26t8a_locV alpha chi R F Yw.1 Yw.2) =
      fun Yw : Euc d × Euc d => (fun Yw : Euc d × Euc d => r26t8a_locW alpha chi R F Yw.1 Yw.2)
        (Yw.1 + (-(1 / 2 : ℝ)) • Yw.2, Yw.2) := rfl
  rw [e]
  refine hsh.trans ?_
  have hX : X + (-(1 / 2 : ℝ)) • z = X - (1 / 2 : ℝ) • z := by rw [neg_smul, sub_eq_add_neg]
  rw [hX]
  set L : ℝ := (1 + |Real.log R|) ^ b with hL
  have hL0 : 0 ≤ L := by positivity
  have hjb0 : 0 ≤ jbracket X ^ (2 * M) := Real.rpow_nonneg (s83_jb_pos X).le _
  set T : ℝ := C0 * A * jbracket X ^ (2 * M) * (R ^ (alpha - sigma - q)) * L with hT
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  have hterm : ∀ t ∈ Finset.range (q + 1), (q.choose t : ℝ) * |(-(1 / 2 : ℝ))| ^ t *
      ‖r26t8a_nest (p + t) (q - t) (fun Yw : Euc d × Euc d => r26t8a_locW alpha chi R F Yw.1 Yw.2)
        (X - (1 / 2 : ℝ) • z) z‖ ≤ (q.choose t : ℝ) * T := by
    intro t ht
    have htq : t ≤ q := Nat.lt_succ_iff.1 (Finset.mem_range.1 ht)
    have h1 := hW F A hA hF R hR hR1 X z hz (p + t) (q - t) (by omega)
    have hR' : R ^ (alpha - sigma - ((q - t : ℕ) : ℝ)) ≤ R ^ (alpha - sigma - (q : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hR hR1 (by
        have : ((q - t : ℕ) : ℝ) ≤ q := by exact_mod_cast (by omega : q - t ≤ q)
        linarith)
    have h2 : C0 * A * jbracket X ^ (2 * M) * (R ^ (alpha - sigma - ((q - t : ℕ) : ℝ))) * L ≤ T := by
      rw [hT]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hR' (by positivity)) hL0
    have hch : (0 : ℝ) ≤ q.choose t := Nat.cast_nonneg _
    have hhalf : |(-(1 / 2 : ℝ))| ^ t ≤ 1 :=
      pow_le_one₀ (abs_nonneg _) (by norm_num [abs_neg, abs_of_pos])
    calc (q.choose t : ℝ) * |(-(1 / 2 : ℝ))| ^ t *
          ‖r26t8a_nest (p + t) (q - t) (fun Yw : Euc d × Euc d => r26t8a_locW alpha chi R F Yw.1 Yw.2)
            (X - (1 / 2 : ℝ) • z) z‖
        ≤ (q.choose t : ℝ) * 1 * T :=
          mul_le_mul (mul_le_mul_of_nonneg_left hhalf hch) (h1.trans h2) (norm_nonneg _) (by positivity)
      _ = (q.choose t : ℝ) * T := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  have hsum : (∑ t ∈ Finset.range (q + 1), (q.choose t : ℝ)) = 2 ^ q := by
    exact_mod_cast Nat.sum_range_choose q
  rw [hsum]
  calc (2 : ℝ) ^ q * T ≤ 2 ^ k * T :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hT0
    _ = 2 ^ k * C0 * A * jbracket X ^ (2 * M) * (R ^ (alpha - sigma - q)) * L := by rw [hT]; ring

end HRS.MS.R26T8A
