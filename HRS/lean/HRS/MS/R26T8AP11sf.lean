import HRS.MS.R26T8AP11s
import HRS.MS.R26T8APot4

/-!
# S8.2 nonlocal layer: one annular piece of the local Riesz potential, far regime (shifted centre)
`r26t8a_locW_far` (derivatives fall on the kernel, `r26t8a_far_conv`, sheared source `src ∘ S_{1/2}`) and
`r26t8a_locV_far` (passage to centre/relative coordinates by the shear `S_{-1/2}`), for `4R <= |z| <= 2`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

theorem r26t8a_locW_far (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (alpha M sigma : ℝ)
    (halpha : 0 < alpha) (had : alpha < d) (hM : 0 ≤ M) (hsigma : 0 ≤ sigma)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A →
      Conormal k b M sigma A F → ∀ R : ℝ, 0 < R → R ≤ 1 → ∀ X z : Euc d, z ≠ 0 → ‖z‖ ≤ 2 →
      2 * R ≤ ‖z‖ / 2 → ∀ p q : ℕ, p + q ≤ k →
        ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => r26t8a_locW alpha chi R F Yw.1 Yw.2)
          (X - (1 / 2 : ℝ) • z) z‖ ≤
          C * A * jbracket X ^ (2 * M) * (R ^ ((d : ℝ) - sigma) * ‖z‖ ^ (alpha - (d : ℝ) - q)) *
            (1 + |Real.log R|) ^ b := by
  obtain ⟨CK, hCK0, hKsm, hKj, -⟩ := r26t8a_riesz_potential_jets d hd alpha halpha had k
  obtain ⟨C1, hC10, hP1⟩ := r26t8a_annular_source k b M sigma hM hsigma chi hchi
  set omg : ℝ := (volume : Measure (Euc d)).real (ball (0 : Euc d) 1) with homg
  have homg0 : 0 ≤ omg := measureReal_nonneg
  refine ⟨C1 * 6 ^ (2 * M) * CK * 2 ^ ((d : ℝ) + k) * 2 ^ d * omg, by positivity, ?_⟩
  intro F A hA hF R hR hR1 X z hz0 hz2 hz p q hpq
  obtain ⟨-, hbd⟩ := hP1 A hA F hF R hR hR1
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
  set src := r26t8a_p11_src chi R F with hsrc
  have hsrc_cd : ContDiff ℝ (k : WithTop ℕ∞) src := r26t8a_p11_src_contDiff hchi hR hF.1
  set S' : Euc d × Euc d → ℝ := fun Yw => src (Yw.1 + (1 / 2 : ℝ) • Yw.2, Yw.2) with hS'
  have hSc : ContDiff ℝ ⊤ (r26t8a_sh_S (E := Euc d) (1 / 2)) :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ) (r26t8a_sh_S (E := Euc d) (1 / 2))
  have hS'cd : ContDiff ℝ (p : WithTop ℕ∞) S' :=
    ((hsrc_cd.of_le (by exact_mod_cast (by omega : p ≤ k))).comp (hSc.of_le le_top))
  have hSv : ∀ Y w : Euc d, 2 * R < ‖w‖ → S' (Y, w) = 0 := fun Y w hw =>
    r26t8a_p11_src_vanish hchi hR F _ w hw
  set L : ℝ := (1 + |Real.log R|) ^ b with hL
  have hL0 : 0 ≤ L := by positivity
  have hRs : 0 ≤ R ^ (-sigma) := Real.rpow_nonneg hR.le _
  have hjb0 : 0 ≤ jbracket X ^ (2 * M) := Real.rpow_nonneg (s83_jb_pos X).le _
  set B : ℝ := C1 * A * (6 ^ (2 * M) * jbracket X ^ (2 * M)) * R ^ (-sigma) * L with hB
  have hB0 : 0 ≤ B := by rw [hB]; positivity
  have hBd : ∀ i ≤ p, ∀ Y : Euc d, ‖Y - (X - (1 / 2 : ℝ) • z)‖ < 1 → ∀ w : Euc d,
      ‖r26t8a_nest i 0 S' Y w‖ ≤ B := by
    intro i hi Y hY w
    by_cases hw : 2 * R < ‖w‖
    · rw [r26t8a_nest_vanish i 0 S' (2 * R) hSv Y w hw, norm_zero]; exact hB0
    · push Not at hw
      have hΨ : ContDiff ℝ ((i + 0 : ℕ) : WithTop ℕ∞) src :=
        hsrc_cd.of_le (by exact_mod_cast (by omega : i + 0 ≤ k))
      have hsh := r26t8a_shear (1 / 2) i 0 src hΨ Y w
      simp only [zero_add, Finset.sum_range_one, Nat.choose_self, Nat.cast_one, pow_zero, one_mul,
        Nat.sub_zero, add_zero] at hsh
      refine hsh.trans ?_
      have h1 := hbd i 0 (by omega) (Y + (1 / 2 : ℝ) • w) w
      rw [r26t8a_p11_src_nest hchi hR F] at h1
      have hY'' : jbracket (Y + (1 / 2 : ℝ) • w) ≤ 6 * jbracket X := by
        have e1 : Y + (1 / 2 : ℝ) • w = X + (Y + (1 / 2 : ℝ) • w - X) := by abel
        have h2 : ‖Y + (1 / 2 : ℝ) • w - X‖ ≤ 4 := by
          have e : Y + (1 / 2 : ℝ) • w - X =
              (Y - (X - (1 / 2 : ℝ) • z)) - (1 / 2 : ℝ) • z + (1 / 2 : ℝ) • w := by abel
          rw [e]
          have n1 : ‖(1 / 2 : ℝ) • z‖ ≤ 1 := by rw [norm_smul]; simp; linarith
          have n2 : ‖(1 / 2 : ℝ) • w‖ ≤ R := by rw [norm_smul]; simp; linarith
          calc ‖(Y - (X - (1 / 2 : ℝ) • z)) - (1 / 2 : ℝ) • z + (1 / 2 : ℝ) • w‖
              ≤ ‖(Y - (X - (1 / 2 : ℝ) • z)) - (1 / 2 : ℝ) • z‖ + ‖(1 / 2 : ℝ) • w‖ := norm_add_le _ _
            _ ≤ (‖Y - (X - (1 / 2 : ℝ) • z)‖ + ‖(1 / 2 : ℝ) • z‖) + ‖(1 / 2 : ℝ) • w‖ :=
                add_le_add (norm_sub_le _ _) le_rfl
            _ ≤ 4 := by linarith
        rw [e1]
        refine (r26t8a_jb_shift' X _).trans ?_
        nlinarith [s83_jb_pos X]
      have hjb : jbracket (Y + (1 / 2 : ℝ) • w) ^ (2 * M) ≤ 6 ^ (2 * M) * jbracket X ^ (2 * M) := by
        rw [← Real.mul_rpow (by norm_num) (s83_jb_pos X).le]
        exact Real.rpow_le_rpow (s83_jb_pos _).le hY'' (by positivity)
      have hexp : R ^ (-(sigma + ((0 : ℕ) : ℝ))) = R ^ (-sigma) := by simp
      rw [hexp] at h1
      refine h1.trans ?_
      rw [hB]
      have h3 : C1 * A * jbracket (Y + (1 / 2 : ℝ) • w) ^ (2 * M) ≤ C1 * A * (6 ^ (2 * M) * jbracket X ^ (2 * M)) :=
        mul_le_mul_of_nonneg_left hjb (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h3 hRs) hL0
  -- kernel bounds
  set ρ0 : ℝ := ‖z‖ / 4 with hρ0
  set ρ1 : ℝ := ‖z‖ / 2 with hρ1
  have hρ0p : 0 < ρ0 := by rw [hρ0]; positivity
  have hρ1p : 0 < ρ1 := by rw [hρ1]; positivity
  have hneg : ∀ j : ℕ, alpha - (d : ℝ) - j ≤ 0 := fun j => by
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have hpow : ∀ (j : ℕ) (r x : ℝ), 0 < r → r ≤ x → x ^ (alpha - (d : ℝ) - j) ≤ r ^ (alpha - (d : ℝ) - j) :=
    fun j r x hr hrx => Real.rpow_le_rpow_of_nonpos hr hrx (hneg j)
  set BK : ℝ := CK * ∑ j ∈ Finset.range (q + 1), ρ0 ^ (alpha - (d : ℝ) - j) with hBK
  have hBKd : ∀ j ≤ q, ∀ x : Euc d, ρ0 ≤ ‖x‖ → ‖iteratedFDeriv ℝ j (fun v : Euc d => ‖v‖ ^ (alpha - (d : ℝ))) x‖ ≤ BK := by
    intro j hj x hx
    have hx0 : x ≠ 0 := fun h => by rw [h, norm_zero] at hx; linarith
    refine (hKj j (by omega) x hx0).trans ?_
    rw [hBK]
    refine mul_le_mul_of_nonneg_left ?_ hCK0
    refine (hpow j ρ0 ‖x‖ hρ0p hx).trans ?_
    exact Finset.single_le_sum (f := fun j : ℕ => ρ0 ^ (alpha - (d : ℝ) - j))
      (fun i _ => Real.rpow_nonneg hρ0p.le _) (Finset.mem_range.2 (by omega))
  have hBKd' : ∀ x : Euc d, ρ1 ≤ ‖x‖ →
      ‖iteratedFDeriv ℝ q (fun v : Euc d => ‖v‖ ^ (alpha - (d : ℝ))) x‖ ≤ CK * ρ1 ^ (alpha - (d : ℝ) - q) := by
    intro x hx
    have hx0 : x ≠ 0 := fun h => by rw [h, norm_zero] at hx; linarith
    refine (hKj q (by omega) x hx0).trans ?_
    exact mul_le_mul_of_nonneg_left (hpow q ρ1 ‖x‖ hρ1p hx) hCK0
  have hmain := r26t8a_far_conv (fun v : Euc d => ‖v‖ ^ (alpha - (d : ℝ))) p q
    (hKsm.of_le (by exact_mod_cast le_top)) S' hS'cd (2 * R)
    hSv (X - (1 / 2 : ℝ) • z) z ρ0 hρ0p ρ0 hρ0p
    (fun z' hz' v hv => by
      have h1 : ‖z'‖ > ‖z‖ - ρ0 := by
        have := norm_sub_norm_le z z'
        have h3 : ‖z - z'‖ < ρ0 := by simpa [dist_eq_norm, norm_sub_rev] using hz'
        linarith
      have h2 := norm_sub_norm_le z' v
      have : ‖z'‖ - ‖v‖ ≤ ‖z' - v‖ := h2
      rw [hρ0] at *
      linarith)
    BK hBKd ρ1 (CK * ρ1 ^ (alpha - (d : ℝ) - q))
    (fun v hv => by
      have h2 := norm_sub_norm_le z v
      rw [hρ1]; linarith)
    hBKd' B hBd
  have hfun : (fun Yw : Euc d × Euc d => r26t8a_locW alpha chi R F Yw.1 Yw.2) =
      fun Yw : Euc d × Euc d => ∫ v, ‖Yw.2 - v‖ ^ (alpha - (d : ℝ)) * S' (Yw.1, v) := rfl
  rw [hfun]
  refine hmain.trans ?_
  have hvol : (volume : Measure (Euc d)).real (closedBall (0 : Euc d) (2 * R)) = (2 * R) ^ d * omg := by
    rw [Measure.addHaar_real_closedBall volume 0 (by positivity), finrank_euclideanSpace_fin]
  rw [hvol]
  set e : ℝ := alpha - (d : ℝ) - q with he
  have hzne : 0 ≤ ‖z‖ ^ e := Real.rpow_nonneg hzpos.le _
  have hρ1e : ρ1 ^ e ≤ 2 ^ ((d : ℝ) + k) * ‖z‖ ^ e := by
    rw [hρ1, Real.div_rpow hzpos.le (by norm_num)]
    have h2 : (2 : ℝ) ^ (-((d : ℝ) + k)) ≤ 2 ^ e := by
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have : (q : ℝ) ≤ k := by exact_mod_cast (by omega : q ≤ k)
      rw [he]; linarith
    have h3 : (0 : ℝ) < 2 ^ (-((d : ℝ) + k)) := by positivity
    calc ‖z‖ ^ e / 2 ^ e ≤ ‖z‖ ^ e / 2 ^ (-((d : ℝ) + k)) := div_le_div_of_nonneg_left hzne h3 h2
      _ = 2 ^ ((d : ℝ) + k) * ‖z‖ ^ e := by
        rw [Real.rpow_neg (by norm_num), div_inv_eq_mul, mul_comm]
  have hRd : R ^ d * R ^ (-sigma) = R ^ ((d : ℝ) - sigma) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hR]; congr 1
  have hfac : 0 ≤ B * ((2 * R) ^ d * omg) := by positivity
  calc CK * ρ1 ^ e * B * ((2 * R) ^ d * omg)
      = (CK * ρ1 ^ e) * (B * ((2 * R) ^ d * omg)) := by ring
    _ ≤ (CK * (2 ^ ((d : ℝ) + k) * ‖z‖ ^ e)) * (B * ((2 * R) ^ d * omg)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hρ1e hCK0) hfac
    _ = C1 * 6 ^ (2 * M) * CK * 2 ^ ((d : ℝ) + k) * 2 ^ d * omg * A * jbracket X ^ (2 * M) *
          (R ^ ((d : ℝ) - sigma) * ‖z‖ ^ e) * L := by
        rw [hB, ← hRd, mul_pow]; ring


/-- Far regime of one annular piece of the local Riesz potential, in centre/relative coordinates. -/
theorem r26t8a_locV_far (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (alpha M sigma : ℝ)
    (halpha : 0 < alpha) (had : alpha < d) (hM : 0 ≤ M) (hsigma : 0 ≤ sigma)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ F : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A →
      Conormal k b M sigma A F → ∀ R : ℝ, 0 < R → R ≤ 1 → ∀ X z : Euc d, z ≠ 0 → ‖z‖ ≤ 2 →
      2 * R ≤ ‖z‖ / 2 → ∀ p q : ℕ, p + q ≤ k →
        ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => r26t8a_locV alpha chi R F Yw.1 Yw.2) X z‖ ≤
          C * A * jbracket X ^ (2 * M) * (R ^ ((d : ℝ) - sigma) * ‖z‖ ^ (alpha - (d : ℝ) - q)) *
            (1 + |Real.log R|) ^ b := by
  obtain ⟨C0, hC0, hW⟩ := r26t8a_locW_far d hd k b alpha M sigma halpha had hM hsigma chi hchi
  refine ⟨2 ^ k * C0, by positivity, ?_⟩
  intro F A hA hF R hR hR1 X z hz0 hz2 hz p q hpq
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
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
  set T : ℝ := C0 * A * jbracket X ^ (2 * M) * (R ^ ((d : ℝ) - sigma) * ‖z‖ ^ (alpha - (d : ℝ) - q)) * L with hT
  have hRs : 0 ≤ R ^ ((d : ℝ) - sigma) := Real.rpow_nonneg hR.le _
  have hzq : 0 ≤ ‖z‖ ^ (alpha - (d : ℝ) - q) := Real.rpow_nonneg hzpos.le _
  have hT0 : 0 ≤ T := by rw [hT]; positivity
  have hterm : ∀ t ∈ Finset.range (q + 1), (q.choose t : ℝ) * |(-(1 / 2 : ℝ))| ^ t *
      ‖r26t8a_nest (p + t) (q - t) (fun Yw : Euc d × Euc d => r26t8a_locW alpha chi R F Yw.1 Yw.2)
        (X - (1 / 2 : ℝ) • z) z‖ ≤ (q.choose t : ℝ) * T := by
    intro t ht
    have htq : t ≤ q := Nat.lt_succ_iff.1 (Finset.mem_range.1 ht)
    have h1 := hW F A hA hF R hR hR1 X z hz0 hz2 hz (p + t) (q - t) (by omega)
    have hpowe : ‖z‖ ^ (alpha - (d : ℝ) - ((q - t : ℕ) : ℝ)) = ‖z‖ ^ (alpha - (d : ℝ) - q) * ‖z‖ ^ t := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hzpos]
      congr 1
      rw [Nat.cast_sub htq]; ring
    have hzt : |(-(1 / 2 : ℝ))| ^ t * ‖z‖ ^ t ≤ 1 := by
      rw [← mul_pow]
      refine pow_le_one₀ (by positivity) ?_
      rw [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      linarith
    have hch : (0 : ℝ) ≤ q.choose t := Nat.cast_nonneg _
    have hhalf0 : 0 ≤ |(-(1 / 2 : ℝ))| ^ t := by positivity
    calc (q.choose t : ℝ) * |(-(1 / 2 : ℝ))| ^ t *
          ‖r26t8a_nest (p + t) (q - t) (fun Yw : Euc d × Euc d => r26t8a_locW alpha chi R F Yw.1 Yw.2)
            (X - (1 / 2 : ℝ) • z) z‖
        ≤ (q.choose t : ℝ) * |(-(1 / 2 : ℝ))| ^ t *
            (C0 * A * jbracket X ^ (2 * M) * (R ^ ((d : ℝ) - sigma) *
              (‖z‖ ^ (alpha - (d : ℝ) - q) * ‖z‖ ^ t)) * L) := by
          rw [← hpowe]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = (q.choose t : ℝ) * (|(-(1 / 2 : ℝ))| ^ t * ‖z‖ ^ t) * T := by rw [hT]; ring
      _ ≤ (q.choose t : ℝ) * 1 * T :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hzt hch) hT0
      _ = (q.choose t : ℝ) * T := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  have hsum : (∑ t ∈ Finset.range (q + 1), (q.choose t : ℝ)) = 2 ^ q := by
    exact_mod_cast Nat.sum_range_choose q
  rw [hsum]
  calc (2 : ℝ) ^ q * T ≤ 2 ^ k * T :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) hT0
    _ = 2 ^ k * C0 * A * jbracket X ^ (2 * M) *
          (R ^ ((d : ℝ) - sigma) * ‖z‖ ^ (alpha - (d : ℝ) - q)) * L := by rw [hT]; ring

end HRS.MS.R26T8A
