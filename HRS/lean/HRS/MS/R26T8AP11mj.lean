import HRS.MS.R26T8AP11fin

/-!
# S8.2 nonlocal layer: a locally uniform summable majorant for the nested jets of the annular pieces (P11e, part 3a input)
`r26t8a_loc_majorant`: for `0 < |z| < 2` there are `r > 0` and a summable `Phi : ℕ → ℝ` bounding `‖nest i j (locV (2^-n)) Y w‖`
(`i + j <= k`) for `‖Y-X‖ < r`, `‖w-z‖ < r`, using the near bound for `|w| <= 4 R_n` (finitely many `n`) and the far bound otherwise.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

theorem r26t8a_summable_geom_log (b : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    Summable fun n : ℕ => (((1 : ℝ) / 2) ^ n) ^ δ * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b := by
  set ρ : ℝ := ((1 : ℝ) / 2) ^ δ with hρ
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos (by norm_num) _
  have hρ1 : ρ < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) hδ
  have hf : Summable fun n : ℕ => (n : ℝ) ^ b * ρ ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one b (by rw [Real.norm_of_nonneg hρ0.le]; exact hρ1)
  have hg : Summable fun n : ℕ => (((n + 1 : ℕ) : ℝ)) ^ b * ρ ^ (n + 1) := (summable_nat_add_iff 1).2 hf
  have hg' : Summable fun n : ℕ => ((n : ℝ) + 1) ^ b * ρ ^ n := by
    refine (hg.mul_right ρ⁻¹).congr fun n => ?_
    push_cast
    field_simp
    ring
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hg'
  have e1 : (((1 : ℝ) / 2) ^ n) ^ δ = ρ ^ n := by
    rw [hρ, Real.rpow_pow_comm (by norm_num)]
  have e2 : |Real.log (((1 : ℝ) / 2) ^ n)| ≤ n := by
    rw [Real.log_pow, one_div, Real.log_inv, abs_mul, Nat.abs_cast, abs_neg,
      abs_of_nonneg (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))]
    have : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  rw [e1]
  have : (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b ≤ ((n : ℝ) + 1) ^ b :=
    pow_le_pow_left₀ (by positivity) (by linarith) b
  calc ρ ^ n * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b ≤ ρ ^ n * ((n : ℝ) + 1) ^ b :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = ((n : ℝ) + 1) ^ b * ρ ^ n := by ring

theorem r26t8a_loc_majorant (d : ℕ) (hd : 2 ≤ d) (k b : ℕ) (alpha M sigma : ℝ)
    (halpha : 0 < alpha) (had : alpha < d) (hM : 0 ≤ M) (hsigma : 0 ≤ sigma) (hsd : sigma < d)
    (chi : Euc d → ℝ) (hchi : NewtonCutoff chi) :
    ∀ F : Euc d → Euc d → ℝ, ∀ A : ℝ, 0 ≤ A → Conormal k b M sigma A F → ∀ X z : Euc d, z ≠ 0 → ‖z‖ < 2 →
      ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∃ Φ : ℕ → ℝ, (∀ n, 0 ≤ Φ n) ∧ Summable Φ ∧
        ∀ n : ℕ, ∀ i j : ℕ, i + j ≤ k → ∀ Y : Euc d, ‖Y - X‖ < r → ∀ w : Euc d, ‖w - z‖ < r →
          ‖r26t8a_nest i j (fun Yw : Euc d × Euc d => r26t8a_locV alpha chi ((1 / 2 : ℝ) ^ n) F Yw.1 Yw.2) Y w‖ ≤ Φ n := by
  obtain ⟨Cn, hCn0, hCn⟩ := r26t8a_locV_near d hd k b alpha M sigma halpha had hM hsigma chi hchi
  obtain ⟨Cf, hCf0, hCf⟩ := r26t8a_locV_far d hd k b alpha M sigma halpha had hM hsigma chi hchi
  intro F A hA hF X z hz0 hz2
  have hδ : 0 < (d : ℝ) - sigma := by linarith
  have hzpos : 0 < ‖z‖ := norm_pos_iff.2 hz0
  set r : ℝ := min (‖z‖ / 2) (min ((2 - ‖z‖) / 2) 1) with hr
  have hr0 : 0 < r := lt_min (by positivity) (lt_min (by linarith) one_pos)
  have hr1 : r ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have hrz : r ≤ ‖z‖ / 2 := min_le_left _ _
  have hr2 : r ≤ (2 - ‖z‖) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  set J : ℝ := (3 : ℝ) ^ (2 * M) * jbracket X ^ (2 * M) with hJ
  have hJ0 : 0 ≤ J := by rw [hJ]; have := s83_jb_pos X; positivity
  set Sn : ℕ → ℝ := fun n => ∑ j ∈ Finset.range (k + 1), (((1 : ℝ) / 2) ^ n) ^ (alpha - sigma - (j : ℝ)) with hSn
  set Sf : ℝ := ∑ j ∈ Finset.range (k + 1), (‖z‖ / 2) ^ (alpha - (d : ℝ) - (j : ℝ)) with hSf
  set NR : ℕ → ℝ := fun n => if ‖z‖ / 8 ≤ ((1 : ℝ) / 2) ^ n then
      Sn n * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b else 0 with hNR
  set FR : ℕ → ℝ := fun n => (((1 : ℝ) / 2) ^ n) ^ ((d : ℝ) - sigma) *
      (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b * Sf with hFR
  have hSn0 : ∀ n, 0 ≤ Sn n := fun n => Finset.sum_nonneg fun j _ => Real.rpow_nonneg (by positivity) _
  have hSf0 : 0 ≤ Sf := Finset.sum_nonneg fun j _ => Real.rpow_nonneg (by positivity) _
  have hNR0 : ∀ n, 0 ≤ NR n := fun n => by
    rw [hNR]; dsimp only; split_ifs
    · exact mul_nonneg (hSn0 n) (by positivity)
    · exact le_rfl
  have hFR0 : ∀ n, 0 ≤ FR n := fun n => by rw [hFR]; have := hSf0; positivity
  refine ⟨r, hr0, hr1, fun n => (Cn + Cf) * A * J * (NR n + FR n), fun n => ?_, ?_, ?_⟩
  · have := hNR0 n; have := hFR0 n; have : 0 ≤ Cn + Cf := add_nonneg hCn0 hCf0; positivity
  · refine Summable.mul_left _ (Summable.add ?_ ?_)
    · obtain ⟨n1, hn1⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < ‖z‖ / 8) (by norm_num : (1 : ℝ) / 2 < 1)
      refine summable_of_ne_finset_zero (s := Finset.range n1) fun n hn => ?_
      rw [Finset.mem_range, not_lt] at hn
      have : ((1 : ℝ) / 2) ^ n < ‖z‖ / 8 :=
        lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn) hn1
      rw [hNR]; simp only; rw [if_neg (not_le.2 this)]
    · exact (r26t8a_summable_geom_log b hδ).mul_right Sf
  · intro n i j hij Y hY w hw
    have hR : 0 < ((1 : ℝ) / 2) ^ n := by positivity
    have hR1 : ((1 : ℝ) / 2) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hwz : ‖z‖ / 2 ≤ ‖w‖ := by
      have := norm_sub_norm_le z w
      rw [norm_sub_rev] at this; linarith
    have hw2 : ‖w‖ ≤ 2 := by
      have := norm_le_insert' w z; linarith
    have hjb : jbracket Y ^ (2 * M) ≤ J := by
      have h1 : jbracket Y ≤ 3 * jbracket X := by
        have e : Y = X + (Y - X) := by abel
        have := r26t8a_jb_shift' X (Y - X)
        rw [← e] at this
        nlinarith [s83_jb_pos X, norm_nonneg (Y - X)]
      calc jbracket Y ^ (2 * M) ≤ (3 * jbracket X) ^ (2 * M) :=
            Real.rpow_le_rpow (s83_jb_pos Y).le h1 (by linarith)
        _ = J := by rw [hJ, Real.mul_rpow (by norm_num) (s83_jb_pos X).le]
    have hjb0 : 0 ≤ jbracket Y ^ (2 * M) := Real.rpow_nonneg (s83_jb_pos Y).le _
    have hL0 : 0 ≤ (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b := by positivity
    by_cases hnear : ‖w‖ ≤ 4 * ((1 : ℝ) / 2) ^ n
    · have h := hCn F A hA hF _ hR hR1 Y w hnear i j hij
      have hRz : ‖z‖ / 8 ≤ ((1 : ℝ) / 2) ^ n := by linarith
      have hT : (((1 : ℝ) / 2) ^ n) ^ (alpha - sigma - (j : ℝ)) ≤ Sn n :=
        Finset.single_le_sum (f := fun j : ℕ => (((1 : ℝ) / 2) ^ n) ^ (alpha - sigma - (j : ℝ)))
          (fun j _ => Real.rpow_nonneg hR.le _) (Finset.mem_range.2 (by omega))
      have hNRn : (((1 : ℝ) / 2) ^ n) ^ (alpha - sigma - (j : ℝ)) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b
          ≤ NR n := by
        rw [hNR]; simp only; rw [if_pos hRz]
        exact mul_le_mul_of_nonneg_right hT hL0
      have hT0 : 0 ≤ (((1 : ℝ) / 2) ^ n) ^ (alpha - sigma - (j : ℝ)) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b :=
        mul_nonneg (Real.rpow_nonneg hR.le _) hL0
      calc _ ≤ Cn * A * jbracket Y ^ (2 * M) * (((1 : ℝ) / 2) ^ n) ^ (alpha - sigma - (j : ℝ)) *
            (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b := h
        _ = Cn * A * jbracket Y ^ (2 * M) * ((((1 : ℝ) / 2) ^ n) ^ (alpha - sigma - (j : ℝ)) *
            (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b) := by ring
        _ ≤ Cn * A * J * ((((1 : ℝ) / 2) ^ n) ^ (alpha - sigma - (j : ℝ)) *
            (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hjb (mul_nonneg hCn0 hA)) hT0
        _ ≤ (Cn + Cf) * A * J * (NR n + FR n) := by
            have h1 : Cn * A * J * (((1 : ℝ) / 2) ^ n) ^ (alpha - sigma - (j : ℝ)) ≥ 0 := by positivity
            have h2 : (Cn + Cf) * A * J * (NR n + FR n) =
                Cn * A * J * (NR n + FR n) + Cf * A * J * (NR n + FR n) := by ring
            have h3 : 0 ≤ Cf * A * J * (NR n + FR n) := by
              have := hNR0 n; have := hFR0 n; positivity
            have h4 : Cn * A * J * ((((1 : ℝ) / 2) ^ n) ^ (alpha - sigma - (j : ℝ)) *
                (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b) ≤ Cn * A * J * (NR n + FR n) :=
              mul_le_mul_of_nonneg_left (hNRn.trans (le_add_of_nonneg_right (hFR0 n))) (by positivity)
            linarith
    · push Not at hnear
      have hw0 : w ≠ 0 := by
        intro h; rw [h, norm_zero] at hwz; linarith
      have h := hCf F A hA hF _ hR hR1 Y w hw0 hw2 (by linarith) i j hij
      have hpow : ‖w‖ ^ (alpha - (d : ℝ) - (j : ℝ)) ≤ (‖z‖ / 2) ^ (alpha - (d : ℝ) - (j : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos (by positivity) hwz (by
          have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
          linarith)
      have hS : (‖z‖ / 2) ^ (alpha - (d : ℝ) - (j : ℝ)) ≤ Sf :=
        Finset.single_le_sum (f := fun j : ℕ => (‖z‖ / 2) ^ (alpha - (d : ℝ) - (j : ℝ)))
          (fun j _ => Real.rpow_nonneg (by positivity) _) (Finset.mem_range.2 (by omega))
      have hFRn : (((1 : ℝ) / 2) ^ n) ^ ((d : ℝ) - sigma) * ‖w‖ ^ (alpha - (d : ℝ) - (j : ℝ)) *
          (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b ≤ FR n := by
        rw [hFR]; simp only
        have hp0 : 0 ≤ (((1 : ℝ) / 2) ^ n) ^ ((d : ℝ) - sigma) := Real.rpow_nonneg hR.le _
        calc (((1 : ℝ) / 2) ^ n) ^ ((d : ℝ) - sigma) * ‖w‖ ^ (alpha - (d : ℝ) - (j : ℝ)) *
              (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b
            ≤ (((1 : ℝ) / 2) ^ n) ^ ((d : ℝ) - sigma) * Sf * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hpow.trans hS) hp0) hL0
          _ = _ := by ring
      have hT0 : 0 ≤ (((1 : ℝ) / 2) ^ n) ^ ((d : ℝ) - sigma) * ‖w‖ ^ (alpha - (d : ℝ) - (j : ℝ)) *
          (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b := by positivity
      calc _ ≤ Cf * A * jbracket Y ^ (2 * M) * ((((1 : ℝ) / 2) ^ n) ^ ((d : ℝ) - sigma) *
            ‖w‖ ^ (alpha - (d : ℝ) - (j : ℝ))) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b := h
        _ = Cf * A * jbracket Y ^ (2 * M) * ((((1 : ℝ) / 2) ^ n) ^ ((d : ℝ) - sigma) *
            ‖w‖ ^ (alpha - (d : ℝ) - (j : ℝ)) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b) := by ring
        _ ≤ Cf * A * J * ((((1 : ℝ) / 2) ^ n) ^ ((d : ℝ) - sigma) *
            ‖w‖ ^ (alpha - (d : ℝ) - (j : ℝ)) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hjb (mul_nonneg hCf0 hA)) hT0
        _ ≤ (Cn + Cf) * A * J * (NR n + FR n) := by
            have h2 : (Cn + Cf) * A * J * (NR n + FR n) =
                Cn * A * J * (NR n + FR n) + Cf * A * J * (NR n + FR n) := by ring
            have h3 : 0 ≤ Cn * A * J * (NR n + FR n) := by
              have := hNR0 n; have := hFR0 n; positivity
            have h4 : Cf * A * J * ((((1 : ℝ) / 2) ^ n) ^ ((d : ℝ) - sigma) *
                ‖w‖ ^ (alpha - (d : ℝ) - (j : ℝ)) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b) ≤
                Cf * A * J * (NR n + FR n) :=
              mul_le_mul_of_nonneg_left (hFRn.trans (le_add_of_nonneg_left (hNR0 n))) (by positivity)
            linarith

end HRS.MS.R26T8A
