import HRS.MS.R26T8AP07m
import HRS.MS.R26T8AP07l

/-!
# S8.2 local Newton layer, packet T8A.P07 (part n): local summable majorant of the nested jets of the pieces
`r26t8a_p07_majorant`: for `0 < |z| <= 3` there are `r > 0` and a summable `Phi >= 0` with
`‖nest i j (annularNewton (1/2)^n) Y w‖ <= Phi n` for all `n`, `i + j <= k`, `|Y - X| < r`, `|w - z| < r`.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

namespace HRS.MS.R26T8A

variable {d : ℕ}

theorem r26t8a_p07_geom_log (b : ℕ) {δ : ℝ} (hδ : 0 < δ) :
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

theorem r26t8a_p07_majorant (hd : 2 ≤ d) (k b : ℕ) (nu M σ : ℝ) (hnu : 0 < nu) (hM : 0 ≤ M) (hσd : σ < d) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) :
    ∀ A : ℝ, 0 ≤ A → ∀ F : Euc d → Euc d → ℝ, ConormalP k b M σ A F → ∀ X z : Euc d, 0 < ‖z‖ → ‖z‖ ≤ 3 →
      ∃ r : ℝ, 0 < r ∧ r ≤ 1 / 2 ∧ r ≤ ‖z‖ / 2 ∧ ∃ Φ : ℕ → ℝ, (∀ n, 0 ≤ Φ n) ∧ Summable Φ ∧
        ∀ n : ℕ, ∀ i j : ℕ, i + j ≤ k → ∀ Y : Euc d, ‖Y - X‖ < r → ∀ w : Euc d, ‖w - z‖ < r →
          ‖r26t8a_nest i j (fun Yw : Euc d × Euc d =>
            r26t8a_annularNewton nu chi (((1 : ℝ) / 2) ^ n) F Yw.1 Yw.2) Y w‖ ≤ Φ n := by
  obtain ⟨C, hC0, hC⟩ := r26t8a_p07_term_bound hd k b nu M σ hnu hM hσd hchi
  intro A hA F hF X z hz hz3
  have hδ : 0 < (d : ℝ) - σ := by linarith
  set ζ : ℝ := ‖z‖ / 2 with hζ
  have hζ0 : 0 < ζ := by positivity
  set r : ℝ := min ζ (1 / 2) with hr
  have hr0 : 0 < r := lt_min hζ0 (by norm_num)
  have hrζ : r ≤ ζ := min_le_left _ _
  have hr12 : r ≤ 1 / 2 := min_le_right _ _
  set J : ℝ := (3 : ℝ) ^ (2 * M) * jbracket X ^ (2 * M) with hJ
  have hJ0 : 0 ≤ J := by rw [hJ]; have := s83_jb_pos X; positivity
  set u : ℕ → ℝ := fun n => ((1 : ℝ) / 2) ^ n with hu
  set ℓ : ℕ → ℝ := fun n => 1 + |Real.log (u n)| with hℓ
  have hu0 : ∀ n, 0 < u n := fun n => by simp only [hu]; positivity
  have hℓ0 : ∀ n, 0 ≤ ℓ n := fun n => by simp only [hℓ]; positivity
  set Eq : ℕ → ℕ → ℝ := fun q n => if ζ / 4 ≤ u n then
      (u n) ^ (2 - σ - (q : ℝ)) * (ℓ n) ^ b * (1 + ℓ n) else 0 with hEq
  set Lq : ℕ → ℕ → ℝ := fun q n => (u n) ^ ((d : ℝ) - σ) * ζ ^ (2 - (d : ℝ) - (q : ℝ)) * (ℓ n) ^ b *
      (4 + ℓ n + |Real.log ζ|) with hLq
  have hEq0 : ∀ q n, 0 ≤ Eq q n := fun q n => by
    simp only [hEq]; split_ifs
    · have := hu0 n; have := hℓ0 n; positivity
    · exact le_rfl
  have hLq0 : ∀ q n, 0 ≤ Lq q n := fun q n => by
    have := hu0 n; have := hℓ0 n; simp only [hLq]; positivity
  set Ψ : ℕ → ℝ := fun n => ∑ q ∈ Finset.range (k + 1), (Eq q n + Lq q n) with hΨ
  have hΨ0 : ∀ n, 0 ≤ Ψ n := fun n => Finset.sum_nonneg fun q _ => add_nonneg (hEq0 q n) (hLq0 q n)
  refine ⟨r, hr0, hr12, hrζ.trans (by rw [hζ]), fun n => C * A * J * Ψ n, fun n => by
    have := hΨ0 n; positivity, ?_, ?_⟩
  · refine Summable.mul_left _ (summable_sum fun q _ => Summable.add ?_ ?_)
    · obtain ⟨n1, hn1⟩ := exists_pow_lt_of_lt_one (by positivity : 0 < ζ / 4) (by norm_num : (1 : ℝ) / 2 < 1)
      refine summable_of_ne_finset_zero (s := Finset.range n1) fun n hn => ?_
      rw [Finset.mem_range, not_lt] at hn
      have : u n < ζ / 4 := lt_of_le_of_lt (pow_le_pow_of_le_one (by norm_num) (by norm_num) hn) hn1
      simp only [hEq]; rw [if_neg (not_le.2 this)]
    · have h1 := (r26t8a_p07_geom_log b hδ).mul_left (ζ ^ (2 - (d : ℝ) - (q : ℝ)) * (4 + |Real.log ζ|))
      have h2 := (r26t8a_p07_geom_log (b + 1) hδ).mul_left (ζ ^ (2 - (d : ℝ) - (q : ℝ)))
      refine (h1.add h2).congr fun n => ?_
      simp only [hLq, hℓ, hu, pow_succ]
      ring
  · intro n i j hij Y hY w hw
    have hwz : ζ ≤ ‖w‖ := by
      have := norm_sub_norm_le z w
      rw [norm_sub_rev] at this
      have : ‖w - z‖ < ζ := lt_of_lt_of_le hw hrζ
      have := norm_sub_norm_le z w; rw [norm_sub_rev z w] at this
      linarith [norm_sub_rev w z]
    have hw4 : ‖w‖ ≤ 4 := by
      have := norm_le_insert' w z; linarith
    have hw0 : 0 < ‖w‖ := lt_of_lt_of_le hζ0 hwz
    have hjb : jbracket Y ^ (2 * M) ≤ J := by
      have h1 : jbracket Y ≤ 3 * jbracket X := by
        have e : Y = X + (Y - X) := by abel
        have := r26t8a_jb_shift' X (Y - X)
        rw [← e] at this
        have : ‖Y - X‖ < 1 := by linarith
        nlinarith [s83_jb_pos X, norm_nonneg (Y - X), r26t8a_jb_shift' X (Y - X)]
      calc jbracket Y ^ (2 * M) ≤ (3 * jbracket X) ^ (2 * M) :=
            Real.rpow_le_rpow (s83_jb_pos Y).le h1 (by linarith)
        _ = J := by rw [hJ, Real.mul_rpow (by norm_num) (s83_jb_pos X).le]
    have hjb0 : 0 ≤ jbracket Y ^ (2 * M) := Real.rpow_nonneg (s83_jb_pos Y).le _
    have hterm := hC A hA F hF n i j hij Y w hw0
    -- compare the envelope with Eq + Lq
    have hβ : r26t8a_p07_beta d b j σ ‖w‖ n ≤ Eq j n + Lq j n := by
      unfold r26t8a_p07_beta
      by_cases h : ((1 : ℝ) / 2) ^ n ≤ ‖w‖ / 4
      · rw [if_pos h]
        have hlog : |Real.log ‖w‖| ≤ |Real.log ζ| + 3 := by
          rcases le_total 1 ‖w‖ with h1 | h1
          · have : Real.log ‖w‖ ≤ Real.log 4 := Real.log_le_log hw0 hw4
            have h3 : Real.log 4 ≤ 3 := by
              have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4); linarith
            rw [abs_of_nonneg (Real.log_nonneg h1)]
            linarith [abs_nonneg (Real.log ζ)]
          · have : Real.log ζ ≤ Real.log ‖w‖ := Real.log_le_log hζ0 hwz
            have h4 := Real.log_nonpos hw0.le h1
            rw [abs_of_nonpos h4]
            have := neg_abs_le (Real.log ζ)
            linarith
        have hpow : ‖w‖ ^ (2 - (d : ℝ) - (j : ℝ)) ≤ ζ ^ (2 - (d : ℝ) - (j : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos hζ0 hwz (by
            have : (2 : ℝ) ≤ d := by exact_mod_cast hd
            have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
            linarith)
        have hL0 : 0 ≤ (ℓ n) ^ b := pow_nonneg (hℓ0 n) _
        have hu1 : 0 ≤ (u n) ^ ((d : ℝ) - σ) := Real.rpow_nonneg (hu0 n).le _
        have hz1 : 0 ≤ ζ ^ (2 - (d : ℝ) - (j : ℝ)) := Real.rpow_nonneg hζ0.le _
        have hLj : (u n) ^ ((d : ℝ) - σ) * ‖w‖ ^ (2 - (d : ℝ) - (j : ℝ)) * (ℓ n) ^ b *
            (if d = 2 ∧ j = 0 then ℓ n + |Real.log ‖w‖| else 1) ≤ Lq j n := by
          simp only [hLq]
          have hs : (if d = 2 ∧ j = 0 then ℓ n + |Real.log ‖w‖| else 1) ≤ 4 + ℓ n + |Real.log ζ| := by
            split_ifs
            · linarith
            · linarith [hℓ0 n, abs_nonneg (Real.log ζ)]
          have hs0 : 0 ≤ (if d = 2 ∧ j = 0 then ℓ n + |Real.log ‖w‖| else 1) := by
            split_ifs
            · exact add_nonneg (hℓ0 n) (abs_nonneg _)
            · exact zero_le_one
          calc _ ≤ (u n) ^ ((d : ℝ) - σ) * ζ ^ (2 - (d : ℝ) - (j : ℝ)) * (ℓ n) ^ b *
                (if d = 2 ∧ j = 0 then ℓ n + |Real.log ‖w‖| else 1) := by gcongr
            _ ≤ _ := by gcongr
        have hform : ((u n) ^ ((d : ℝ) - σ) * ‖w‖ ^ (2 - (d : ℝ) - (j : ℝ))) * (ℓ n) ^ b *
            (if d = 2 ∧ j = 0 then 1 + |Real.log (u n)| + |Real.log ‖w‖| else 1) =
            (u n) ^ ((d : ℝ) - σ) * ‖w‖ ^ (2 - (d : ℝ) - (j : ℝ)) * (ℓ n) ^ b *
              (if d = 2 ∧ j = 0 then ℓ n + |Real.log ‖w‖| else 1) := by
          split_ifs <;> simp only [hℓ] <;> ring
        simp only [hu] at hform hLj ⊢
        have := hEq0 j n
        linarith [hform ▸ hLj]
      · rw [if_neg h]
        push Not at h
        have hE : ζ / 4 ≤ u n := by
          have : ζ / 4 ≤ ‖w‖ / 4 := by linarith
          simp only [hu] at h ⊢; linarith
        have hs : (if d = 2 ∧ j = 0 then 1 + |Real.log (((1 : ℝ) / 2) ^ n)| else 1) ≤ 1 + ℓ n := by
          split_ifs
          · simp only [hℓ, hu]; linarith [abs_nonneg (Real.log (((1 : ℝ) / 2) ^ n))]
          · linarith [hℓ0 n]
        have hs0 : 0 ≤ (if d = 2 ∧ j = 0 then 1 + |Real.log (((1 : ℝ) / 2) ^ n)| else 1) := by
          split_ifs
          · positivity
          · exact zero_le_one
        have h1 : 0 ≤ (((1 : ℝ) / 2) ^ n) ^ (2 - σ - (j : ℝ)) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b := by
          have := hu0 n; simp only [hu] at this; positivity
        have : Eq j n = (((1 : ℝ) / 2) ^ n) ^ (2 - σ - (j : ℝ)) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b *
            (1 + ℓ n) := by simp only [hEq, hu, hℓ]; rw [if_pos (by simpa [hu] using hE)]
        have hLn := hLq0 j n
        calc (((1 : ℝ) / 2) ^ n) ^ (2 - σ - (j : ℝ)) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b *
              (if d = 2 ∧ j = 0 then 1 + |Real.log (((1 : ℝ) / 2) ^ n)| else 1)
            ≤ (((1 : ℝ) / 2) ^ n) ^ (2 - σ - (j : ℝ)) * (1 + |Real.log (((1 : ℝ) / 2) ^ n)|) ^ b *
              (1 + ℓ n) := mul_le_mul_of_nonneg_left hs h1
          _ = Eq j n := this.symm
          _ ≤ Eq j n + Lq j n := le_add_of_nonneg_right hLn
    have hΨj : Eq j n + Lq j n ≤ Ψ n :=
      Finset.single_le_sum (f := fun q => Eq q n + Lq q n) (fun q _ => add_nonneg (hEq0 q n) (hLq0 q n))
        (Finset.mem_range.2 (by omega))
    have hAJ : 0 ≤ C * A := mul_nonneg hC0 hA
    calc ‖r26t8a_nest i j (fun Yw : Euc d × Euc d =>
            r26t8a_annularNewton nu chi (((1 : ℝ) / 2) ^ n) F Yw.1 Yw.2) Y w‖
        ≤ C * A * jbracket Y ^ (2 * M) * r26t8a_p07_beta d b j σ ‖w‖ n := hterm
      _ ≤ C * A * J * Ψ n := by
          have hβ0 : 0 ≤ r26t8a_p07_beta d b j σ ‖w‖ n := by
            have := hu0 n; have := hℓ0 n
            unfold r26t8a_p07_beta
            have hl' : 0 ≤ 1 + |Real.log (((1 : ℝ) / 2) ^ n)| := by positivity
            have hp : 0 < ((1 : ℝ) / 2) ^ n := by positivity
            split_ifs <;> positivity
          calc C * A * jbracket Y ^ (2 * M) * r26t8a_p07_beta d b j σ ‖w‖ n
              ≤ C * A * J * r26t8a_p07_beta d b j σ ‖w‖ n :=
                mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hjb hAJ) hβ0
            _ ≤ C * A * J * Ψ n := mul_le_mul_of_nonneg_left (hβ.trans hΨj) (by positivity)

end HRS.MS.R26T8A
