import HRS.MS.MfeConfAux78

/-!
# S.B.1, packet F8 (part 11): weighted Lipschitz bound of the source on configuration space
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4Mol
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

theorem sb1_lv_avg_lip {gk : Euc d → Euc d} {L2 : ℝ} (hL2 : 0 ≤ L2) (hgk : ∀ z z', ‖gk z - gk z'‖ ≤ L2 * ‖z - z'‖)
    (Z Z' : EucConfig d N) (i : Fin N) :
    ‖(1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i, gk (Z i - Z j) -
      (1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i, gk (Z' i - Z' j)‖ ≤ 2 * L2 * ‖Z - Z'‖ := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; exact i.elim0
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← smul_sub, ← Finset.sum_sub_distrib, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hj : ∀ j ∈ Finset.univ.erase i, ‖gk (Z i - Z j) - gk (Z' i - Z' j)‖ ≤ 2 * L2 * ‖Z - Z'‖ := by
    intro j _
    refine (hgk _ _).trans ?_
    have h1 : ‖Z i - Z' i‖ ≤ ‖Z - Z'‖ := by simpa using norm_le_pi_norm (Z - Z') i
    have h2 : ‖Z j - Z' j‖ ≤ ‖Z - Z'‖ := by simpa using norm_le_pi_norm (Z - Z') j
    have : ‖Z i - Z j - (Z' i - Z' j)‖ ≤ 2 * ‖Z - Z'‖ := by
      calc ‖Z i - Z j - (Z' i - Z' j)‖ = ‖(Z i - Z' i) - (Z j - Z' j)‖ := by congr 1; abel
        _ ≤ ‖Z i - Z' i‖ + ‖Z j - Z' j‖ := norm_sub_le _ _
        _ ≤ 2 * ‖Z - Z'‖ := by linarith
    calc L2 * ‖Z i - Z j - (Z' i - Z' j)‖ ≤ L2 * (2 * ‖Z - Z'‖) := mul_le_mul_of_nonneg_left this hL2
      _ = _ := by ring
  have h1 : ‖∑ j ∈ Finset.univ.erase i, (gk (Z i - Z j) - gk (Z' i - Z' j))‖ ≤
      ∑ j ∈ Finset.univ.erase i, 2 * L2 * ‖Z - Z'‖ := (norm_sum_le _ _).trans (Finset.sum_le_sum hj)
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at h1
  have hc : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
  have hnn : 0 ≤ 2 * L2 * ‖Z - Z'‖ := by positivity
  calc 1 / (N : ℝ) * ‖∑ j ∈ Finset.univ.erase i, (gk (Z i - Z j) - gk (Z' i - Z' j))‖
      ≤ 1 / (N : ℝ) * (((N - 1 : ℕ) : ℝ) * (2 * L2 * ‖Z - Z'‖)) := mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ 1 / (N : ℝ) * ((N : ℝ) * (2 * L2 * ‖Z - Z'‖)) := by gcongr
    _ = 2 * L2 * ‖Z - Z'‖ := by field_simp

theorem sb1_lv_pairV_lip {gk u : Euc d → Euc d} {Lg L2 B1 K1 Ku : ℝ} (hLg : 0 ≤ Lg) (hL2 : 0 ≤ L2)
    (hB1 : 0 ≤ B1) (hK1 : 0 ≤ K1) (hKu : 0 ≤ Ku) (hgk : ∀ z, ‖gk z‖ ≤ Lg)
    (hgl : ∀ z z', ‖gk z - gk z'‖ ≤ L2 * ‖z - z'‖) (hu : ∀ x, ‖u x‖ ≤ B1 + K1 * ‖x‖)
    (hul : ∀ x y, ‖u x - u y‖ ≤ Ku * ‖x - y‖) (Z Z' : EucConfig d N) (i : Fin N) :
    |sb1_lv_pairV gk u Z i - sb1_lv_pairV gk u Z' i| ≤
      (Ku * Lg + 2 * L2 * (B1 + K1)) * ‖Z - Z'‖ * (1 + ‖Z‖ + ‖Z'‖) := by
  unfold sb1_lv_pairV
  set a := u (Z i)
  set a' := u (Z' i)
  set b := (1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i, gk (Z i - Z j)
  set b' := (1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i, gk (Z' i - Z' j)
  have e : inner ℝ a b - inner ℝ a' b' = inner ℝ (a - a') b + inner ℝ a' (b - b') := by
    simp only [inner_sub_left, inner_sub_right]; ring
  rw [e]
  have h1 : ‖a - a'‖ ≤ Ku * ‖Z - Z'‖ := by
    refine (hul _ _).trans (mul_le_mul_of_nonneg_left ?_ hKu)
    simpa using norm_le_pi_norm (Z - Z') i
  have h2 := sb1_lv_avg_norm_le hgk Z i
  have h3 := sb1_lv_avg_lip hL2 hgl Z Z' i
  have h4 : ‖a'‖ ≤ (B1 + K1) * (1 + ‖Z'‖) := by
    have := hu (Z' i)
    have h5 : ‖Z' i‖ ≤ ‖Z'‖ := norm_le_pi_norm Z' i
    nlinarith [norm_nonneg (Z' i), norm_nonneg Z']
  calc |inner ℝ (a - a') b + inner ℝ a' (b - b')| ≤ |inner ℝ (a - a') b| + |inner ℝ a' (b - b')| := abs_add_le _ _
    _ ≤ ‖a - a'‖ * ‖b‖ + ‖a'‖ * ‖b - b'‖ :=
        add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ ≤ (Ku * ‖Z - Z'‖) * Lg + ((B1 + K1) * (1 + ‖Z'‖)) * (2 * L2 * ‖Z - Z'‖) := by
        gcongr
    _ ≤ _ := by
        have hz : 0 ≤ ‖Z - Z'‖ := norm_nonneg _
        have hz1 : 0 ≤ ‖Z‖ := norm_nonneg _
        have hz2 : 0 ≤ ‖Z'‖ := norm_nonneg _
        nlinarith [mul_nonneg hz hz1, mul_nonneg hz hz2, mul_nonneg (mul_nonneg hKu hLg) hz,
          mul_nonneg (mul_nonneg (mul_nonneg hL2 (add_nonneg hB1 hK1)) hz) hz2,
          mul_nonneg (mul_nonneg hKu hLg) (mul_nonneg hz hz1), mul_nonneg (mul_nonneg hKu hLg) (mul_nonneg hz hz2),
          mul_nonneg (mul_nonneg hL2 (add_nonneg hB1 hK1)) (mul_nonneg hz hz1)]

theorem sb1_lv_Src_lip {θ : ℝ} (hθ : 0 < θ) {gk u : Euc d → Euc d} {Θ : Euc d → ℝ} {Lg L2 B1 K1 Ku DΘ c : ℝ}
    (hLg : 0 ≤ Lg) (hL2 : 0 ≤ L2) (hB1 : 0 ≤ B1) (hK1 : 0 ≤ K1) (hKu : 0 ≤ Ku) (hDΘ : 0 ≤ DΘ)
    (hgk : ∀ z, ‖gk z‖ ≤ Lg) (hgl : ∀ z z', ‖gk z - gk z'‖ ≤ L2 * ‖z - z'‖) (hu : ∀ x, ‖u x‖ ≤ B1 + K1 * ‖x‖)
    (hul : ∀ x y, ‖u x - u y‖ ≤ Ku * ‖x - y‖)
    (hΘl : ∀ x y, |Θ x - Θ y| ≤ DΘ * ‖x - y‖ * (1 + ‖x‖ + ‖y‖)) (Z Z' : EucConfig d N) :
    |sb1_lv_Src θ N gk u Θ c Z - sb1_lv_Src θ N gk u Θ c Z'| ≤
      (N * (DΘ + Ku * Lg + 2 * L2 * (B1 + K1)) / θ) * ‖Z - Z'‖ * (1 + ‖Z‖ + ‖Z'‖) := by
  unfold sb1_lv_Src
  rw [add_sub_add_right_eq_sub, ← Finset.sum_sub_distrib]
  have hi : ∀ i : Fin N, |(Θ (Z i) - sb1_lv_pairV gk u Z i) / θ - (Θ (Z' i) - sb1_lv_pairV gk u Z' i) / θ| ≤
      (DΘ + Ku * Lg + 2 * L2 * (B1 + K1)) / θ * (‖Z - Z'‖ * (1 + ‖Z‖ + ‖Z'‖)) := by
    intro i
    have e : (Θ (Z i) - sb1_lv_pairV gk u Z i) / θ - (Θ (Z' i) - sb1_lv_pairV gk u Z' i) / θ =
        ((Θ (Z i) - Θ (Z' i)) - (sb1_lv_pairV gk u Z i - sb1_lv_pairV gk u Z' i)) / θ := by ring
    rw [e, abs_div, abs_of_pos hθ]
    have hd1 : ‖Z i - Z' i‖ ≤ ‖Z - Z'‖ := by simpa using norm_le_pi_norm (Z - Z') i
    have hz : 0 ≤ ‖Z - Z'‖ := norm_nonneg _
    have hw : 1 + ‖Z i‖ + ‖Z' i‖ ≤ 1 + ‖Z‖ + ‖Z'‖ := by
      have := norm_le_pi_norm Z i; have := norm_le_pi_norm Z' i; linarith
    have h1 : |Θ (Z i) - Θ (Z' i)| ≤ DΘ * (‖Z - Z'‖ * (1 + ‖Z‖ + ‖Z'‖)) := by
      refine (hΘl _ _).trans ?_
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left (mul_le_mul hd1 hw (by positivity) hz) hDΘ
    have h2 := sb1_lv_pairV_lip hLg hL2 hB1 hK1 hKu hgk hgl hu hul Z Z' i
    rw [mul_assoc] at h2
    rw [div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ hθ.le
    calc |(Θ (Z i) - Θ (Z' i)) - (sb1_lv_pairV gk u Z i - sb1_lv_pairV gk u Z' i)| ≤
        |Θ (Z i) - Θ (Z' i)| + |sb1_lv_pairV gk u Z i - sb1_lv_pairV gk u Z' i| := abs_sub _ _
      _ ≤ _ := by nlinarith
  calc |∑ i, ((Θ (Z i) - sb1_lv_pairV gk u Z i) / θ - (Θ (Z' i) - sb1_lv_pairV gk u Z' i) / θ)|
      ≤ ∑ i : Fin N, |(Θ (Z i) - sb1_lv_pairV gk u Z i) / θ - (Θ (Z' i) - sb1_lv_pairV gk u Z' i) / θ| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin N, (DΘ + Ku * Lg + 2 * L2 * (B1 + K1)) / θ * (‖Z - Z'‖ * (1 + ‖Z‖ + ‖Z'‖)) :=
        Finset.sum_le_sum fun i _ => hi i
    _ = _ := by simp [Finset.sum_const]; ring

end HRS.MS.MfeConf
