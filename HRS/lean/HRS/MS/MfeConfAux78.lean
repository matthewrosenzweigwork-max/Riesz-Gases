import HRS.MS.MfeConfAux77

/-!
# S.B.1, packet F8 (part 10): bounds of the source on configuration space from one-body bounds

`sb1_lv_Src θ N gk u Θ c Z = ∑_i (Θ(Z_i) - ⟨u(Z_i), N⁻¹∑_{j≠i} gk(Z_i - Z_j)⟩)/θ + c` is the form of the source of the level-`k`
entropy inequality (`gk = ∇k`, `Θ` the one-body part, `c = κ'/θ`).  From one-body bounds:

* `sb1_lv_Src_bound`: `|Src Z| ≤ CS (1 + ∑_i |Z_i|²)` (`CS = (N(cΘ + Lg(B1+K1)) + |c|θ)/θ`);
* `sb1_lv_Src_lip`: `|Src Z - Src Z'| ≤ DS |Z-Z'| (1 + |Z| + |Z'|)`.
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4Mol
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

/-- `⟨u(Z_i), N⁻¹ ∑_{j≠i} gk(Z_i - Z_j)⟩` -/
def sb1_lv_pairV (gk u : Euc d → Euc d) (Z : EucConfig d N) (i : Fin N) : ℝ :=
  inner ℝ (u (Z i)) ((1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i, gk (Z i - Z j))

/-- the source in terms of the one-body data -/
def sb1_lv_Src (θ : ℝ) (N : ℕ) (gk u : Euc d → Euc d) (Θ : Euc d → ℝ) (c : ℝ) (Z : EucConfig d N) : ℝ :=
  ∑ i, (Θ (Z i) - sb1_lv_pairV gk u Z i) / θ + c

theorem sb1_lv_avg_norm_le {gk : Euc d → Euc d} {Lg : ℝ} (hgk : ∀ z, ‖gk z‖ ≤ Lg) (Z : EucConfig d N) (i : Fin N) :
    ‖(1 / (N : ℝ)) • ∑ j ∈ Finset.univ.erase i, gk (Z i - Z j)‖ ≤ Lg := by
  have hL : 0 ≤ Lg := (norm_nonneg _).trans (hgk 0)
  rw [norm_smul]
  have h1 : ‖∑ j ∈ Finset.univ.erase i, gk (Z i - Z j)‖ ≤ ∑ j ∈ Finset.univ.erase i, Lg :=
    (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hgk _)
  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at h1
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN; exact i.elim0
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  have : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
  calc 1 / (N : ℝ) * ‖∑ j ∈ Finset.univ.erase i, gk (Z i - Z j)‖ ≤ 1 / (N : ℝ) * (((N - 1 : ℕ) : ℝ) * Lg) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ 1 / (N : ℝ) * ((N : ℝ) * Lg) := by gcongr
    _ = Lg := by field_simp

theorem sb1_lv_pairV_abs {gk u : Euc d → Euc d} {Lg B1 K1 : ℝ} (hgk : ∀ z, ‖gk z‖ ≤ Lg)
    (hu : ∀ x, ‖u x‖ ≤ B1 + K1 * ‖x‖) (Z : EucConfig d N) (i : Fin N) :
    |sb1_lv_pairV gk u Z i| ≤ (B1 + K1 * ‖Z i‖) * Lg := by
  unfold sb1_lv_pairV
  refine (abs_real_inner_le_norm _ _).trans ?_
  exact mul_le_mul (hu _) (sb1_lv_avg_norm_le hgk Z i) (norm_nonneg _) ((norm_nonneg _).trans (hu (Z i)))

theorem sb1_lv_Src_bound {θ : ℝ} (hθ : 0 < θ) {gk u : Euc d → Euc d} {Θ : Euc d → ℝ} {Lg B1 K1 cΘ c : ℝ}
    (hLg : 0 ≤ Lg) (hB1 : 0 ≤ B1) (hK1 : 0 ≤ K1) (hcΘ : 0 ≤ cΘ) (hgk : ∀ z, ‖gk z‖ ≤ Lg)
    (hu : ∀ x, ‖u x‖ ≤ B1 + K1 * ‖x‖) (hΘ : ∀ x, |Θ x| ≤ cΘ * (1 + ‖x‖ ^ 2)) (Z : EucConfig d N) :
    |sb1_lv_Src θ N gk u Θ c Z| ≤ ((N * (cΘ + Lg * (B1 + K1)) + |c| * θ) / θ) * (1 + p4m_q Z) := by
  unfold sb1_lv_Src
  have hq : 0 ≤ p4m_q Z := p4m_q_nonneg Z
  have hterm : ∀ i, |(Θ (Z i) - sb1_lv_pairV gk u Z i) / θ| ≤ (cΘ + Lg * (B1 + K1)) * (1 + ‖Z i‖ ^ 2) / θ := by
    intro i
    rw [abs_div, abs_of_pos hθ]
    refine div_le_div_of_nonneg_right ?_ hθ.le
    have h1 := hΘ (Z i)
    have h2 := sb1_lv_pairV_abs hgk hu Z i
    have h3 : ‖Z i‖ ≤ 1 + ‖Z i‖ ^ 2 := by nlinarith [norm_nonneg (Z i), sq_nonneg (‖Z i‖ - 1)]
    have h4 : (B1 + K1 * ‖Z i‖) * Lg ≤ Lg * (B1 + K1) * (1 + ‖Z i‖ ^ 2) := by
      have : B1 + K1 * ‖Z i‖ ≤ (B1 + K1) * (1 + ‖Z i‖ ^ 2) := by nlinarith [norm_nonneg (Z i), sq_nonneg ‖Z i‖]
      nlinarith
    calc |Θ (Z i) - sb1_lv_pairV gk u Z i| ≤ |Θ (Z i)| + |sb1_lv_pairV gk u Z i| := abs_sub _ _
      _ ≤ _ := by nlinarith
  have hsum : |∑ i, (Θ (Z i) - sb1_lv_pairV gk u Z i) / θ| ≤
      (cΘ + Lg * (B1 + K1)) * (N + p4m_q Z) / θ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum fun i _ => hterm i).trans (le_of_eq ?_))
    rw [← Finset.sum_div, ← Finset.mul_sum]
    congr 2
    simp [Finset.sum_add_distrib, p4m_q]
  have hNq : (N : ℝ) + p4m_q Z ≤ N * (1 + p4m_q Z) := by
    rcases Nat.eq_zero_or_pos N with hN | hN
    · subst hN; simp [p4m_q]
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    nlinarith
  calc |∑ i, (Θ (Z i) - sb1_lv_pairV gk u Z i) / θ + c| ≤ |∑ i, (Θ (Z i) - sb1_lv_pairV gk u Z i) / θ| + |c| :=
        abs_add_le _ _
    _ ≤ (cΘ + Lg * (B1 + K1)) * (N + p4m_q Z) / θ + |c| := by linarith
    _ ≤ (cΘ + Lg * (B1 + K1)) * (N * (1 + p4m_q Z)) / θ + |c| * (1 + p4m_q Z) := by
        have := mul_le_mul_of_nonneg_left hNq (by positivity : 0 ≤ cΘ + Lg * (B1 + K1))
        have h5 : 0 ≤ |c| * p4m_q Z := mul_nonneg (abs_nonneg _) hq
        have := div_le_div_of_nonneg_right this hθ.le
        linarith
    _ = ((N * (cΘ + Lg * (B1 + K1)) + |c| * θ) / θ) * (1 + p4m_q Z) := by field_simp

end HRS.MS.MfeConf
