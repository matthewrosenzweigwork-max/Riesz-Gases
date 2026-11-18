import HRS.MS.SA12X2Q

/-!
# S.A.12 N8 (SA12X2), part R: weighted `L²` comparison and regularity/support of `L`
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3

variable {d : ℕ}

/-- `∫ g² ≤ K² c_T ∫ W Y` for `|g| ≤ K T` supported where `W ≥ 1`. -/
theorem sa12x2_wl2 {m : ℕ} {W g F : Euc d → ℝ} {K : ℝ} (hW : Continuous W) (hWcs : HasCompactSupport W)
    (hF : ContDiff ℝ ∞ F) (hg : Continuous g) (hgc : HasCompactSupport g)
    (hg1 : ∀ y, g y ≠ 0 → 1 ≤ W y) (hb : ∀ y, |g y| ≤ K * sa12z3_T m F y) (hW0 : ∀ y, 0 ≤ W y) :
    ∫ x, g x ^ 2 ≤ K ^ 2 * sa12z3_cT d m * ∫ x, W x * sa12z3_Y m F x := by
  have hYc : Continuous (sa12z3_Y m F) := by
    unfold sa12z3_Y
    refine continuous_finsetSum _ fun r _ => continuous_finsetSum _ fun γ _ => ?_
    exact ((sa12z3_pd_contDiff_inf hF γ).continuous).pow 2
  have hWYi : Integrable (fun x => W x * sa12z3_Y m F x) volume :=
    (hW.mul hYc).integrable_of_hasCompactSupport hWcs.mul_right
  have hgi : Integrable (fun x => g x ^ 2) volume :=
    Continuous.integrable_of_hasCompactSupport (f := fun x => g x ^ 2) (hg.pow 2)
      (hgc.comp_left (g := fun t : ℝ => t ^ 2) (by simp))
  rw [← integral_const_mul]
  refine integral_mono hgi (hWYi.const_mul _) fun x => ?_
  by_cases hx : g x = 0
  · rw [hx]; simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (sa12z3_cT_nonneg d m))
      (mul_nonneg (hW0 x) (sa12z3_Y_nonneg _ _ _))
  · have hW1 := hg1 x hx
    have hT := sa12z3_T_sq m F x
    have hY := sa12z3_Y_nonneg m F x
    calc g x ^ 2 = |g x| ^ 2 := (sq_abs _).symm
      _ ≤ (K * sa12z3_T m F x) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hb x) 2
      _ = K ^ 2 * sa12z3_T m F x ^ 2 := by ring
      _ ≤ K ^ 2 * (sa12z3_cT d m * sa12z3_Y m F x) := by gcongr
      _ = K ^ 2 * sa12z3_cT d m * (1 * sa12z3_Y m F x) := by ring
      _ ≤ K ^ 2 * sa12z3_cT d m * (W x * sa12z3_Y m F x) := by
        have := sa12z3_cT_nonneg d m
        gcongr

/-- Jets of the square of a cutoff. -/
theorem sa12x2_sq_jets {om : Euc d → ℝ} (hom : ContDiff ℝ 2 om) {Kw : ℝ}
    (hKw : ∀ k ≤ 2, ∀ x, ‖iteratedFDeriv ℝ k om x‖ ≤ Kw) :
    ∀ j ≤ 2, ∀ x, ‖iteratedFDeriv ℝ j (fun y => om y ^ 2) x‖ ≤ 4 * Kw ^ 2 := by
  intro j hj x
  have hKw0 : 0 ≤ Kw := (norm_nonneg _).trans (hKw 0 (by omega) x)
  have e : (fun y => om y ^ 2) = fun y => om y * om y := by funext y; ring
  rw [e]
  have h1 := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (N := ((2 : ℕ) : WithTop ℕ∞)) (hf := hom) (hg := hom) x
    (n := j) (by exact_mod_cast hj)
  refine h1.trans ?_
  have hterm : ∀ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i om x‖ *
      ‖iteratedFDeriv ℝ (j - i) om x‖ ≤ (j.choose i : ℝ) * Kw ^ 2 := by
    intro i hi
    have hi' : i ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    calc (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i om x‖ * ‖iteratedFDeriv ℝ (j - i) om x‖
        ≤ (j.choose i : ℝ) * Kw * Kw := by
          gcongr
          · exact hKw i (by omega) x
          · exact hKw (j - i) (by omega) x
      _ = _ := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  have : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) = 2 ^ j := by exact_mod_cast Nat.sum_range_choose j
  rw [this]
  have h2 : (2 : ℝ) ^ j ≤ 4 := by
    calc (2 : ℝ) ^ j ≤ 2 ^ 2 := pow_le_pow_right₀ (by norm_num) hj
      _ = 4 := by norm_num
  exact mul_le_mul_of_nonneg_right h2 (sq_nonneg _)

/-- Regularity and compact support of `L`. -/
theorem sa12x2_L_reg {m : ℕ} {a F : Euc d → ℝ} (ha : ContDiff ℝ (m + 1) a) (hF : ContDiff ℝ ∞ F)
    {c0 : Euc d} {R : ℝ} (hasup : Function.support a ⊆ closedBall c0 R) (l j : Fin d) {r s : ℕ}
    (hrs : r + s + 1 ≤ m) (σ : Fin r → Fin d) (t : Fin s → Fin d) :
    ContDiff ℝ 1 (sa12x2_L (D1 l a) (D1 j (partialDeriv t F)) σ) ∧
      HasCompactSupport (sa12x2_L (D1 l a) (D1 j (partialDeriv t F)) σ) ∧
      Function.support (sa12x2_L (D1 l a) (D1 j (partialDeriv t F)) σ) ⊆ tsupport a := by
  have hG : ContDiff ℝ ∞ (partialDeriv t F) := sa12z3_pd_contDiff_inf hF t
  have hK : ContDiff ℝ ∞ (D1 j (partialDeriv t F)) :=
    (hG.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hc : ContDiff ℝ (r + 1) (D1 l a) :=
    (ha.fderiv_right (m := (r + 1 : ℕ)) (by exact_mod_cast (by omega : r + 1 + 1 ≤ m + 1))).clm_apply
      contDiff_const
  have hcK : ContDiff ℝ (r + 1) (fun z => D1 l a z * D1 j (partialDeriv t F) z) :=
    hc.mul (sa12z3_cd_of_inf hK _)
  have hP1 : ContDiff ℝ 1 (partialDeriv σ (fun z => D1 l a z * D1 j (partialDeriv t F) z)) := by
    have := sa12z3_pd_contDiff (k := r + 1) (n := r) hcK (by omega) σ
    simpa using this
  have hc1 : ContDiff ℝ 1 (D1 l a) := hc.of_le (by exact_mod_cast (by omega : 1 ≤ r + 1))
  have hK1 : ContDiff ℝ 1 (partialDeriv σ (D1 j (partialDeriv t F))) :=
    (sa12z3_pd_contDiff_inf hK σ).of_le (by exact_mod_cast le_top)
  have hsupp : Function.support (sa12x2_L (D1 l a) (D1 j (partialDeriv t F)) σ) ⊆ tsupport a := by
    intro y hy
    have hc_ts : tsupport (D1 l a) ⊆ tsupport a := by
      refine closure_minimal (fun z hz => ?_) (isClosed_tsupport a)
      have : fderiv ℝ a z ≠ 0 := fun h0 => hz (by simp [D1, h0])
      exact support_fderiv_subset (𝕜 := ℝ) (Function.mem_support.2 this)
    by_cases hcy : D1 l a y = 0
    · have h1 : partialDeriv σ (fun z => D1 l a z * D1 j (partialDeriv t F) z) y ≠ 0 := by
        intro h0
        apply hy
        unfold sa12x2_L
        rw [h0, hcy]; ring
      exact hc_ts (tsupport_mul_subset_left (sa12z3_pd_support σ (Function.mem_support.2 h1)))
    · exact hc_ts (subset_tsupport _ hcy)
  refine ⟨hP1.sub (hc1.mul hK1), ?_, hsupp⟩
  refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c0 R) fun y hy => ?_
  exact (closure_minimal hasup isClosed_closedBall) (hsupp hy)

end HRS.MH.AdjointRd.Phase2SA12Near
