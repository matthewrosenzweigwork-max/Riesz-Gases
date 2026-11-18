import HRS.MS.SA12X2P

/-!
# S.A.12 N8 (SA12X2), part Q: pointwise bounds of the second-order Leibniz remainder `L` and its gradient

`L(σ) = ∂^σ(c K) - c ∂^σ K` with `c = ∂_l a`, `K = ∂_j ∂^t F`: `|L| ≤ K_L T_m F`, `|∂_p L| ≤ K_L T_m F`
(`T_m F = ∑ jets`), when `|σ| + |t| + 1 ≤ m`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3

variable {d : ℕ}

theorem sa12x2_norm_D1' {G : Euc d → ℝ} {k : ℕ} (hG : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) G)
    (p : Fin d) (y : Euc d) :
    ‖iteratedFDeriv ℝ k (D1 p G) y‖ ≤ ‖iteratedFDeriv ℝ (k + 1) G y‖ := by
  set Lp : (Euc d →L[ℝ] ℝ) →L[ℝ] ℝ := ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single p (1 : ℝ))
  have hL : ‖Lp‖ ≤ 1 := by
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun L => ?_)
    have := L.le_opNorm (EuclideanSpace.single p (1 : ℝ))
    simpa [Lp, PiLp.norm_single] using this
  have hf : ContDiff ℝ k (fderiv ℝ G) := hG.fderiv_right (m := k) (by push_cast; rfl)
  have e : D1 p G = Lp ∘ fderiv ℝ G := rfl
  rw [e]
  refine (Lp.norm_iteratedFDeriv_comp_left (N := (k : ℕ∞ω)) hf.contDiffAt le_rfl).trans ?_
  rw [← norm_iteratedFDeriv_fderiv]
  calc ‖Lp‖ * ‖iteratedFDeriv ℝ k (fderiv ℝ G) y‖ ≤ 1 * ‖iteratedFDeriv ℝ k (fderiv ℝ G) y‖ :=
        mul_le_mul_of_nonneg_right hL (norm_nonneg _)
    _ = _ := one_mul _

/-- Jets of `F` bounded by `T_m F`. -/
theorem sa12x2_iter_le_T {m : ℕ} {F : Euc d → ℝ} (j : ℕ) (hj : j ≤ m) (y : Euc d) :
    ‖iteratedFDeriv ℝ j F y‖ ≤ sa12z3_T m F y :=
  (sa12z3_norm_iter_le F y j).trans (sa12z3_sum_pd_le_T hj F y)

/-- The remainder `L`. -/
def sa12x2_L (c K : Euc d → ℝ) {r : ℕ} (σ : Fin r → Fin d) (y : Euc d) : ℝ :=
  partialDeriv σ (fun z => c z * K z) y - c y * partialDeriv σ K y

theorem sa12x2_L_pt {m : ℕ} {a F : Euc d → ℝ} (ha : ContDiff ℝ (m + 1) a) (hF : ContDiff ℝ ∞ F)
    {Ka : ℝ} (hKa : ∀ k ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ k a x‖ ≤ Ka) (l j : Fin d) {r s : ℕ}
    (hrs : r + s ≤ m) (σ : Fin r → Fin d) (t : Fin s → Fin d) (y : Euc d) :
    |sa12x2_L (D1 l a) (D1 j (partialDeriv t F)) σ y| ≤ Ka * 2 ^ m * sa12z3_T m F y := by
  have hKa0 : 0 ≤ Ka := (norm_nonneg _).trans (hKa 0 (Nat.zero_le _) y)
  have hG : ContDiff ℝ ∞ (partialDeriv t F) := sa12z3_pd_contDiff_inf hF t
  have hK : ContDiff ℝ ∞ (D1 j (partialDeriv t F)) :=
    (hG.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hc : ContDiff ℝ r (D1 l a) :=
    (ha.fderiv_right (m := r) (by exact_mod_cast (by omega : r + 1 ≤ m + 1))).clm_apply contDiff_const
  have h1 := sa12z3_leib_diff hc (sa12z3_cd_of_inf hK r) σ y
  unfold sa12x2_L
  refine h1.trans ?_
  have hT0 := sa12z3_T_nonneg m F y
  have hterm : ∀ k ∈ Finset.range (r + 1), (if k = 0 then (0 : ℝ) else
      (r.choose k : ℝ) * ‖iteratedFDeriv ℝ k (D1 l a) y‖ *
        ‖iteratedFDeriv ℝ (r - k) (D1 j (partialDeriv t F)) y‖) ≤
      (r.choose k : ℝ) * (Ka * sa12z3_T m F y) := by
    intro k hk
    by_cases hk0 : k = 0
    · rw [if_pos hk0]; positivity
    · rw [if_neg hk0]
      have hkr : k ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)
      have hka : ‖iteratedFDeriv ℝ k (D1 l a) y‖ ≤ Ka := by
        refine (sa12x2_norm_D1' (k := k) (ha.of_le (by exact_mod_cast (by omega : k + 1 ≤ m + 1))) l y).trans
          (hKa (k + 1) (by omega) y)
      have hkk : ‖iteratedFDeriv ℝ (r - k) (D1 j (partialDeriv t F)) y‖ ≤ sa12z3_T m F y := by
        refine (sa12x2_norm_D1' (k := r - k) (sa12z3_cd_of_inf hG _) j y).trans ?_
        refine (sa12x2_jet hF s (r - k + 1) t y).trans (sa12x2_iter_le_T _ (by omega) y)
      calc (r.choose k : ℝ) * ‖iteratedFDeriv ℝ k (D1 l a) y‖ *
            ‖iteratedFDeriv ℝ (r - k) (D1 j (partialDeriv t F)) y‖
          ≤ (r.choose k : ℝ) * Ka * sa12z3_T m F y := by gcongr
        _ = _ := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  have hsum : ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ) * (Ka * sa12z3_T m F y) =
      2 ^ r * (Ka * sa12z3_T m F y) := by
    rw [← Finset.sum_mul]
    congr 1
    exact_mod_cast Nat.sum_range_choose r
  rw [hsum]
  have h2 : (2 : ℝ) ^ r ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) (by omega)
  calc (2 : ℝ) ^ r * (Ka * sa12z3_T m F y) ≤ 2 ^ m * (Ka * sa12z3_T m F y) :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = _ := by ring


theorem sa12x2_L_grad {m : ℕ} {a F : Euc d → ℝ} (ha : ContDiff ℝ (m + 1) a) (hF : ContDiff ℝ ∞ F)
    {Ka : ℝ} (hKa : ∀ k ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ k a x‖ ≤ Ka) (l j : Fin d) {r s : ℕ}
    (hrs : r + s + 1 ≤ m) (σ : Fin r → Fin d) (t : Fin s → Fin d) (p : Fin d) (y : Euc d) :
    |D1 p (fun z => sa12x2_L (D1 l a) (D1 j (partialDeriv t F)) σ z) y| ≤
      Ka * (2 ^ m + 1) * sa12z3_T m F y := by
  have hKa0 : 0 ≤ Ka := (norm_nonneg _).trans (hKa 0 (Nat.zero_le _) y)
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
  have e := sa12x2_D1_sub_mul (P := partialDeriv σ (fun z => D1 l a z * D1 j (partialDeriv t F) z))
    (a := D1 l a) (K := partialDeriv σ (D1 j (partialDeriv t F))) p y
    (hP1.differentiable one_ne_zero y) (hc1.differentiable one_ne_zero y)
    (hK1.differentiable one_ne_zero y)
  have e2 : D1 p (fun z => sa12x2_L (D1 l a) (D1 j (partialDeriv t F)) σ z) y =
      sa12x2_L (D1 l a) (D1 j (partialDeriv t F)) (Fin.cons p σ : Fin (r + 1) → Fin d) y -
        D1 p (D1 l a) y * partialDeriv σ (D1 j (partialDeriv t F)) y := by
    unfold sa12x2_L
    rw [show (fun z => partialDeriv σ (fun z => D1 l a z * D1 j (partialDeriv t F) z) z -
      D1 l a z * partialDeriv σ (D1 j (partialDeriv t F)) z) = fun z => partialDeriv σ
      (fun z => D1 l a z * D1 j (partialDeriv t F) z) z - D1 l a z *
      partialDeriv σ (D1 j (partialDeriv t F)) z from rfl, e,
      sa12z3_pd_cons σ p hcK y, sa12z3_pd_cons σ p (sa12z3_cd_of_inf hK _) y]
    ring
  rw [e2]
  have b1 := sa12x2_L_pt ha hF hKa l j (r := r + 1) (s := s) (by omega) (Fin.cons p σ) t y
  have b2 : |D1 p (D1 l a) y| ≤ Ka := by
    refine (sa12z3_D1_le p _ y).trans ?_
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ)]
    exact (sa12x2_norm_D1' (k := 1) (ha.of_le (by exact_mod_cast (by omega : 2 ≤ m + 1))) l y).trans
      (hKa 2 (by omega) y)
  have b3 : |partialDeriv σ (D1 j (partialDeriv t F)) y| ≤ sa12z3_T m F y := by
    refine (sa12z3_pd_le_norm _ y σ).trans ?_
    refine (sa12x2_norm_D1' (k := r) (sa12z3_cd_of_inf hG _) j y).trans ?_
    exact (sa12x2_jet hF s (r + 1) t y).trans (sa12x2_iter_le_T _ (by omega) y)
  have hT0 := sa12z3_T_nonneg m F y
  calc |sa12x2_L (D1 l a) (D1 j (partialDeriv t F)) (Fin.cons p σ : Fin (r + 1) → Fin d) y -
        D1 p (D1 l a) y * partialDeriv σ (D1 j (partialDeriv t F)) y|
      ≤ |sa12x2_L (D1 l a) (D1 j (partialDeriv t F)) (Fin.cons p σ : Fin (r + 1) → Fin d) y| +
        |D1 p (D1 l a) y| * |partialDeriv σ (D1 j (partialDeriv t F)) y| := by
        refine (abs_sub _ _).trans ?_
        rw [abs_mul]
    _ ≤ Ka * 2 ^ m * sa12z3_T m F y + Ka * sa12z3_T m F y :=
        add_le_add b1 (mul_le_mul b2 b3 (abs_nonneg _) hKa0)
    _ = _ := by ring

end HRS.MH.AdjointRd.Phase2SA12Near
