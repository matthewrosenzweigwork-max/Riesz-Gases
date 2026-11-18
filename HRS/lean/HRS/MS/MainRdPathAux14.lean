import HRS.MS.MainRdPathAux13

/-!
# S.A.9, packet P3h: bounds for the tail function `sa9_Tm` of the gradient kernels

For `0 ≤ r ≤ t ≤ T` (and `sa9_Tm = 0` for `r ∉ [0,t]`): the uniform bound `K²`, the decay in `Lc`, the comparison of two
propagators through their `C_b^{m+1}` distance, and the Lipschitz comparison in the space variable.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdPath

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.HNegInfra HRS.MP.RdInit
  HRS.MP.RdMart HRS.MP.RdRem HRS.MP.RdProp HRS.MS.MainRdField

variable {d : ℕ}

theorem sa9_tsum_bessel (a : ℕ → ℝ) {C : ℝ} (hb : ∀ n, ∑ l ∈ Finset.range n, (a l) ^ 2 ≤ C ^ 2) (Lc : ℕ) :
    ∑' l, ENNReal.ofReal ((a (l + Lc)) ^ 2) ≤ ENNReal.ofReal (C ^ 2) := by
  calc ∑' l, ENNReal.ofReal ((a (l + Lc)) ^ 2)
      ≤ ∑' l, ENNReal.ofReal ((a l) ^ 2) :=
        ENNReal.tsum_comp_le_tsum_of_injective (add_left_injective Lc) (fun l => ENNReal.ofReal ((a l) ^ 2))
    _ ≤ ENNReal.ofReal (C ^ 2) := by
        rw [ENNReal.tsum_eq_iSup_nat]
        refine iSup_le fun n => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg fun l _ => sq_nonneg _]
        exact ENNReal.ofReal_le_ofReal (hb n)

section PropSec

variable {q m : ℕ} {T K : ℝ} {Cf : WholeCoeff d}

theorem sa9_propr_lin (hadj : AdjointInputOneD ((q : ℕ) : ℝ) m Cf T K) {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t)
    (htT : t ≤ T) :
    (∀ a b : mhn_Hc d, propagatorW Cf r t (mhn_phi (a + b)) =
      propagatorW Cf r t (mhn_phi a) + propagatorW Cf r t (mhn_phi b)) ∧
    (∀ (c : ℝ) (a : mhn_Hc d), propagatorW Cf r t (mhn_phi (c • a)) = c • propagatorW Cf r t (mhn_phi a)) := by
  refine ⟨fun a b => ?_, fun c a => ?_⟩
  · have := (hadj r t hr hrt htT _ (mhn_isSobolevTest_phi _ a)).2.2.1 _ (mhn_isSobolevTest_phi _ b) 1
    rw [mri_phi_add]
    simpa using this
  · have := (hadj r t hr hrt htT _ (mhn_isSobolevTest_phi _ a)).2.2.1 _ (mhn_isSobolevTest_phi _ a) (c - 1)
    have e : mhn_phi a + (c - 1) • mhn_phi a = c • mhn_phi a := by funext y; simp; ring
    rw [e] at this
    rw [mri_phi_smul, this]
    funext y; simp; ring

/-- The gradient component as a first partial derivative. -/
theorem sa9_Gr_eq {r t : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) (j : Fin d) (φ : Euc d → ℝ) (x : Euc d) :
    sa9_Gr Cf t j φ (r, x) = partialDeriv (fun _ : Fin 1 => j) (propagatorW Cf r t φ) x := by
  unfold sa9_Gr
  rw [if_pos hr, rpk_gradient_partial]

theorem sa9_Tm_le (hadj : AdjointInputOneD ((q : ℕ) : ℝ) (m + 1) Cf T K) (h : ℕ → mhn_Hc d)
    (hP : ∀ F : HNeg d ((q : ℕ) : ℝ), HasSum (fun n => (inner ℝ (mhn_rep ((q : ℕ) : ℝ) (h n)) F) ^ 2) (‖F‖ ^ 2))
    {t : ℝ} (htT : t ≤ T) (j : Fin d) (Lc : ℕ) (r : ℝ) (x : Euc d) :
    sa9_Tm h Cf t j Lc (r, x) ≤ ENNReal.ofReal (K ^ 2) := by
  by_cases hr : r ∈ Set.Icc (0 : ℝ) t
  swap
  · simp [sa9_Tm, sa9_Gr, hr]
  obtain ⟨hadd, hsmul⟩ := sa9_propr_lin hadj hr.1 hr.2 htT
  have hcd : ∀ a : mhn_Hc d, ContDiff ℝ 1 (propagatorW Cf r t (mhn_phi a)) := fun a =>
    ((hadj r t hr.1 hr.2 htT _ (mhn_isSobolevTest_phi _ a)).2.1).of_le (by exact_mod_cast Nat.le_add_left 1 m)
  have hb := sa9_bessel h hP (i := 1) (propagatorW Cf r t) (fun _ => j) x hadd hsmul hcd (C := K)
    (fun g => (hadj r t hr.1 hr.2 htT _ (mhn_isSobolevTest_phi _ g)).2.2.2 1 (Nat.le_add_left 1 m) _ x)
  unfold sa9_Tm
  have := sa9_tsum_bessel (fun l => sa9_Gr Cf t j (mhn_phi (h l)) (r, x)) (C := K)
    (fun n => by simpa [sa9_Gr_eq hr] using hb n) Lc
  exact this

theorem sa9_Tm_tendsto (hadj : AdjointInputOneD ((q : ℕ) : ℝ) (m + 1) Cf T K) (h : ℕ → mhn_Hc d)
    (hP : ∀ F : HNeg d ((q : ℕ) : ℝ), HasSum (fun n => (inner ℝ (mhn_rep ((q : ℕ) : ℝ) (h n)) F) ^ 2) (‖F‖ ^ 2))
    {t : ℝ} (htT : t ≤ T) (j : Fin d) (r : ℝ) (x : Euc d) :
    Tendsto (fun Lc => sa9_Tm h Cf t j Lc (r, x)) atTop (𝓝 0) := by
  unfold sa9_Tm
  refine ENNReal.tendsto_sum_nat_add (fun l => ENNReal.ofReal ((sa9_Gr Cf t j (mhn_phi (h l)) (r, x)) ^ 2)) ?_
  have := sa9_Tm_le hadj h hP htT j 0 r x
  unfold sa9_Tm at this
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (by simpa using this)

end PropSec

section Cmp

variable {q m : ℕ} {T K₁ K₂ : ℝ} {CfN CfL : WholeCoeff d}

theorem sa9_Tm_cmp (h : ℕ → mhn_Hc d)
    (hP : ∀ F : HNeg d ((q : ℕ) : ℝ), HasSum (fun n => (inner ℝ (mhn_rep ((q : ℕ) : ℝ) (h n)) F) ^ 2) (‖F‖ ^ 2))
    (hN : AdjointInputOneD ((q : ℕ) : ℝ) (m + 1) CfN T K₁) (hL : AdjointInputOneD ((q : ℕ) : ℝ) (m + 1) CfL T K₂)
    {t : ℝ} (htT : t ≤ T) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) {D : ℝ}
    (hdiff : ∀ g : mhn_Hc d,
      MemCb (m + 1) (fun x => propagatorW CfN r t (mhn_phi g) x - propagatorW CfL r t (mhn_phi g) x) ∧
        cbNorm (m + 1) (fun x => propagatorW CfN r t (mhn_phi g) x - propagatorW CfL r t (mhn_phi g) x) ≤
          D * HRS.Whole.sobolevNorm ((q : ℕ) : ℝ) (mhn_phi g)) (j : Fin d) (Lc : ℕ) (x : Euc d) :
    sa9_Tm h CfN t j Lc (r, x) ≤ 2 * sa9_Tm h CfL t j Lc (r, x) + 2 * ENNReal.ofReal (D ^ 2) := by
  obtain ⟨haddN, hsmulN⟩ := sa9_propr_lin hN hr.1 hr.2 htT
  obtain ⟨haddL, hsmulL⟩ := sa9_propr_lin hL hr.1 hr.2 htT
  set P : (Euc d → ℝ) → (Euc d → ℝ) := fun f y => propagatorW CfN r t f y - propagatorW CfL r t f y with hPdef
  have hcdN : ∀ g : mhn_Hc d, ContDiff ℝ 1 (propagatorW CfN r t (mhn_phi g)) := fun g =>
    ((hN r t hr.1 hr.2 htT _ (mhn_isSobolevTest_phi _ g)).2.1).of_le (by exact_mod_cast Nat.le_add_left 1 m)
  have hcdL : ∀ g : mhn_Hc d, ContDiff ℝ 1 (propagatorW CfL r t (mhn_phi g)) := fun g =>
    ((hL r t hr.1 hr.2 htT _ (mhn_isSobolevTest_phi _ g)).2.1).of_le (by exact_mod_cast Nat.le_add_left 1 m)
  have hadd : ∀ a b : mhn_Hc d, P (mhn_phi (a + b)) = P (mhn_phi a) + P (mhn_phi b) := by
    intro a b; funext y
    simp only [hPdef, haddN, haddL, Pi.add_apply]; ring
  have hsmul : ∀ (c : ℝ) (a : mhn_Hc d), P (mhn_phi (c • a)) = c • P (mhn_phi a) := by
    intro c a; funext y
    simp only [hPdef, hsmulN, hsmulL, Pi.smul_apply, smul_eq_mul]; ring
  have hcd : ∀ a : mhn_Hc d, ContDiff ℝ 1 (P (mhn_phi a)) := fun a => (hcdN a).sub (hcdL a)
  have hb := fun n => sa9_bessel h hP (i := 1) P (fun _ => j) x hadd hsmul hcd (C := D)
    (fun g => (sa9_partial_le_cb (hdiff g).1 (Nat.le_add_left 1 m) _ x).trans (hdiff g).2) n
  have hD : ∀ n, ∑ l ∈ Finset.range n, (sa9_Gr CfN t j (mhn_phi (h l)) (r, x) -
      sa9_Gr CfL t j (mhn_phi (h l)) (r, x)) ^ 2 ≤ D ^ 2 := by
    intro n
    refine le_of_eq_of_le (Finset.sum_congr rfl fun l _ => ?_) (hb n)
    rw [sa9_Gr_eq hr, sa9_Gr_eq hr]
    simp only [hPdef]
    rw [mri_partialDeriv_sub (hcdN _) (hcdL _)]
  exact sa9_tail_cmp _ _ Lc hD

theorem sa9_Tm_lip (hm : 1 ≤ m) (h : ℕ → mhn_Hc d) {Cf : WholeCoeff d} {K : ℝ}
    (hP : ∀ F : HNeg d ((q : ℕ) : ℝ), HasSum (fun n => (inner ℝ (mhn_rep ((q : ℕ) : ℝ) (h n)) F) ^ 2) (‖F‖ ^ 2))
    (hadj : AdjointInputOneD ((q : ℕ) : ℝ) (m + 1) Cf T K)
    {t : ℝ} (htT : t ≤ T) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) (j : Fin d) (Lc : ℕ) (x y : Euc d) :
    sa9_Tm h Cf t j Lc (r, x) ≤ 2 * sa9_Tm h Cf t j Lc (r, y) +
      2 * ENNReal.ofReal (((d : ℝ) * d * |K| * ‖x - y‖) ^ 2) := by
  obtain ⟨hadd, hsmul⟩ := sa9_propr_lin hadj hr.1 hr.2 htT
  have hcd1 : ∀ a : mhn_Hc d, ContDiff ℝ 1 (propagatorW Cf r t (mhn_phi a)) := fun a =>
    ((hadj r t hr.1 hr.2 htT _ (mhn_isSobolevTest_phi _ a)).2.1).of_le (by exact_mod_cast Nat.le_add_left 1 m)
  obtain ⟨Λx, hΛx⟩ := sa9_exists_lam (propagatorW Cf r t) (fun _ : Fin 1 => j) x hadd hsmul hcd1
  obtain ⟨Λy, hΛy⟩ := sa9_exists_lam (propagatorW Cf r t) (fun _ : Fin 1 => j) y hadd hsmul hcd1
  have hbd : ∀ g : mhn_Hc d, |(Λx - Λy) g| ≤ ((d : ℝ) * d * |K| * ‖x - y‖) * ‖mhn_rep ((q : ℕ) : ℝ) g‖ := by
    intro g
    have hφ := mhn_isSobolevTest_phi ((q : ℕ) : ℝ) g
    have hc2 : ContDiff ℝ 2 (propagatorW Cf r t (mhn_phi g)) :=
      ((hadj r t hr.1 hr.2 htT _ hφ).2.1).of_le (by exact_mod_cast Nat.add_le_add_right hm 1)
    have hlipg := sa6_grad_lip hc2 (B := |K| * HRS.Whole.sobolevNorm ((q : ℕ) : ℝ) (mhn_phi g))
      (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) (fun i z =>
        ((hadj r t hr.1 hr.2 htT _ hφ).2.2.2 2 (Nat.add_le_add_right hm 1) i z).trans
          (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _))) x y
    rw [LinearMap.sub_apply, hΛx, hΛy, mhn_norm_rep, ← rpk_gradient_partial, ← rpk_gradient_partial]
    have h1 : |gradient (propagatorW Cf r t (mhn_phi g)) x j - gradient (propagatorW Cf r t (mhn_phi g)) y j| ≤
        ‖gradient (propagatorW Cf r t (mhn_phi g)) x - gradient (propagatorW Cf r t (mhn_phi g)) y‖ := by
      have := PiLp.norm_apply_le (gradient (propagatorW Cf r t (mhn_phi g)) x -
        gradient (propagatorW Cf r t (mhn_phi g)) y) j
      simpa [Real.norm_eq_abs] using this
    refine h1.trans (hlipg.trans (le_of_eq ?_))
    ring
  have hb := fun n => mri_bessel ((q : ℕ) : ℝ) h hP (Λx - Λy) _ hbd n
  have hD : ∀ n, ∑ l ∈ Finset.range n, (sa9_Gr Cf t j (mhn_phi (h l)) (r, x) -
      sa9_Gr Cf t j (mhn_phi (h l)) (r, y)) ^ 2 ≤ ((d : ℝ) * d * |K| * ‖x - y‖) ^ 2 := by
    intro n
    refine le_of_eq_of_le (Finset.sum_congr rfl fun l _ => ?_) (hb n)
    rw [LinearMap.sub_apply, hΛx, hΛy, sa9_Gr_eq hr, sa9_Gr_eq hr]
  exact sa9_tail_cmp _ _ Lc hD

end Cmp

end HRS.MS.MainRdPath
