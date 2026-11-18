import HRS.MS.SA12NN2A

/-!
# S.A.12 N2 (SA12N), part B: the pointwise Hessian formula for a test function vanishing at the point

For `w ∈ C²_c` with `|w(x)| ≤ M ‖y-x‖^p`, `|∂_i w(x)| ≤ M' ‖y-x‖^{p-1}` (`p ∈ {1,2}`) and `s + 2 < d + p`:
`g * ∂_j∂_i w (y) = ∫ (∂_i ∂_j g)(y-x) w(x) dx`, an absolutely convergent integral.  Two applications
of `sa12n_weak_deriv` (the first with `k = g`, the second with `k = ∂_j g`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqT3 HRS.MS.UniqN0
  HRS.MH.Screened HRS.MS.UniqN1a

variable {d : ℕ}

/-- Integrability of `f(y-·) F` from a power bound on `f` and the vanishing `|F(x)| ≤ M ‖y-x‖^q`. -/
theorem sa12n_integrable_of_pow (hd : 1 ≤ d) {f F : Euc d → ℝ} (y : Euc d)
    (hf : AEStronglyMeasurable f volume) (hFc : Continuous F) (hFcs : HasCompactSupport F)
    {t A M q : ℝ} (hq : t - q < d) (hfb : ∀ z : Euc d, z ≠ 0 → |f z| ≤ A * ‖z‖ ^ (-t))
    (hFb : ∀ x, |F x| ≤ M * ‖y - x‖ ^ q) :
    Integrable (fun x => f (y - x) * F x) volume := by
  have hG : AEStronglyMeasurable (fun z => f z * F (y - z)) volume :=
    hf.mul ((hFc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  have hloc : LocallyIntegrable (fun z => f z * F (y - z)) volume := by
    refine n1a_locInt_of_bound hd hG (t := t - q) (A := A * M) hq (fun z hz => ?_)
    have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
    have h1 := hfb z hz
    have h2 := hFb (y - z)
    rw [show y - (y - z) = z by abel] at h2
    rw [abs_mul]
    have h3 : A * ‖z‖ ^ (-t) * (M * ‖z‖ ^ q) = A * M * ‖z‖ ^ (-(t - q)) := by
      rw [show -(t - q) = -t + q by ring, Real.rpow_add hn]; ring
    rw [← h3]
    exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
  have hcs : HasCompactSupport (fun z => f z * F (y - z)) := by
    have : HasCompactSupport (fun z => F (y - z)) :=
      hFcs.comp_isClosedEmbedding (Homeomorph.subLeft y).isClosedEmbedding
    exact this.mul_left
  have hint : Integrable (fun z => f z * F (y - z)) volume :=
    (integrableOn_iff_integrable_of_support_subset (subset_tsupport _)).1
      (hloc.integrableOn_isCompact hcs)
  have := hint.comp_sub_left y
  refine this.congr (Eventually.of_forall fun x => ?_)
  simp [sub_sub_cancel]

/-- Power bound for `g` near `0`, with the exponent adapted to `s + 2 < d + p`. -/
theorem sa12n_g_bound {s : ℝ} (hs0 : 0 ≤ s) (p : ℕ) (hsp : s + 2 < d + p) :
    ∃ a A : ℝ, 0 ≤ a ∧ a + 2 < d + p ∧
      ∀ z : Euc d, z ≠ 0 → ‖z‖ ≤ 1 → |rieszKernel d s z| ≤ A * ‖z‖ ^ (-a) := by
  by_cases h0 : s = 0
  · have h3 : (3 : ℝ) ≤ d + p := by
      have h2 : (2 : ℕ) < d + p := by
        have : (2 : ℝ) < ((d + p : ℕ) : ℝ) := by push_cast; rw [h0] at hsp; linarith
        exact_mod_cast this
      have : (3 : ℕ) ≤ d + p := h2
      exact_mod_cast this
    refine ⟨1 / 2, 2, by norm_num, by linarith, fun z hz hz1 => ?_⟩
    have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hrk : rieszKernel d s z = Real.log (‖z‖⁻¹) := by
      unfold rieszKernel; rw [if_pos h0, Real.log_inv]
    rw [hrk]
    have h1 : 0 ≤ Real.log (‖z‖⁻¹) := Real.log_nonneg (one_le_inv_iff₀.2 ⟨hn, hz1⟩)
    rw [abs_of_nonneg h1]
    have := Real.log_le_rpow_div (x := ‖z‖⁻¹) (ε := 1 / 2) (inv_nonneg.2 hn.le) (by norm_num)
    refine this.trans (le_of_eq ?_)
    rw [Real.inv_rpow hn.le, ← Real.rpow_neg hn.le]
    ring
  · refine ⟨s, 1, hs0, hsp, fun z hz hz1 => ?_⟩
    have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
    unfold rieszKernel
    rw [if_neg h0, abs_of_nonneg (Real.rpow_nonneg hn.le _), one_mul]

/-- The Hessian kernel formula. -/
theorem sa12n_hess_repr (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (p : ℕ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (hsp : s + 2 < d + p) {w : Euc d → ℝ} (hw : ContDiff ℝ 2 w) (hwc : HasCompactSupport w)
    (i j : Fin d) (y : Euc d) {M M' : ℝ} (hM0 : 0 ≤ M) (hM'0 : 0 ≤ M')
    (hwb : ∀ x, |w x| ≤ M * ‖y - x‖ ^ (p : ℝ))
    (hw'b : ∀ x, |D1 i w x| ≤ M' * ‖y - x‖ ^ ((p : ℝ) - 1)) :
    HRS.Whole.convFun (rieszKernel d s) (D1 j (D1 i w)) y =
      ∫ x, q09_DH s j (y - x) (EuclideanSpace.single i 1) * w x := by
  have hp1' : (1 : ℝ) ≤ p := by exact_mod_cast hp1
  have hp2' : (p : ℝ) ≤ 2 := by exact_mod_cast hp2
  have hsd : s < d := by linarith
  have hpos : (0 : ℝ) ≤ (p : ℝ) := by linarith
  have hpos1 : (0 : ℝ) ≤ (p : ℝ) - 1 := by linarith
  have hqb : ∀ z : Euc d, z ≠ 0 → |q09_H s j z| ≤ max 1 s * ‖z‖ ^ (-(s + 1)) := by
    intro z hz
    have := n0_qH_bound hs0 j hz
    rwa [show -(s + 1) = -s - 1 by ring]
  have hkg := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  obtain ⟨a, A, ha0, had, hgb⟩ := sa12n_g_bound (d := d) hs0 p hsp
  -- step 1: k = g, F = ∂_i w
  have hF1 : ContDiff ℝ 1 (D1 i w) := D1_contDiff hw i
  have hI1 : Integrable (fun x => fderiv ℝ (rieszKernel d s) (y - x) (EuclideanSpace.single j 1) *
      D1 i w x) volume := by
    have h := sa12n_integrable_of_pow hd y (n1a_H_meas s j).aestronglyMeasurable
      hF1.continuous (D1_supp hwc i) (t := s + 1) (A := max 1 s) (M := M') (q := (p : ℝ) - 1)
      (by linarith) hqb hw'b
    refine h.congr ((k3_ae_ne hd y).mono fun x hx => ?_)
    simp only
    rw [q09_H_eq_fderiv s j (sub_ne_zero.2 hx.symm)]
  have hDc : Continuous (fun x => fderiv ℝ (D1 i w) x (EuclideanSpace.single j 1)) :=
    (hF1.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDcs : HasCompactSupport (fun x => fderiv ℝ (D1 i w) x (EuclideanSpace.single j 1)) :=
    ((D1_supp hwc i).fderiv (𝕜 := ℝ)).comp_left
      (g := fun L : Euc d →L[ℝ] ℝ => L (EuclideanSpace.single j 1)) (by simp)
  have hI1g : Integrable (fun x => rieszKernel d s (y - x) *
      fderiv ℝ (D1 i w) x (EuclideanSpace.single j 1)) volume :=
    n1a_conv_integrable hkg hDc hDcs y
  have h1 := sa12n_weak_deriv hd j (fun z hz => n0_g_contDiffAt s hz) (a := a) (A := A)
    (M := M') (p := (p : ℝ) - 1) ha0 hpos1 hM'0 (by linarith) hgb hF1 (D1_supp hwc i) y hw'b
    hI1g hI1
  -- step 2: k = H_j, F = w
  have hfd : ∀ z : Euc d, z ≠ 0 → fderiv ℝ (q09_H s j) z = q09_DH s j z :=
    fun z hz => (q09_H_hasFDerivAt s j hz).fderiv
  have hI2 : Integrable (fun x => fderiv ℝ (q09_H s j) (y - x) (EuclideanSpace.single i 1) *
      w x) volume := by
    have h := sa12n_integrable_of_pow hd y (n1a_DH_meas s i j).aestronglyMeasurable
      (hw.continuous) hwc (t := s + 2) (A := max 1 s * (s + 3)) (M := M) (q := (p : ℝ))
      (by linarith) (fun z hz => by
        have := n0_qDH_bound hs0 j i hz
        rwa [show -(s + 2) = -s - 2 by ring]) hwb
    refine h.congr ((k3_ae_ne hd y).mono fun x hx => ?_)
    simp only
    rw [hfd _ (sub_ne_zero.2 hx.symm)]
  have hI1H : Integrable (fun x => q09_H s j (y - x) *
      fderiv ℝ w x (EuclideanSpace.single i 1)) volume :=
    sa12n_integrable_of_pow hd y (n1a_H_meas s j).aestronglyMeasurable
      hF1.continuous (D1_supp hwc i) (t := s + 1) (A := max 1 s) (M := M') (q := (p : ℝ) - 1)
      (by linarith) hqb hw'b
  have h2 := sa12n_weak_deriv hd i (fun z hz => (n0_qH_contDiffAt s j hz).of_le
    (by exact_mod_cast le_top)) (a := s + 1) (A := max 1 s) (M := M) (p := (p : ℝ))
    (by linarith) hpos hM0 (by linarith) (fun z hz _ => hqb z hz) (hw.of_le (by norm_num)) hwc y hwb
    hI1H hI2
  have e1 : ∫ x, fderiv ℝ (rieszKernel d s) (y - x) (EuclideanSpace.single j 1) * D1 i w x =
      ∫ x, q09_H s j (y - x) * fderiv ℝ w x (EuclideanSpace.single i 1) := by
    refine integral_congr_ae ((k3_ae_ne hd y).mono fun x hx => ?_)
    simp only
    rw [q09_H_eq_fderiv s j (sub_ne_zero.2 hx.symm)]
    rfl
  have e2 : ∫ x, fderiv ℝ (q09_H s j) (y - x) (EuclideanSpace.single i 1) * w x =
      ∫ x, q09_DH s j (y - x) (EuclideanSpace.single i 1) * w x := by
    refine integral_congr_ae ((k3_ae_ne hd y).mono fun x hx => ?_)
    simp only
    rw [hfd _ (sub_ne_zero.2 hx.symm)]
  show ∫ x, rieszKernel d s (y - x) * fderiv ℝ (D1 i w) x (EuclideanSpace.single j 1) = _
  rw [h1, e1, h2, e2]

end HRS.MH.AdjointRd.Phase2SA12Near
