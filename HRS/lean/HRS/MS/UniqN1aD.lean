import HRS.MS.UniqN1aC
import HRS.MS.UniqN2bA

/-!
# N1a of `UniqPlan.md`, part (d): `g * ∂_j∂_iψ = (∂_j∂_i g) * ψ` pointwise (`0 ≤ s < d - 2`)

With `H_j := q09_H s j = ∂_j g` and `G_{ji} := q09_DH s j · e_i = ∂_i∂_j g` (both `C^∞` off `0`),
`|H_j(z)| ≤ m ‖z‖^{-s-1}`, `|G_{ji}(z)| ≤ m (s+3) ‖z‖^{-s-2}`; two applications of `n1a_weak_deriv`
(with `k = g`, `a = s` resp. `1/2` for `s = 0`; and `k = H_j`, `a = s+1`) give, for `ψ ∈ C²_c`,
`(g * ∂_j∂_iψ)(y) = ∫ G_{ji}(y - x) ψ(x) dx` for every `y` (`n1a_hess_repr`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqN1a

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqT3 HRS.MS.UniqN0
  HRS.MH.Screened

variable {d : ℕ}

/-- Local integrability from a power bound off the origin. -/
theorem n1a_locInt_of_bound (hd : 1 ≤ d) {f : Euc d → ℝ} (hf : AEStronglyMeasurable f volume)
    {t A : ℝ} (ht : t < d) (hb : ∀ z : Euc d, z ≠ 0 → |f z| ≤ A * ‖z‖ ^ (-t)) :
    LocallyIntegrable f volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Euc d)
  obtain ⟨CK, hCK0, hCK⟩ := lintegral_ball_rpow_le_proof (d := d) hd ht
  have hR' : closedBall (0 : Euc d) R ⊆ closedBall (0 : Euc d) (max R 1) :=
    closedBall_subset_closedBall (le_max_left _ _)
  refine IntegrableOn.mono_set ?_ (hR.trans hR')
  refine ⟨hf.restrict, ?_⟩
  unfold HasFiniteIntegral
  have hae : ∀ᵐ z ∂(volume : Measure (Euc d)), z ≠ 0 := k3_ae_ne hd 0
  calc ∫⁻ z in closedBall (0 : Euc d) (max R 1), ‖f z‖ₑ
      ≤ ∫⁻ z in closedBall (0 : Euc d) (max R 1),
          ENNReal.ofReal (max A 0) * ENNReal.ofReal (‖z‖ ^ (-t)) := by
        refine lintegral_mono_ae ((ae_restrict_of_ae hae).mono fun z hz => ?_)
        rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (le_max_right _ _)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [Real.norm_eq_abs]
        exact (hb z hz).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    _ = ENNReal.ofReal (max A 0) * ∫⁻ z in closedBall (0 : Euc d) (max R 1),
          ENNReal.ofReal (‖z‖ ^ (-t)) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (max A 0) * ENNReal.ofReal (CK * (max R 1) ^ ((d : ℝ) - t)) :=
        mul_le_mul_of_nonneg_left (hCK _ (lt_of_lt_of_le one_pos (le_max_right _ _))) (by positivity)
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top

/-- Power bound for `g` near `0`. -/
theorem n1a_g_bound {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ a A : ℝ, 0 ≤ a ∧ a + 1 < d ∧
      ∀ z : Euc d, z ≠ 0 → ‖z‖ ≤ 1 → |rieszKernel d s z| ≤ A * ‖z‖ ^ (-a) := by
  by_cases h0 : s = 0
  · refine ⟨1 / 2, 2, by norm_num, by linarith, fun z hz hz1 => ?_⟩
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
  · refine ⟨s, 1, hs0, by linarith, fun z hz hz1 => ?_⟩
    have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
    unfold rieszKernel
    rw [if_neg h0, abs_of_nonneg (Real.rpow_nonneg hn.le _), one_mul]

theorem n1a_H_meas (s : ℝ) (j : Fin d) : Measurable (q09_H s j) := by
  unfold q09_H
  have : Measurable (fun z : Euc d => z j) := (EuclideanSpace.proj j : Euc d →L[ℝ] ℝ).measurable
  fun_prop

/-- The hypotheses of `n1a_weak_deriv` for `k = g`. -/
theorem n1a_weak_g (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (j : Fin d)
    {F : Euc d → ℝ} (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) (y : Euc d) :
    ∫ x, rieszKernel d s (y - x) * fderiv ℝ F x (EuclideanSpace.single j 1) =
      ∫ x, q09_H s j (y - x) * F x := by
  obtain ⟨a, A, ha0, had, hb⟩ := n1a_g_bound (d := d) hs0 hsd
  have hs1 : s < (d : ℝ) := by linarith
  have hk := rieszKernel_locallyIntegrable (d := d) hs0 hs1
  have hk' : LocallyIntegrable (fun z => fderiv ℝ (rieszKernel d s) z (EuclideanSpace.single j 1))
      volume := by
    refine n1a_locInt_of_bound hd (t := s + 1) (A := max 1 s)
      (measurable_fderiv_apply_const ℝ (rieszKernel d s) _).aestronglyMeasurable (by linarith)
      (fun z hz => ?_)
    have := n0_qH_bound hs0 j hz
    rw [q09_H_eq_fderiv s j hz, show -(s + 1) = -s - 1 by ring]
    exact this
  have := n1a_weak_deriv hd j (fun z hz => n0_g_contDiffAt s hz) hk hk' ha0 had hb hF hFc y
  rw [this]
  refine integral_congr_ae ((k3_ae_ne hd y).mono fun x hx => ?_)
  beta_reduce
  rw [q09_H_eq_fderiv s j (sub_ne_zero.2 hx.symm)]

/-- Second step: `k = ∂_j g`. -/
theorem n1a_weak_H (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (i j : Fin d)
    {F : Euc d → ℝ} (hF : ContDiff ℝ 1 F) (hFc : HasCompactSupport F) (y : Euc d) :
    ∫ x, q09_H s j (y - x) * fderiv ℝ F x (EuclideanSpace.single i 1) =
      ∫ x, q09_DH s j (y - x) (EuclideanSpace.single i 1) * F x := by
  have hqb : ∀ z : Euc d, z ≠ 0 → |q09_H s j z| ≤ max 1 s * ‖z‖ ^ (-(s + 1)) := by
    intro z hz
    have := n0_qH_bound hs0 j hz
    rwa [show -(s + 1) = -s - 1 by ring]
  have hk : LocallyIntegrable (q09_H s j) volume :=
    n1a_locInt_of_bound hd (n1a_H_meas s j).aestronglyMeasurable (t := s + 1) (A := max 1 s)
      (by linarith) hqb
  have hfd : ∀ z : Euc d, z ≠ 0 → fderiv ℝ (q09_H s j) z = q09_DH s j z :=
    fun z hz => (q09_H_hasFDerivAt s j hz).fderiv
  have hk' : LocallyIntegrable (fun z => fderiv ℝ (q09_H s j) z (EuclideanSpace.single i 1))
      volume := by
    refine n1a_locInt_of_bound hd (t := s + 2) (A := max 1 s * (s + 3))
      (measurable_fderiv_apply_const ℝ (q09_H s j) _).aestronglyMeasurable (by linarith)
      (fun z hz => ?_)
    rw [hfd z hz, show -(s + 2) = -s - 2 by ring]
    have := n0_qDH_bound hs0 j i hz
    exact this
  have := n1a_weak_deriv hd i (fun z hz => (n0_qH_contDiffAt s j hz).of_le (by exact_mod_cast le_top))
    hk hk' (a := s + 1) (A := max 1 s) (by linarith) (by linarith) (fun z hz _ => hqb z hz) hF hFc y
  rw [this]
  refine integral_congr_ae ((k3_ae_ne hd y).mono fun x hx => ?_)
  beta_reduce
  rw [hfd _ (sub_ne_zero.2 hx.symm)]

/-- **Hessian representation.** For `ψ ∈ C²_c`, `0 ≤ s < d - 2`, every `y`:
`(g * ∂_j∂_iψ)(y) = ∫ (∂_i∂_j g)(y - x) ψ(x) dx`. -/
theorem n1a_hess_repr (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2)
    {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) (i j : Fin d) (y : Euc d) :
    HRS.Whole.convFun (rieszKernel d s) (D1 j (D1 i ψ)) y =
      ∫ x, q09_DH s j (y - x) (EuclideanSpace.single i 1) * ψ x := by
  have h1 := n1a_weak_g hd hs0 hsd j (D1_contDiff hψ i) (D1_supp hψc i) y
  have h2 := n1a_weak_H hd hs0 hsd i j (hψ.of_le (by norm_num)) hψc y
  rw [← h2]
  exact h1

end HRS.MS.UniqN1a
