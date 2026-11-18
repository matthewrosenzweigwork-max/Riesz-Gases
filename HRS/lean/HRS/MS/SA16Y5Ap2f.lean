import HRS.MS.SA16Y5Sf1
import HRS.MS.SA16Y5Ap2

/-!
# S.A.16 (SA16Y5) Ap2f: the interpolated fractional-order operator and its heat-composed bound (B9)

`sa16y5f_Gop` (the operator of a density, by choice), `sa16y5f_NInt` (hat interpolation, level `m`), `sa16y5_Qh_lin`, `sa16y5_Qh_all`:
`‖Qh a N‖ ≤ C a^{-γ}` on all of `(0, A0]` from the bound on `(0,1]` and `‖N‖ ≤ Cg`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Ap2f
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)] {s : ℝ}

open Classical in
def sa16y5f_Gop (d m : ℕ) (p : ℝ) [Fact (2 ≤ p)] (s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (μ : Euc d → ℝ) :
    WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p :=
  if h : ∃ T, SA16FOp d m p s M μ T then Classical.choose h else 0

lemma sa16y5f_Gop_eq {m : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} {μ : Euc d → ℝ}
    {T : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p} (hT : SA16FOp d m p s M μ T) :
    sa16y5f_Gop d m p s M μ = T := by
  have h : ∃ T, SA16FOp d m p s M μ T := ⟨T, hT⟩
  unfold sa16y5f_Gop
  rw [dif_pos h]
  have h1 := Classical.choose_spec h
  refine ContinuousLinearMap.ext fun x => ?_
  refine (sa16r_Jcc_dense d (m + 1 + 1) p).induction_on x
    (isClosed_eq (Classical.choose h).continuous T.continuous) (fun φ => ?_)
  exact sa16r_wrep_inj d m p _ _ (by filter_upwards [h1 φ, hT φ] with z e1 e2; rw [e1, e2])

/-- interpolated nonlocal operator at level `m` -/
def sa16y5f_NInt (d m N : ℕ) (p : ℝ) [Fact (2 ≤ p)] (s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (t : ℝ)
    (μ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (σ : ℝ) : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p :=
  ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ • sa16y5f_Gop d m p s M (sa16q_mol N (μ (t - (i : ℝ) * t / N)))

lemma sa16y5_Qh_lin {m : ℕ} (a : ℝ) {ι : Type*} (S : Finset ι) (w : ι → ℝ)
    (N : ι → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p) :
    sa16y5_Qh d m p a (∑ i ∈ S, w i • N i) = ∑ i ∈ S, w i • sa16y5_Qh d m p a (N i) := by
  refine ContinuousLinearMap.ext fun x => ?_
  simp only [sa16y5_Qh, ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, map_sum, map_smul]

lemma sa16y5_Qh_big {m : ℕ} {a : ℝ} (ha : 1 ≤ a) (N : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p) :
    ‖sa16y5_Qh d m p a N‖ ≤ (sa16r_cG d (1 / 2)) ^ 2 * ‖N‖ := by
  have ha0 : 0 < a / 2 := by linarith
  have hc : sa16r_cG d (a / 2) ≤ sa16r_cG d (1 / 2) := by
    unfold sa16r_cG
    have : (a / 2) ^ (-(1 / 2 : ℝ)) ≤ (1 / 2) ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) (by linarith) (by norm_num)
    have h2 : 0 ≤ (d : ℝ) * (4 / 3 : ℝ) ^ ((d : ℝ) / 2) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right this h2]
  have h1 := sa16r_Gam_norm (d := d) (p := p) ha0 m
  have h2 := sa16r_Gam_norm (d := d) (p := p) ha0 (m + 1)
  have hcn := sa16r_cG_nonneg d ha0
  unfold sa16y5_Qh
  calc _ ≤ ‖sa16r_Gam d (m + 1) p (a / 2)‖ * ‖(sa16r_Gam d m p (a / 2)).comp N‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖sa16r_Gam d (m + 1) p (a / 2)‖ * (‖sa16r_Gam d m p (a / 2)‖ * ‖N‖) := by
        gcongr; exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ sa16r_cG d (1 / 2) * (sa16r_cG d (1 / 2) * ‖N‖) := by
        have hcG0 : 0 ≤ sa16r_cG d (1 / 2) := sa16r_cG_nonneg d (by norm_num)
        exact mul_le_mul (h2.trans hc) (mul_le_mul_of_nonneg_right (h1.trans hc)
          (ContinuousLinearMap.opNorm_nonneg _)) (mul_nonneg (ContinuousLinearMap.opNorm_nonneg _)
          (ContinuousLinearMap.opNorm_nonneg _)) hcG0
    _ = _ := by ring

lemma sa16y5_Qh_all {m : ℕ} {γ C Cg A0 : ℝ} (hγ : 0 ≤ γ) (hA0 : 1 ≤ A0) (hC : 0 ≤ C) (hCg : 0 ≤ Cg)
    (N : WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p) (hN : ‖N‖ ≤ Cg)
    (hsmall : ∀ a : ℝ, 0 < a → a ≤ 1 → ‖sa16y5_Qh d m p a N‖ ≤ C * a ^ (-γ)) :
    ∀ a : ℝ, 0 < a → a ≤ A0 →
      ‖sa16y5_Qh d m p a N‖ ≤ max C ((sa16r_cG d (1 / 2)) ^ 2 * Cg * A0 ^ γ) * a ^ (-γ) := by
  intro a ha haA
  have hap : 0 ≤ a ^ (-γ) := Real.rpow_nonneg ha.le _
  by_cases h1 : a ≤ 1
  · exact (hsmall a ha h1).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hap)
  · push_neg at h1
    have hb := sa16y5_Qh_big (p := p) h1.le N
    have hcG : 0 ≤ sa16r_cG d (1 / 2) := sa16r_cG_nonneg d (by norm_num)
    have e : (1 : ℝ) ≤ a ^ γ * a ^ (-γ) := by
      rw [← Real.rpow_add ha]; simp
    have hag : a ^ γ ≤ A0 ^ γ := Real.rpow_le_rpow ha.le haA hγ
    calc ‖sa16y5_Qh d m p a N‖ ≤ (sa16r_cG d (1 / 2)) ^ 2 * ‖N‖ := hb
      _ ≤ (sa16r_cG d (1 / 2)) ^ 2 * Cg := mul_le_mul_of_nonneg_left hN (by positivity)
      _ = (sa16r_cG d (1 / 2)) ^ 2 * Cg * 1 := by ring
      _ ≤ (sa16r_cG d (1 / 2)) ^ 2 * Cg * (a ^ γ * a ^ (-γ)) :=
          mul_le_mul_of_nonneg_left e (by positivity)
      _ ≤ (sa16r_cG d (1 / 2)) ^ 2 * Cg * (A0 ^ γ * a ^ (-γ)) := by gcongr
      _ ≤ _ := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) hap

end Ap2f

end HRS.Whole.AppendixA.Phase2SA16R
