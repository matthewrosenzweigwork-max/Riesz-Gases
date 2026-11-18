import HRS.MS.SA16PForce4
import HRS.MS.CzHlsAux2
import HRS.MS.SA16JetSchwartz
import HRS.Whole.Dynamics

/-!
# SA16P P4, part 5: the force `∇g * ρ` (cancellation convention) is `C^k` with uniform bounds

* `sa16p_regular_bounds`: `IsRegularDensityW r Λ ρ` gives `‖D^j ρ y‖ ≤ A (1+|y|)^{-(d+3)}`, `j ≤ r`.
* `sa16p_conv_eq_phi`: `convGradConvW G ρ x = ∑_j Φ_{G_j} ρ x • e_j`.
* `sa16p_force_contDiff`: for `ρ ∈ C^{k+1}` with weighted bounds, `x ↦ convGradConvW (∇g) ρ x` is `C^k` and
  `‖D^j (∇g*ρ)‖ ≤ d C₀ A` for `j ≤ k`.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

universe u

namespace HRS.Whole.AppendixA.Phase2SA16P
open HRS HRS.Whole HRS.Whole.AppendixA

section Force
variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma sa16p_jbracket_ge (y : 𝔼) : (1 + ‖y‖) / Real.sqrt 2 ≤ jbracket y := by
  unfold jbracket
  rw [div_le_iff₀ (by positivity), ← Real.sqrt_mul (by positivity)]
  apply Real.le_sqrt_of_sq_le
  nlinarith [sq_nonneg (1 - ‖y‖), norm_nonneg y]

lemma sa16p_regular_bounds {r : ℕ} {Λ : ℝ} {ρ : 𝔼 → ℝ} (hreg : IsRegularDensityW r Λ ρ) :
    ∀ j ≤ r, ∀ y : 𝔼, ‖iteratedFDeriv ℝ j ρ y‖ ≤
      ((d : ℝ) ^ j * max Λ 0 * 2 ^ (((d : ℝ) + 3) / 2)) * sa16p_w d y := by
  intro j hj y
  have hsup := hreg.2.2
  have hb : ∀ i : Fin j → Fin d, |partialDeriv i ρ y| ≤ max Λ 0 * jbracket y ^ (-((d : ℝ) + 3)) := by
    intro i
    have h1 : ENNReal.ofReal (jbracket y ^ ((d : ℝ) + 3) * |partialDeriv i ρ y|) ≤ ENNReal.ofReal Λ := by
      refine le_trans ?_ ((le_add_self).trans hsup)
      unfold weightedSupE derivSupE
      exact le_iSup_of_le (⟨j, by omega⟩ : Fin (r + 1)) (le_iSup_of_le i (le_iSup_of_le y le_rfl))
    have h2 : jbracket y ^ ((d : ℝ) + 3) * |partialDeriv i ρ y| ≤ max Λ 0 := by
      rcases (ENNReal.ofReal_le_ofReal_iff' ).1 h1 with h | h
      · exact h.trans (le_max_left _ _)
      · exact h.trans (le_max_right _ _)
    have hjb : 0 < jbracket y := Real.sqrt_pos.2 (by positivity)
    rw [Real.rpow_neg hjb.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hjb _)]
    linarith
  have hjj : jbracket y ^ (-((d : ℝ) + 3)) ≤ 2 ^ (((d : ℝ) + 3) / 2) * sa16p_w d y := by
    unfold sa16p_w
    have h2 : (0 : ℝ) < (1 + ‖y‖) / Real.sqrt 2 := by positivity
    have h3 : jbracket y ^ (-((d : ℝ) + 3)) ≤ ((1 + ‖y‖) / Real.sqrt 2) ^ (-((d : ℝ) + 3)) :=
      Real.rpow_le_rpow_of_nonpos h2 (sa16p_jbracket_ge y) (by
        have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        linarith)
    have hr : (0 : ℝ) ≤ (d : ℝ) + 3 := by positivity
    have hjb : 0 < jbracket y := Real.sqrt_pos.2 (by positivity)
    have hA : (1 + ‖y‖) ^ ((d : ℝ) + 3) ≤ 2 ^ (((d : ℝ) + 3) / 2) * jbracket y ^ ((d : ℝ) + 3) := by
      have h4 : 1 + ‖y‖ ≤ Real.sqrt 2 * jbracket y := by
        have := sa16p_jbracket_ge y
        rwa [div_le_iff₀ (by positivity), mul_comm] at this
      calc (1 + ‖y‖) ^ ((d : ℝ) + 3) ≤ (Real.sqrt 2 * jbracket y) ^ ((d : ℝ) + 3) :=
            Real.rpow_le_rpow (by positivity) h4 hr
        _ = 2 ^ (((d : ℝ) + 3) / 2) * jbracket y ^ ((d : ℝ) + 3) := by
            rw [Real.mul_rpow (Real.sqrt_nonneg 2) hjb.le,
              Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]
            congr 2; ring
    rw [Real.rpow_neg hjb.le]
    calc (jbracket y ^ ((d : ℝ) + 3))⁻¹ ≤ (((1 + ‖y‖) ^ ((d : ℝ) + 3)) / 2 ^ (((d : ℝ) + 3) / 2))⁻¹ :=
          inv_anti₀ (by positivity) (by rw [div_le_iff₀ (by positivity)]; linarith)
      _ = 2 ^ (((d : ℝ) + 3) / 2) * ((1 + ‖y‖) ^ ((d : ℝ) + 3))⁻¹ := by
          rw [inv_div, div_eq_mul_inv]
      _ = 2 ^ (((d : ℝ) + 3) / 2) * (1 + ‖y‖) ^ (-((d : ℝ) + 3)) := by
          rw [Real.rpow_neg (by positivity)]
  calc ‖iteratedFDeriv ℝ j ρ y‖ ≤ ∑ i : Fin j → Fin d, |partialDeriv i ρ y| :=
        Phase2SA16.sa16j_norm_iter_le ρ y j
    _ ≤ ∑ i : Fin j → Fin d, max Λ 0 * (2 ^ (((d : ℝ) + 3) / 2) * sa16p_w d y) :=
        Finset.sum_le_sum fun i _ => (hb i).trans (mul_le_mul_of_nonneg_left hjj (le_max_right _ _))
    _ = ((d : ℝ) ^ j * max Λ 0 * 2 ^ (((d : ℝ) + 3) / 2)) * sa16p_w d y := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun]
        simp only [Fintype.card_fin, nsmul_eq_mul, Nat.cast_pow]
        ring

lemma sa16p_conv_eq_phi (G : 𝔼 → 𝔼) (ρ : 𝔼 → ℝ) (x : 𝔼)
    (hint : ∀ j : Fin d, Integrable (sa16p_phiI (fun z => G z j) ρ x) volume) :
    convGradConvW G ρ x =
      ∑ j : Fin d, (sa16p_phiF (fun z => G z j) ρ x) • (EuclideanSpace.single j (1 : ℝ) : 𝔼) := by
  unfold convGradConvW
  have h1 : ∫ y, (if ‖x - y‖ ≤ 1 / 4 then (ρ y - ρ x) • G (x - y) else ρ y • G (x - y)) =
      ∫ z, (if ‖z‖ ≤ 1 / 4 then (ρ (x - z) - ρ x) • G z else ρ (x - z) • G z) := by
    rw [← integral_sub_left_eq_self (fun y => if ‖x - y‖ ≤ 1 / 4 then (ρ y - ρ x) • G (x - y)
      else ρ y • G (x - y)) volume x]
    congr 1; funext z; simp only [sub_sub_cancel]
  rw [h1]
  have h2 : ∀ z, (if ‖z‖ ≤ 1 / 4 then (ρ (x - z) - ρ x) • G z else ρ (x - z) • G z) =
      ∑ j : Fin d, (sa16p_phiI (fun z => G z j) ρ x z) • (EuclideanSpace.single j (1 : ℝ) : 𝔼) := by
    intro z
    have hG : G z = ∑ j : Fin d, (G z j) • (EuclideanSpace.single j (1 : ℝ) : 𝔼) := by
      ext i; simp [Finset.sum_apply, Pi.single_apply]
    by_cases hn : ‖z‖ ≤ 1 / 4
    · simp only [if_pos hn, sa16p_phiI]
      conv_lhs => rw [hG]
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [smul_smul, smul_eq_mul, mul_comm]
    · simp only [if_neg hn, sa16p_phiI, sub_zero]
      conv_lhs => rw [hG]
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [smul_smul, smul_eq_mul, mul_comm]
  simp_rw [h2]
  rw [integral_finset_sum _ (fun j _ => (hint j).smul_const _)]
  exact Finset.sum_congr rfl fun j _ => integral_smul_const _ _

set_option synthInstance.maxHeartbeats 400000 in
theorem sa16p_force_contDiff (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (k : ℕ) {ρ : 𝔼 → ℝ}
    {A : ℝ} (hρ : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) ρ)
    (hb : ∀ j ≤ k + 1, ∀ y, ‖iteratedFDeriv ℝ j ρ y‖ ≤ A * sa16p_w d y) :
    ContDiff ℝ (k : WithTop ℕ∞) (convGradConvW (rieszKernelGrad d s) ρ) ∧
      ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j (convGradConvW (rieszKernelGrad d s) ρ) x‖ ≤
        d * (sa16p_C0 d (HRS.CZ.Hls.hlsg_c s) s * A) := by
  set Kf : Fin d → 𝔼 → ℝ := fun j z => rieszKernelGrad d s z j with hKf
  have hKe : ∀ j z, Kf j z = fderiv ℝ (rieszKernel d s) z (EuclideanSpace.single j 1) := fun j z => by
    simp only [hKf, rieszKernelGrad]; exact q09_gradient_apply _ _ _
  have hKm : ∀ j, Measurable (Kf j) := fun j => by
    have : Kf j = fun z => fderiv ℝ (rieszKernel d s) z (EuclideanSpace.single j 1) := funext (hKe j)
    rw [this]; exact measurable_fderiv_apply_const ℝ (rieszKernel d s) _
  have hKb : ∀ j, ∀ z, z ≠ 0 → |Kf j z| ≤ HRS.CZ.Hls.hlsg_c s * ‖z‖ ^ (-s - 1) := fun j z hz => by
    rw [hKe]; exact HRS.CZ.Hls.force_kernel_bound_coord hs0 hz j
  have hc : 0 ≤ HRS.CZ.Hls.hlsg_c s := HRS.CZ.Hls.hlsg_c_nonneg hs0
  have hρ1' : ContDiff ℝ 1 ρ := hρ.of_le (by
    have : (1 : WithTop ℕ∞) ≤ ((k + 1 : ℕ) : WithTop ℕ∞) := by exact_mod_cast (by omega : 1 ≤ k + 1)
    exact this)
  have hρd : Differentiable ℝ ρ := hρ1'.differentiable (by norm_num)
  have hρw : ∀ y, ‖ρ y‖ ≤ A * sa16p_w d y := fun y => by simpa using hb 0 (by omega) y
  have hA : 0 ≤ A := by
    have := (norm_nonneg (ρ 0)).trans (hρw 0)
    have hw := sa16p_w_pos (d := d) 0
    nlinarith
  have hρ1 : ∀ y, ‖fderiv ℝ ρ y‖ ≤ A := fun y => by
    rw [sa16p_norm_fderiv_eq]
    exact (hb 1 (by omega) y).trans (mul_le_of_le_one_right hA (sa16p_w_le_one y))
  have hphi := fun j => sa16p_phi_contDiff hd (hKm j) hc hs0 hsd (hKb j) k ρ A hρ hb
  have hfun : convGradConvW (rieszKernelGrad d s) ρ = fun x => ∑ j : Fin d,
      (sa16p_phiF (Kf j) ρ x) • (EuclideanSpace.single j (1 : ℝ) : 𝔼) := funext fun x =>
    sa16p_conv_eq_phi _ ρ x (fun j => (sa16p_phi_bound hd (hKm j) hc hs0 hsd (hKb j) hρd hρw hρ1 x).1)
  rw [hfun]
  refine ⟨ContDiff.sum fun j _ => ((hphi j).1).smul contDiff_const, fun i hi x => ?_⟩
  have hcd : ∀ j ∈ (Finset.univ : Finset (Fin d)), ContDiffAt ℝ (i : WithTop ℕ∞)
      (fun x => (sa16p_phiF (Kf j) ρ x) • (EuclideanSpace.single j (1 : ℝ) : 𝔼)) x := fun j _ =>
    (((hphi j).1).smul contDiff_const).contDiffAt.of_le (by exact_mod_cast hi)
  rw [iteratedFDeriv_fun_sum_apply hcd]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j : Fin d, ‖iteratedFDeriv ℝ i (fun x => (sa16p_phiF (Kf j) ρ x) •
          (EuclideanSpace.single j (1 : ℝ) : 𝔼)) x‖ ≤ ∑ j : Fin d, sa16p_C0 d (HRS.CZ.Hls.hlsg_c s) s * A := by
        refine Finset.sum_le_sum fun j _ => ?_
        let L : ℝ →L[ℝ] 𝔼 := ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
          (EuclideanSpace.single j (1 : ℝ) : 𝔼)
        have hL : ‖L‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun a => by
          simp [L, norm_smul])
        have hLf : (fun x => (sa16p_phiF (Kf j) ρ x) • (EuclideanSpace.single j (1 : ℝ) : 𝔼)) =
            L ∘ (sa16p_phiF (Kf j) ρ) := by
          funext y; simp [L]
        rw [hLf]
        have h1 := L.norm_iteratedFDeriv_comp_left (f := sa16p_phiF (Kf j) ρ) (x := x)
          (((hphi j).1).contDiffAt) (by exact_mod_cast hi)
        refine h1.trans ?_
        calc ‖L‖ * ‖iteratedFDeriv ℝ i (sa16p_phiF (Kf j) ρ) x‖ ≤ 1 * (sa16p_C0 d (HRS.CZ.Hls.hlsg_c s) s * A) :=
              mul_le_mul hL ((hphi j).2 i hi x) (norm_nonneg _) zero_le_one
          _ = _ := one_mul _
    _ = d * (sa16p_C0 d (HRS.CZ.Hls.hlsg_c s) s * A) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

end Force

end HRS.Whole.AppendixA.Phase2SA16P
