import HRS.MS.SA16QFin1

/-!
# S.A.16 (SA16Q), E6 part 16: bookkeeping for the limit argument

Sums of binomial coefficients, `N_P`/`N_Q` from termwise bounds, the weighted operator-norm bound from coordinate
weights, smoothness of `eucNonlocal` for `a ∈ SB`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16

section Fin2
variable {d : ℕ}

lemma sa16q_choose_sum (l : ℕ) :
    ∑ k ∈ Finset.range (l + 1), ENNReal.ofReal (l.choose k : ℝ) = ENNReal.ofReal (2 ^ l) := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => Nat.cast_nonneg _)]
  congr 1
  exact_mod_cast Nat.sum_range_choose l

lemma sa16q_NP_le {a u : Euc d → ℝ} {l : ℕ} {r : ℝ} (K : ℝ≥0∞)
    (h : ∀ k ≤ l, eLpNorm (fun x => ‖iteratedFDeriv ℝ k a x‖ * ‖iteratedFDeriv ℝ (l - k) u x‖)
      (ENNReal.ofReal r) volume ≤ K) : sa16q_NP a u l r ≤ ENNReal.ofReal (2 ^ l) * K := by
  unfold sa16q_NP
  calc ∑ k ∈ Finset.range (l + 1), ENNReal.ofReal (l.choose k : ℝ) *
        eLpNorm (fun x => ‖iteratedFDeriv ℝ k a x‖ * ‖iteratedFDeriv ℝ (l - k) u x‖)
          (ENNReal.ofReal r) volume
      ≤ ∑ k ∈ Finset.range (l + 1), ENNReal.ofReal (l.choose k : ℝ) * K :=
        Finset.sum_le_sum fun k hk => sa16q_mul_le6 (h k (by have := Finset.mem_range.1 hk; omega))
    _ = ENNReal.ofReal (2 ^ l) * K := by rw [← Finset.sum_mul, sa16q_choose_sum]

lemma sa16q_NQ_le {a u : Euc d → ℝ} {l : ℕ} {r : ℝ} (K : ℝ≥0∞)
    (h : ∀ k ≤ l, eLpNorm (fun x => ‖iteratedFDeriv ℝ (k + 1) a x‖ * ‖iteratedFDeriv ℝ (l - k) u x‖)
      (ENNReal.ofReal r) volume ≤ K) : sa16q_NQ a u l r ≤ ENNReal.ofReal (2 ^ l) * K := by
  unfold sa16q_NQ
  calc ∑ k ∈ Finset.range (l + 1), ENNReal.ofReal (l.choose k : ℝ) *
        eLpNorm (fun x => ‖iteratedFDeriv ℝ (k + 1) a x‖ * ‖iteratedFDeriv ℝ (l - k) u x‖)
          (ENNReal.ofReal r) volume
      ≤ ∑ k ∈ Finset.range (l + 1), ENNReal.ofReal (l.choose k : ℝ) * K :=
        Finset.sum_le_sum fun k hk => sa16q_mul_le6 (h k (by have := Finset.mem_range.1 hk; omega))
    _ = ENNReal.ofReal (2 ^ l) * K := by rw [← Finset.sum_mul, sa16q_choose_sum]

/-- the weight in terms of coordinate derivatives -/
lemma sa16q_weight_conv {a : Euc d → ℝ} {κ : ℕ} {Λ2 : ℝ}
    (hw : ∀ r : Fin κ → Fin d, ∀ x, |partialDeriv r a x| * (1 + ‖x‖) ^ (d + 3) ≤ Λ2) (x : Euc d) :
    ‖iteratedFDeriv ℝ κ a x‖ ≤ (d : ℝ) ^ κ * Λ2 * (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ)) := by
  have hpos : 0 < (1 + ‖x‖) ^ (d + 3) := by positivity
  have hω : (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ)) = ((1 + ‖x‖) ^ (d + 3))⁻¹ := by
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
  have hω0 : 0 ≤ (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ)) := Real.rpow_nonneg (by positivity) _
  have h1 : ∀ r : Fin κ → Fin d, |partialDeriv r a x| ≤ Λ2 * (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ)) := by
    intro r
    rw [hω, ← div_eq_mul_inv, le_div_iff₀ hpos]
    exact hw r x
  refine (sa16j_norm_iter_le a x κ).trans ?_
  calc ∑ r : Fin κ → Fin d, |partialDeriv r a x|
      ≤ ∑ r : Fin κ → Fin d, Λ2 * (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ)) := Finset.sum_le_sum fun r _ => h1 r
    _ = (d : ℝ) ^ κ * Λ2 * (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ)) := by
        simp [Finset.sum_const, Fintype.card_fun]; ring

variable (hd : 2 ≤ d) {s : ℝ} (hs : 0 ≤ s) (hs2 : s ≤ (d : ℝ) - 2)
include hd hs hs2

lemma sa16q_F_smooth (M : Matrix (Fin d) (Fin d) ℝ) {a : Euc d → ℝ} (ha : sa16q_SB a) (u : 𝓢(Euc d, ℝ)) :
    ContDiff ℝ ∞ (HRS.MH.AdjointRd.eucNonlocal s M a ⇑u) := by
  have hGs : ∀ ψ : 𝓢(Euc d, ℝ), ContDiff ℝ ∞ (HRS.Whole.convFun (rieszKernel d s) ψ) :=
    fun ψ => sa16q_conv_contDiff_top hd hs hs2 ψ
  have hVs : ∀ (ψ : 𝓢(Euc d, ℝ)) (j : Fin d), ContDiff ℝ ∞
      (fun z => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) ψ) z (EuclideanSpace.single j (1 : ℝ))) :=
    fun ψ j => ((hGs ψ).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hAs : ∀ (ψ : 𝓢(Euc d, ℝ)) (i j : Fin d), ContDiff ℝ ∞
      (fun y => fderiv ℝ (fun z => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) ψ) z
        (EuclideanSpace.single j (1 : ℝ))) y (EuclideanSpace.single i (1 : ℝ))) := fun ψ i j =>
    (((hVs ψ j).fderiv_right (m := ∞) (by simp))).clm_apply contDiff_const
  have hBs : ∀ (ψ : 𝓢(Euc d, ℝ)) (i : Fin d), ContDiff ℝ ∞
      (fun y => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) ψ) y (EuclideanSpace.single i (1 : ℝ))) :=
    fun ψ i => ((hGs ψ).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have hfun : HRS.MH.AdjointRd.eucNonlocal s M a ⇑u = fun y => ∑ i : Fin d, ∑ j : Fin d, M j i *
      (fderiv ℝ (fun z => fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) (sa16q_mulS ha u)) z
          (EuclideanSpace.single j (1 : ℝ))) y (EuclideanSpace.single i (1 : ℝ)) -
        fderiv ℝ (HRS.Whole.convFun (rieszKernel d s)
          (sa16q_mulS (sa16q_SB_pd ha (EuclideanSpace.single j (1 : ℝ))) u)) y
          (EuclideanSpace.single i (1 : ℝ))) :=
    funext fun y => sa16q_F_decomp hd hs hs2 M ha u y
  rw [hfun]
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
    contDiff_const.mul ((hAs _ i j).sub (hBs _ i))

end Fin2

end HRS.Whole.AppendixA.Phase2SA16Q
