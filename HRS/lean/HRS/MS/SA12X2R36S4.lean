import HRS.MS.SA12X2R36S3
import HRS.MS.SA12Z3NearN7B

/-!
# S.A.12 R36 (SA12X3), part S4: expansion of the jet pairing

`jetPair m w F (eucNonlocal s M a F) = ∑_j C(m,j) ∑_idx ∑_i ∑_l M_{li} ∫ (w² ∂^idx F) · T_i(∂^idx(a ∂_lF))`
with `T_i = firstRiesz` (via `sa12z3_pd_eucNL`).
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12 HRS.MS.UniqT3

variable {d : ℕ}

/-- Smoothness of the Riesz convolution of a compactly supported `C^k` function. -/
theorem sa12x2_convFun_cd {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {k : ℕ} {Q : Euc d → ℝ}
    (hQ : ContDiff ℝ k Q) (hQc : HasCompactSupport Q) :
    ContDiff ℝ k (fun x => ∫ y, rieszKernel d s (x - y) * Q y) := by
  have hK : LocallyIntegrable (rieszKernel d s) (volume : Measure (Euc d)) :=
    rieszKernel_locallyIntegrable hs0 hsd
  have hfun : (fun x => ∫ y, rieszKernel d s (x - y) * Q y) =
      rieszKernel d s ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] Q := by
    funext x'
    have h := integral_sub_left_eq_self (μ := volume) (fun t => rieszKernel d s t * Q (x' - t)) x'
    simp only [sub_sub_cancel] at h
    simpa [convolution_def] using h
  rw [hfun]
  exact hQc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hK hQ

theorem sa12x2_jetPair_expand {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M : Matrix (Fin d) (Fin d) ℝ) {m : ℕ}
    {a F w : Euc d → ℝ} (ha : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) a) (hac : HasCompactSupport a)
    (hF : ContDiff ℝ ∞ F) (hw : Continuous w) (hwc : HasCompactSupport w) :
    jetPair m w F (eucNonlocal s M a F) =
      ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d, ∑ i : Fin d, ∑ l : Fin d,
        M l i * ∫ x, (w x ^ 2 * partialDeriv idx F x) *
          firstRiesz d s i (partialDeriv idx (fun y => a y * D1 l F y)) x := by
  have ha' : ContDiff ℝ (m + 1) a := by exact_mod_cast ha
  unfold jetPair
  refine Finset.sum_congr rfl fun j hj => ?_
  congr 1
  refine Finset.sum_congr rfl fun idx _ => ?_
  have hjm : j ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hpc : Continuous (partialDeriv idx F) := (sa12z3_pd_contDiff_inf hF idx).continuous
  -- the continuity of the pieces
  have hDF : ∀ l : Fin d, ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (D1 l F) := fun l =>
    ((sa12z3_cd_of_inf hF (m + 2)).fderiv_right (m := ((m + 1 : ℕ) : WithTop ℕ∞))
      (by exact_mod_cast le_refl _)).clm_apply contDiff_const
  have hQ : ∀ l : Fin d, ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fun y => a y * D1 l F y) := fun l =>
    ha.mul (hDF l)
  have hT : ∀ i l : Fin d, Continuous (firstRiesz d s i (partialDeriv idx (fun y => a y * D1 l F y))) := by
    intro i l
    have hv1 : ContDiff ℝ 1 (partialDeriv idx (fun y => a y * D1 l F y)) :=
      sa12x2_pd_cd (n := j) (k := 1) ((hQ l).of_le (by exact_mod_cast Nat.succ_le_succ hjm)) idx
    have hvc : HasCompactSupport (partialDeriv idx (fun y => a y * D1 l F y)) :=
      sa12z3_pd_compact (hac.mul_right) idx
    have hcd := sa12x2_convFun_cd hs0 hsd hv1 hvc
    exact (hcd.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hint : ∀ i l : Fin d, Integrable (fun x => M l i * ((w x ^ 2 * partialDeriv idx F x) *
      firstRiesz d s i (partialDeriv idx (fun y => a y * D1 l F y)) x)) volume := by
    intro i l
    refine Continuous.integrable_of_hasCompactSupport
      (continuous_const.mul (((hw.pow 2).mul hpc).mul (hT i l))) ?_
    refine HasCompactSupport.intro (K := tsupport w) hwc ?_
    intro x hx
    have : w x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [this]
  have hpt : ∀ x, w x ^ 2 * (partialDeriv idx F x * partialDeriv idx (eucNonlocal s M a F) x) =
      ∑ i : Fin d, ∑ l : Fin d, M l i * ((w x ^ 2 * partialDeriv idx F x) *
        firstRiesz d s i (partialDeriv idx (fun y => a y * D1 l F y)) x) := by
    intro x
    rw [sa12z3_pd_eucNL hs0 hsd M ha' hac hF hjm idx x]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
  refine (integral_congr_ae (Eventually.of_forall hpt)).trans ?_
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun l _ => hint i l)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun l _ => hint i l)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_const_mul]

end HRS.MH.AdjointRd.Phase2SA12Near
