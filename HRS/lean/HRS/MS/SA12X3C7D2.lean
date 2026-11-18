import HRS.MS.SA12X3C7D1

/-!
# S.A.12 C7 (SA12X3), part D2 (7D): a smooth representative of the far term with the pairing bound; smoothness of `eucNonlocal`
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MS.UniqT3 HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12x3_far_pairing_sm {s L : ℝ} {γ : Euc d → ℝ}
    (hγ : HRS.Whole.AppendixALemmas.IsPeriodicRieszKernel d s L γ) {h R' R'' : ℝ} (hh : 0 < h) (hR : 0 < R'')
    (hR'' : R' + h / 2 ≤ R'') (hRL : R'' < L / 2) {c : Euc d} (M : Matrix (Fin d) (Fin d) ℝ) (MB : ℝ)
    (hM : ∀ i j, |M i j| ≤ MB) {w η μ F : Euc d → ℝ} (hw : Continuous w) (hwc : HasCompactSupport w)
    (hη : Continuous η) (hμ : Continuous μ) (hF : ContDiff ℝ ∞ F)
    (hwN : ∀ x, w x ≠ 0 → x ∈ ball c R' ∧ ∀ y ∈ ball x h, η y = 1) (m : ℕ) {En Mass : ℝ}
    (hwp : ∀ n ≤ m, ∀ idx : Fin n → Fin d, ∫ x, (w x * partialDeriv idx F x) ^ 2 ≤ En)
    (hT : ∀ n ≤ m, ∀ (idx : Fin n → Fin d) (i j : Fin d),
      ∫ x, (w x * sa12x3_Tfar L γ c η μ F idx i j x) ^ 2 ≤ Mass) :
    ∃ Fs : Euc d → ℝ, ContDiff ℝ ∞ Fs ∧ (∀ x, w x ≠ 0 → sa12x3_Far L γ c M η μ F x = Fs x) ∧
      -(2 * jetPair m w F Fs) ≤ (∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * (d : ℝ) ^ j) *
        (En + (d : ℝ) ^ 4 * (max MB 0) ^ 2 * Mass) := by
  obtain ⟨Sh, hSs, hFar, -⟩ := sa12x3_far_pd hγ hh hR hR'' hRL M hw hη hμ hF hwN
  refine ⟨fun x => ∑ i : Fin d, ∑ j : Fin d, M j i * Sh i j x,
    ContDiff.sum fun i _ => ContDiff.sum fun j _ => contDiff_const.mul (hSs i j), hFar, ?_⟩
  have hjp := sa12x3_far_pairing hγ hh hR hR'' hRL M MB hM hw hwc hη hμ hF hwN m hwp hT
  have hopen : IsOpen {x : Euc d | w x ≠ 0} := isOpen_ne_fun hw continuous_const
  have hEq : EqOn (sa12x3_Far L γ c M η μ F) (fun x => ∑ i : Fin d, ∑ j : Fin d, M j i * Sh i j x)
      {x : Euc d | w x ≠ 0} := fun y hy => hFar y hy
  have : jetPair m w F (fun x => ∑ i : Fin d, ∑ j : Fin d, M j i * Sh i j x) =
      jetPair m w F (sa12x3_Far L γ c M η μ F) := by
    unfold jetPair
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    refine Finset.sum_congr rfl fun idx _ => ?_
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : w x = 0
    · simp [hx]
    · simp only
      rw [sa12x3_pd_congr_open hopen hEq idx hx]
  rw [this]
  exact hjp

theorem sa12x3_eucNL_smooth {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M : Matrix (Fin d) (Fin d) ℝ) {m : ℕ}
    {a F : Euc d → ℝ} (ha : ContDiff ℝ (m + 1) a) (hac : HasCompactSupport a) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ m (eucNonlocal s M a F) := by
  have ha1 : ContDiff ℝ 1 a := ha.of_le (by exact_mod_cast (by omega : 1 ≤ m + 1))
  have hDF : ∀ j, ContDiff ℝ (m + 1) (D1 j F) := fun j =>
    ((sa12z3_cd_of_inf hF (m + 2)).fderiv_right (m := (m + 1 : ℕ)) (by push_cast; rfl)).clm_apply contDiff_const
  have hP : ∀ j, ContDiff ℝ (m + 1) (fun y => a y * D1 j F y) := fun j => ha.mul (hDF j)
  have hPc : ∀ j, HasCompactSupport (fun y => a y * D1 j F y) := fun j => hac.mul_right
  have hQ : ∀ i j, ContDiff ℝ m (D1 i (fun y => a y * D1 j F y)) := fun i j =>
    ((hP j).fderiv_right (m := m) (by push_cast; rfl)).clm_apply contDiff_const
  have hQc : ∀ i j, HasCompactSupport (D1 i (fun y => a y * D1 j F y)) := fun i j => D1_supp (hPc j) i
  have hfn : eucNonlocal s M a F = fun y => ∑ i, ∑ j, M j i *
      HRS.Whole.convFun (rieszKernel d s) (D1 i (fun y => a y * D1 j F y)) y :=
    funext fun y => sa12z3_eucNL_eq hs0 hsd M ha1 hac hF y
  rw [hfn]
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => contDiff_const.mul ?_
  have := sa12x3_conv_smooth (N := m) (k := rieszKernel d s) (rieszKernel_locallyIntegrable hs0 hsd) (hQ i j) (hQc i j)
  have e : HRS.Whole.convFun (rieszKernel d s) (D1 i (fun y => a y * D1 j F y)) =
      fun x => ∫ y, rieszKernel d s (x - y) * D1 i (fun y => a y * D1 j F y) y := rfl
  rw [e]
  exact this

end HRS.MH.AdjointRd.Phase2SA12Near
