import HRS.MS.SA12X5N5

/-!
# S.A.12 X5 N6: the smooth (bounded kernel) part of the near identity: Young bound for `∂^{idx}` of
`∑_{i,l} M_{li} (k_i ⋆ (a' ∂_l F))` with continuous kernels `k_i`
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12X5

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3 HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Near
  HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRdP

variable {d : ℕ}

theorem sa12x5_convFun_cd {K : Euc d → ℝ} (hK : LocallyIntegrable K (volume : Measure (Euc d))) {k : ℕ}
    {Q : Euc d → ℝ} (hQ : ContDiff ℝ k Q) (hQc : HasCompactSupport Q) :
    ContDiff ℝ k (HRS.Whole.convFun K Q) := by
  have hfun : HRS.Whole.convFun K Q = K ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] Q := by
    funext x'
    have h := integral_sub_left_eq_self (μ := volume) (fun t => K t * Q (x' - t)) x'
    simp only [sub_sub_cancel] at h
    simpa [convolution_def, HRS.Whole.convFun] using h
  rw [hfun]
  exact hQc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hK hQ

theorem sa12x5_conv_young_gen (hd : 1 ≤ d) {kk : Fin d → Euc d → ℝ} (hkc : ∀ i, Continuous (kk i))
    (M : Matrix (Fin d) (Fin d) ℝ) {MB : ℝ} (hM : PDE.MatBound MB M) {m : ℕ} {a' F w : Euc d → ℝ}
    {c : Euc d} {R : ℝ} (ha' : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) a') (hac : HasCompactSupport a')
    (hF : ContDiff ℝ ∞ F) (hw : Continuous w) (hws : Function.support w ⊆ closedBall c R)
    (hw1 : ∀ x, |w x| ≤ 1) (hsupp : Function.support a' ⊆ closedBall c R) {CK V : ℝ}
    (hCK : ∀ i, ∫ u in closedBall (0 : Euc d) (R + R), |kk i u| ≤ CK) {n : ℕ} (hn : n ≤ m)
    (idx : Fin n → Fin d)
    (hV : ∀ l : Fin d, ∫ x, partialDeriv idx (fun y => a' y * D1 l F y) x ^ 2 ≤ V) :
    ∫ x, (w x * partialDeriv idx (fun x => ∑ i : Fin d, ∑ l : Fin d, M l i *
      HRS.Whole.convFun (kk i) (fun y => a' y * D1 l F y) x) x) ^ 2 ≤ (d : ℝ) ^ 4 * MB ^ 2 * CK ^ 2 * V := by
  have hKl : ∀ i, LocallyIntegrable (kk i) (volume : Measure (Euc d)) := fun i => (hkc i).locallyIntegrable
  have hKm : ∀ i, Measurable (kk i) := fun i => (hkc i).measurable
  have hKi : ∀ i, IntegrableOn (kk i) (closedBall (0 : Euc d) (R + R)) := fun i =>
    (hKl i).integrableOn_isCompact (isCompact_closedBall _ _)
  have hwc : HasCompactSupport w :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c R) hws
  have hDF : ∀ l : Fin d, ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (D1 l F) := fun l =>
    ((hF.fderiv_right (m := ∞) (by simp)).of_le (by exact_mod_cast le_top)).clm_apply contDiff_const
  have hg : ∀ l : Fin d, ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fun y => a' y * D1 l F y) :=
    fun l => ha'.mul (hDF l)
  have hgc : ∀ l : Fin d, HasCompactSupport (fun y => a' y * D1 l F y) := fun l => hac.mul_right
  set v : Fin d → Euc d → ℝ := fun l => partialDeriv idx (fun y => a' y * D1 l F y) with hv
  have hvc : ∀ l, Continuous (v l) := fun l => by
    have := sa12z3_pd_contDiff (k := m + 1) (n := n) (hg l) (by omega) idx
    exact this.continuous
  have hvcs : ∀ l, HasCompactSupport (v l) := fun l => sa12z3_pd_compact (hgc l) _
  have hvsupp : ∀ l, Function.support (v l) ⊆ closedBall c R := fun l => by
    intro x hx
    have h1 := sa12z3_pd_support idx hx
    have h2 : tsupport (fun y => a' y * D1 l F y) ⊆ tsupport a' := tsupport_mul_subset_left
    have h3 : tsupport a' ⊆ closedBall c R := closure_minimal hsupp isClosed_closedBall
    exact h3 (h2 h1)
  set T : Fin d → Fin d → Euc d → ℝ := fun i l x => ∫ y, kk i (x - y) * v l y with hT
  have hTc : ∀ i l, Continuous (T i l) := fun i l =>
    (sa12x5_convFun_cd (hKl i) (k := 0) (contDiff_zero.2 (hvc l)) (hvcs l)).continuous
  have hcdn : ∀ i l, ContDiff ℝ n (HRS.Whole.convFun (kk i) (fun y => a' y * D1 l F y)) := fun i l =>
    sa12x5_convFun_cd (hKl i) ((hg l).of_le (by exact_mod_cast (by omega : n ≤ m + 1))) (hgc l)
  have hexp : ∀ x, w x * partialDeriv idx (fun x => ∑ i : Fin d, ∑ l : Fin d, M l i *
      HRS.Whole.convFun (kk i) (fun y => a' y * D1 l F y) x) x =
      ∑ i : Fin d, ∑ l : Fin d, M l i * (w x * T i l x) := by
    intro x
    have h1 := sa12z3_pd_sum (Finset.univ : Finset (Fin d)) (fun i y => ∑ l : Fin d, M l i *
      HRS.Whole.convFun (kk i) (fun y => a' y * D1 l F y) y) (fun _ => 1) (n := n)
      (fun i _ => ContDiff.sum fun l _ => contDiff_const.mul (hcdn i l)) idx x
    simp only [one_mul] at h1
    rw [h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h2 := sa12z3_pd_sum (Finset.univ : Finset (Fin d)) (fun l y =>
      HRS.Whole.convFun (kk i) (fun y => a' y * D1 l F y) y) (fun l => M l i) (n := n)
      (fun l _ => hcdn i l) idx x
    rw [h2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have e1 := sa12x5_pd_convFun (hKl i) n (fun y => a' y * D1 l F y)
      ((hg l).of_le (by exact_mod_cast (by omega : n ≤ m + 1))) (hgc l) idx x
    rw [e1]
    simp only [hT, hv, HRS.Whole.convFun]
    ring
  have hpt : ∀ x, (w x * partialDeriv idx (fun x => ∑ i : Fin d, ∑ l : Fin d, M l i *
      HRS.Whole.convFun (kk i) (fun y => a' y * D1 l F y) x) x) ^ 2 ≤
      (d : ℝ) ^ 2 * MB ^ 2 * ∑ i : Fin d, ∑ l : Fin d, (w x * T i l x) ^ 2 := by
    intro x
    rw [hexp x]
    have h1 := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
      (f := fun i => ∑ l : Fin d, M l i * (w x * T i l x))
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    have h2 : ∀ i : Fin d, (∑ l : Fin d, M l i * (w x * T i l x)) ^ 2 ≤
        (d : ℝ) * ∑ l : Fin d, (M l i * (w x * T i l x)) ^ 2 := fun i => by
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
        (f := fun l => M l i * (w x * T i l x))
      simpa only [Finset.card_univ, Fintype.card_fin] using this
    have h3 : ∀ i l : Fin d, (M l i * (w x * T i l x)) ^ 2 ≤ MB ^ 2 * (w x * T i l x) ^ 2 := fun i l => by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (by
        have := hM l i
        nlinarith [abs_nonneg (M l i), sq_abs (M l i)]) (sq_nonneg _)
    calc (∑ i : Fin d, ∑ l : Fin d, M l i * (w x * T i l x)) ^ 2
        ≤ (d : ℝ) * ∑ i : Fin d, (∑ l : Fin d, M l i * (w x * T i l x)) ^ 2 := h1
      _ ≤ (d : ℝ) * ∑ i : Fin d, ((d : ℝ) * ∑ l : Fin d, MB ^ 2 * (w x * T i l x) ^ 2) := by
          gcongr with i _
          refine (h2 i).trans ?_
          gcongr with l _
          exact h3 i l
      _ = (d : ℝ) ^ 2 * MB ^ 2 * ∑ i : Fin d, ∑ l : Fin d, (w x * T i l x) ^ 2 := by
          simp only [← Finset.mul_sum]
          ring
  have hint : ∀ i l : Fin d, Integrable (fun x => (w x * T i l x) ^ 2) volume := fun i l => by
    refine Continuous.integrable_of_hasCompactSupport ((hw.mul (hTc i l)).pow 2) ?_
    exact (hwc.mul_right (f' := T i l)).comp_left (g := fun t : ℝ => t ^ 2) (by simp)
  have hY : ∀ i l : Fin d, ∫ x, (w x * T i l x) ^ 2 ≤ CK ^ 2 * V := fun i l => by
    have h := sa12x5_young_loc (K := kk i) (hKm i) (hKi i) (hCK i) (c := c) (R := R) (R' := R) le_rfl
      (hvc l) (hvcs l) (hvsupp l) (hTc i l).aestronglyMeasurable hw hws hw1
    exact h.trans (mul_le_mul_of_nonneg_left (hV l) (sq_nonneg _))
  have hRint : Integrable (fun x => (d : ℝ) ^ 2 * MB ^ 2 * ∑ i : Fin d, ∑ l : Fin d, (w x * T i l x) ^ 2) volume :=
    (integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun l _ => hint i l).const_mul _
  refine (integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _) hRint
    (Eventually.of_forall hpt)).trans ?_
  rw [integral_const_mul, integral_finset_sum _ fun i _ => integrable_finset_sum _ fun l _ => hint i l]
  have hsum : ∑ i : Fin d, ∫ x, ∑ l : Fin d, (w x * T i l x) ^ 2 ≤ (d : ℝ) * ((d : ℝ) * (CK ^ 2 * V)) := by
    calc ∑ i : Fin d, ∫ x, ∑ l : Fin d, (w x * T i l x) ^ 2
        = ∑ i : Fin d, ∑ l : Fin d, ∫ x, (w x * T i l x) ^ 2 :=
          Finset.sum_congr rfl fun i _ => integral_finset_sum _ fun l _ => hint i l
      _ ≤ ∑ i : Fin d, ∑ l : Fin d, CK ^ 2 * V := by
          gcongr with i _ l _
          exact hY i l
      _ = _ := by simp
  calc (d : ℝ) ^ 2 * MB ^ 2 * ∑ i : Fin d, ∫ x, ∑ l : Fin d, (w x * T i l x) ^ 2
      ≤ (d : ℝ) ^ 2 * MB ^ 2 * ((d : ℝ) * ((d : ℝ) * (CK ^ 2 * V))) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (d : ℝ) ^ 4 * MB ^ 2 * CK ^ 2 * V := by ring

end HRS.MH.AdjointRd.Phase2SA12X5
