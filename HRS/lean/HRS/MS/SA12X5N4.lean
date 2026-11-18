import HRS.MS.SA12X5N3
import HRS.MS.SA12X2R36

/-!
# S.A.12 X5 N4: the `L²` bound of `w ∂^{idx}` of the Euclidean near operator by Young, given the `L²` norm of the jets of `a' D1 F`
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12X5

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3 HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12Near
  HRS.MH.AdjointRdP

variable {d : ℕ}

theorem sa12x5_near_young (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (M : Matrix (Fin d) (Fin d) ℝ) {MB : ℝ} (hM : PDE.MatBound MB M) {m : ℕ} {a' F w : Euc d → ℝ}
    {c : Euc d} {R : ℝ} (ha' : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) a') (hac : HasCompactSupport a')
    (hF : ContDiff ℝ ∞ F) (hw : Continuous w) (hws : Function.support w ⊆ closedBall c R)
    (hw1 : ∀ x, |w x| ≤ 1) (hsupp : Function.support a' ⊆ closedBall c R) {CK V : ℝ}
    (hCK : ∫ u in closedBall (0 : Euc d) (R + R), |rieszKernel d s u| ≤ CK) {n : ℕ} (hn : n ≤ m)
    (idx : Fin n → Fin d)
    (hV : ∀ i l : Fin d, ∫ x, partialDeriv (Fin.cons i idx : Fin (n + 1) → Fin d)
      (fun y => a' y * D1 l F y) x ^ 2 ≤ V) :
    ∫ x, (w x * partialDeriv idx (eucNonlocal s M a' F) x) ^ 2 ≤ (d : ℝ) ^ 4 * MB ^ 2 * CK ^ 2 * V := by
  have hK : LocallyIntegrable (rieszKernel d s) (volume : Measure (Euc d)) :=
    rieszKernel_locallyIntegrable hs0 hsd
  have hKm : Measurable (rieszKernel d s) := r3_meas_g s
  have hKi : IntegrableOn (rieszKernel d s) (closedBall (0 : Euc d) (R + R)) :=
    hK.integrableOn_isCompact (isCompact_closedBall _ _)
  have hwc : HasCompactSupport w :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall c R) hws
  have hDF : ∀ l : Fin d, ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (D1 l F) := fun l =>
    ((hF.fderiv_right (m := ∞) (by simp)).of_le (by exact_mod_cast le_top)).clm_apply contDiff_const
  have hg : ∀ l : Fin d, ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fun y => a' y * D1 l F y) :=
    fun l => ha'.mul (hDF l)
  have hgc : ∀ l : Fin d, HasCompactSupport (fun y => a' y * D1 l F y) := fun l => hac.mul_right
  -- the pieces
  set v : Fin d → Fin d → Euc d → ℝ := fun i l =>
    partialDeriv (Fin.cons i idx : Fin (n + 1) → Fin d) (fun y => a' y * D1 l F y) with hv
  have hvc : ∀ i l, Continuous (v i l) := fun i l => by
    have := sa12z3_pd_contDiff (k := m + 1) (n := n + 1) (hg l) (by omega) (Fin.cons i idx)
    exact this.continuous
  have hvcs : ∀ i l, HasCompactSupport (v i l) := fun i l => sa12z3_pd_compact (hgc l) _
  have hvsupp : ∀ i l, Function.support (v i l) ⊆ closedBall c R := fun i l => by
    intro x hx
    have h1 := sa12z3_pd_support (Fin.cons i idx : Fin (n + 1) → Fin d) hx
    have h2 : tsupport (fun y => a' y * D1 l F y) ⊆ tsupport a' := tsupport_mul_subset_left
    have h3 : tsupport a' ⊆ closedBall c R := closure_minimal hsupp isClosed_closedBall
    exact h3 (h2 h1)
  set T : Fin d → Fin d → Euc d → ℝ := fun i l x => ∫ y, rieszKernel d s (x - y) * v i l y with hT
  have hTc : ∀ i l, Continuous (T i l) := fun i l =>
    (sa12x2_convFun_cd hs0 hsd (k := 0) (contDiff_zero.2 (hvc i l)) (hvcs i l)).continuous
  -- the pointwise expansion
  have hexp : ∀ x, w x * partialDeriv idx (eucNonlocal s M a' F) x =
      ∑ i : Fin d, ∑ l : Fin d, M l i * (w x * T i l x) := by
    intro x
    rw [sa12z3_pd_eucNL hs0 hsd M ha' hac hF hn idx x, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    have hP1 : ContDiff ℝ 1 (partialDeriv idx (fun y => a' y * D1 l F y)) := by
      have := sa12z3_pd_contDiff (k := m + 1) (n := n) (hg l) (by omega) idx
      refine this.of_le ?_
      exact_mod_cast (by omega : 1 ≤ m + 1 - n)
    have hPc := sa12z3_pd_compact (hgc l) idx
    have hg' : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) (fun y => a' y * D1 l F y) :=
      (hg l).of_le (by exact_mod_cast (by omega : n + 1 ≤ m + 1))
    have e1 : firstRiesz d s i (partialDeriv idx (fun y => a' y * D1 l F y)) x = T i l x := by
      have e2 : firstRiesz d s i (partialDeriv idx (fun y => a' y * D1 l F y)) x =
          D1 i (HRS.Whole.convFun (rieszKernel d s) (partialDeriv idx (fun y => a' y * D1 l F y))) x := rfl
      rw [e2, convFun_D1 hK hP1 hPc i x]
      unfold HRS.Whole.convFun
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [hv]
      rw [sa12z3_pd_cons idx i hg' y]
    rw [e1]; ring
  -- the pointwise square bound
  have hpt : ∀ x, (w x * partialDeriv idx (eucNonlocal s M a' F) x) ^ 2 ≤
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
  -- integrability of the right side and the Young bound
  have hint : ∀ i l : Fin d, Integrable (fun x => (w x * T i l x) ^ 2) volume := fun i l => by
    refine Continuous.integrable_of_hasCompactSupport ((hw.mul (hTc i l)).pow 2) ?_
    exact (hwc.mul_right (f' := T i l)).comp_left (g := fun t : ℝ => t ^ 2) (by simp)
  have hY : ∀ i l : Fin d, ∫ x, (w x * T i l x) ^ 2 ≤ CK ^ 2 * V := fun i l => by
    have h := sa12x5_young_loc (K := rieszKernel d s) hKm hKi hCK (c := c) (R := R) (R' := R) le_rfl
      (hvc i l) (hvcs i l) (hvsupp i l) (hTc i l).aestronglyMeasurable hw hws hw1
    exact h.trans (mul_le_mul_of_nonneg_left (hV i l) (sq_nonneg _))
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
