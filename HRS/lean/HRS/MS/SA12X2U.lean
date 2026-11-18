import HRS.MS.SA12X2T

/-!
# S.A.12 N8 (SA12X2), part U: the decomposition of the tuple pairing for skew `M`

`∫ ω² u ∂^{idx}𝒢 = ∑ M_{ji} (-∫ ω² u T_i((∂_j a) u) + ∫ ω² u T_i(R_j))` (the Hessian terms cancel).
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3

variable {d : ℕ}

theorem sa12x2_decomp {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {m : ℕ} (hm : 1 ≤ m)
    {M : Matrix (Fin d) (Fin d) ℝ} (hsk : Torus.symPart M = 0) {a F om : Euc d → ℝ}
    (ha : ContDiff ℝ (m + 1) a) (hac : HasCompactSupport a) (hF : ContDiff ℝ ∞ F)
    (hom : Continuous om) (homc : HasCompactSupport om) {n : ℕ} (hn : n ≤ m) (idx : Fin n → Fin d) :
    ∫ x, om x ^ 2 * (partialDeriv idx F x * partialDeriv idx (eucNonlocal s M a F) x) =
      ∑ i, ∑ j, M j i * (-(∫ x, om x ^ 2 * (partialDeriv idx F x *
          firstRiesz d s i (fun y => D1 j a y * partialDeriv idx F y) x)) +
        ∫ x, om x ^ 2 * (partialDeriv idx F x * firstRiesz d s i (sa12z3_Rj a F idx j) x)) := by
  set u : Euc d → ℝ := partialDeriv idx F with hu
  have hu_inf : ContDiff ℝ ∞ u := sa12z3_pd_contDiff_inf hF idx
  have huc : Continuous u := hu_inf.continuous
  have ha1 : ContDiff ℝ 1 a := ha.of_le (by exact_mod_cast (by omega : 1 ≤ m + 1))
  have ha2 : ContDiff ℝ 2 a := ha.of_le (by exact_mod_cast (by omega : 2 ≤ m + 1))
  have hu2 : ContDiff ℝ 2 u := sa12z3_cd_of_inf hu_inf 2
  have hv1 : ContDiff ℝ 2 (fun y => a y * u y) := ha2.mul hu2
  have hv1c : HasCompactSupport (fun y => a y * u y) := hac.mul_right
  have hDja : ∀ j, ContDiff ℝ 1 (D1 j a) := fun j =>
    (ha2.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hv2 : ∀ j, ContDiff ℝ 1 (fun y => D1 j a y * u y) := fun j =>
    (hDja j).mul (sa12z3_cd_of_inf hu_inf 1)
  have hv2c : ∀ j, HasCompactSupport (fun y => D1 j a y * u y) := fun j => (D1_supp hac j).mul_right
  have hDju : ∀ j, ContDiff ℝ 1 (D1 j u) := fun j =>
    (hu2.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hDF : ∀ j, ContDiff ℝ (m + 1) (D1 j F) := fun j =>
    ((sa12z3_cd_of_inf hF (m + 2)).fderiv_right (m := (m + 1 : ℕ)) (by push_cast; rfl)).clm_apply contDiff_const
  have hP : ∀ j, ContDiff ℝ (m + 1) (fun y => a y * D1 j F y) := fun j => ha.mul (hDF j)
  have hPc : ∀ j, HasCompactSupport (fun y => a y * D1 j F y) := fun j => hac.mul_right
  have hΦ1 : ∀ j, ContDiff ℝ 1 (partialDeriv idx (fun y => a y * D1 j F y)) := fun j => by
    have := sa12z3_pd_contDiff (k := m + 1) (n := n) (hP j) (by omega) idx
    exact this.of_le (by norm_cast; omega)
  have hv3 : ∀ j, ContDiff ℝ 1 (sa12z3_Rj a F idx j) := fun j => (hΦ1 j).sub (ha1.mul (hDju j))
  have hv3c : ∀ j, HasCompactSupport (sa12z3_Rj a F idx j) := fun j =>
    (sa12z3_pd_compact (hPc j) idx).sub hac.mul_right
  have hdec := fun (x : Euc d) => sa12z3_pd_G_decomp hs0 hsd M hm ha hac hF hn idx x
  have hom2c : HasCompactSupport (fun x => om x ^ 2) :=
    homc.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
  have hint : ∀ {X : Euc d → ℝ}, Continuous X → Integrable (fun x => om x ^ 2 * (u x * X x)) volume :=
    fun {X} hX => Continuous.integrable_of_hasCompactSupport (f := fun x => om x ^ 2 * (u x * X x))
      ((hom.pow 2).mul (huc.mul hX)) (hom2c.mul_right)
  have hcH := fun i j : Fin d => sa12z3_hess_cont hs0 hsd i j hv1 hv1c
  have hcT2 := fun i j : Fin d => sa12z3_firstRiesz_cont hs0 hsd i (hv2 j) (hv2c j)
  have hcT3 := fun i j : Fin d => sa12z3_firstRiesz_cont hs0 hsd i (hv3 j) (hv3c j)
  set HH : Fin d → Fin d → Euc d → ℝ := fun i j => hessRiesz d s i j (fun y => a y * u y) with hHH
  set T2 : Fin d → Fin d → Euc d → ℝ := fun i j => firstRiesz d s i (fun y => D1 j a y * u y) with hT2
  set T3 : Fin d → Fin d → Euc d → ℝ := fun i j => firstRiesz d s i (sa12z3_Rj a F idx j) with hT3
  have hIij : ∀ i j : Fin d, Integrable (fun x => M j i * (om x ^ 2 * (u x * HH i j x) -
      om x ^ 2 * (u x * T2 i j x) + om x ^ 2 * (u x * T3 i j x))) volume := fun i j =>
    (((hint (hcH i j)).sub (hint (hcT2 i j))).add (hint (hcT3 i j))).const_mul _
  have e1 : ∀ x, om x ^ 2 * (u x * partialDeriv idx (eucNonlocal s M a F) x) = ∑ i, ∑ j, M j i *
      (om x ^ 2 * (u x * HH i j x) - om x ^ 2 * (u x * T2 i j x) + om x ^ 2 * (u x * T3 i j x)) := by
    intro x
    rw [hdec x, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by simp only [hHH, hT2, hT3]; ring
  have h0 := sa12x2_skew_sum hsk (fun i j => ∫ x, om x ^ 2 * (u x * HH i j x)) (fun i j => by
    simp only [hHH, sa12x2_hess_symm hs0 hsd i j hv1 hv1c])
  simp_rw [e1]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hIij i j)]
  have hterm : ∀ i j : Fin d, ∫ x, M j i * (om x ^ 2 * (u x * HH i j x) -
      om x ^ 2 * (u x * T2 i j x) + om x ^ 2 * (u x * T3 i j x)) =
      M j i * (∫ x, om x ^ 2 * (u x * HH i j x)) +
        M j i * (-(∫ x, om x ^ 2 * (u x * T2 i j x)) + ∫ x, om x ^ 2 * (u x * T3 i j x)) := by
    intro i j
    rw [integral_const_mul]
    have hI12 : Integrable (fun x => om x ^ 2 * (u x * HH i j x) - om x ^ 2 * (u x * T2 i j x)) volume :=
      (hint (hcH i j)).sub (hint (hcT2 i j))
    rw [integral_add hI12 (hint (hcT3 i j)), integral_sub (hint (hcH i j)) (hint (hcT2 i j))]
    ring
  have hrow : ∀ i : Fin d, ∫ x, ∑ j, M j i * (om x ^ 2 * (u x * HH i j x) -
      om x ^ 2 * (u x * T2 i j x) + om x ^ 2 * (u x * T3 i j x)) =
      ∑ j, (M j i * (∫ x, om x ^ 2 * (u x * HH i j x)) +
        M j i * (-(∫ x, om x ^ 2 * (u x * T2 i j x)) + ∫ x, om x ^ 2 * (u x * T3 i j x))) := by
    intro i
    rw [integral_finsetSum _ (fun j _ => hIij i j)]
    exact Finset.sum_congr rfl fun j _ => hterm i j
  simp_rw [hrow, Finset.sum_add_distrib]
  rw [h0, zero_add]

end HRS.MH.AdjointRd.Phase2SA12Near
