import HRS.MS.SA12Z3NearN7A
import HRS.MS.UniqN1cA

/-!
# S.A.12 N7 (SA12Z3), part B: the decomposition of `∂^{idx} eucNonlocal`

For `a ∈ C^{m+1}_c`, `F ∈ C^∞` and `|idx| = n ≤ m`, `u = ∂^{idx} F`:
`∂^{idx} (eucNonlocal a F) = ∑_{ij} M_{ji} (hessRiesz_{ij}(a u) - T_i((∂_j a) u) + T_i R_j)`,
`R_j = ∂^{idx}(a ∂_j F) - a ∂_j u`, `T_i = firstRiesz`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.UniqT3

variable {d : ℕ}

/-- `eucNonlocal` as a sum of convolutions. -/
theorem sa12z3_eucNL_eq {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M : Matrix (Fin d) (Fin d) ℝ)
    {a F : Euc d → ℝ} (ha : ContDiff ℝ 1 a) (hac : HasCompactSupport a) (hF : ContDiff ℝ ∞ F)
    (x : Euc d) :
    eucNonlocal s M a F x = ∑ i, ∑ j, M j i *
      HRS.Whole.convFun (rieszKernel d s) (D1 i (fun y => a y * D1 j F y)) x := by
  have hK : LocallyIntegrable (rieszKernel d s) (volume : Measure (Euc d)) :=
    rieszKernel_locallyIntegrable hs0 hsd
  unfold eucNonlocal
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have hDF : ContDiff ℝ 1 (D1 j F) := (sa12z3_cd_of_inf hF 2 |>.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hP : ContDiff ℝ 1 (fun y => a y * D1 j F y) := ha.mul hDF
  have hPc : HasCompactSupport (fun y => a y * D1 j F y) := hac.mul_right
  have := convFun_D1 hK hP hPc i x
  exact this

/-- Linearity of `partialDeriv` over finite sums. -/
theorem sa12z3_pd_sum {ι : Type*} (u : Finset ι) (f : ι → Euc d → ℝ) (c : ι → ℝ) {n : ℕ}
    (h : ∀ t ∈ u, ContDiff ℝ n (f t)) (idx : Fin n → Fin d) (x : Euc d) :
    partialDeriv idx (fun y => ∑ t ∈ u, c t * f t y) x = ∑ t ∈ u, c t * partialDeriv idx (f t) x := by
  unfold partialDeriv
  have h1 := iteratedFDeriv_fun_sum_apply (𝕜 := ℝ) (u := u) (f := fun t y => c t * f t y) (n := n)
    (x := x) (fun t ht => (contDiff_const.mul (h t ht)).contDiffAt)
  rw [h1]
  simp only [ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl fun t ht => ?_
  have h2 : (fun y => c t * f t y) = fun y => c t • f t y := by funext y; simp [smul_eq_mul]
  rw [h2, iteratedFDeriv_const_smul_apply' (h t ht).contDiffAt]
  simp

/-- `∂^{idx}` of `eucNonlocal`. -/
theorem sa12z3_pd_eucNL {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (M : Matrix (Fin d) (Fin d) ℝ) {m : ℕ}
    {a F : Euc d → ℝ} (ha : ContDiff ℝ (m + 1) a) (hac : HasCompactSupport a) (hF : ContDiff ℝ ∞ F)
    {n : ℕ} (hn : n ≤ m) (idx : Fin n → Fin d) (x : Euc d) :
    partialDeriv idx (eucNonlocal s M a F) x = ∑ i, ∑ j, M j i *
      firstRiesz d s i (partialDeriv idx (fun y => a y * D1 j F y)) x := by
  have hK : LocallyIntegrable (rieszKernel d s) (volume : Measure (Euc d)) :=
    rieszKernel_locallyIntegrable hs0 hsd
  have ha1 : ContDiff ℝ 1 a := ha.of_le (by exact_mod_cast (by omega : 1 ≤ m + 1))
  have hDF : ∀ j, ContDiff ℝ (m + 1) (D1 j F) := fun j =>
    ((sa12z3_cd_of_inf hF (m + 2)).fderiv_right (m := (m + 1 : ℕ)) (by push_cast; rfl)).clm_apply contDiff_const
  have hP : ∀ j, ContDiff ℝ (m + 1) (fun y => a y * D1 j F y) := fun j => ha.mul (hDF j)
  have hPc : ∀ j, HasCompactSupport (fun y => a y * D1 j F y) := fun j => hac.mul_right
  have hQ : ∀ i j, ContDiff ℝ m (D1 i (fun y => a y * D1 j F y)) := fun i j =>
    ((hP j).fderiv_right (m := m) (by push_cast; rfl)).clm_apply contDiff_const
  have hQc : ∀ i j, HasCompactSupport (D1 i (fun y => a y * D1 j F y)) := fun i j => D1_supp (hPc j) i
  have hcd : ∀ i j, ContDiff ℝ n (HRS.Whole.convFun (rieszKernel d s) (D1 i (fun y => a y * D1 j F y))) := by
    intro i j
    have hfun : HRS.Whole.convFun (rieszKernel d s) (D1 i (fun y => a y * D1 j F y)) =
        rieszKernel d s ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] (D1 i (fun y => a y * D1 j F y)) := by
      funext x'
      have h := integral_sub_left_eq_self (μ := volume)
        (fun t => rieszKernel d s t * (D1 i (fun y => a y * D1 j F y)) (x' - t)) x'
      simp only [sub_sub_cancel] at h
      simpa [convolution_def, HRS.Whole.convFun] using h
    rw [hfun]
    exact (hQc i j).contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hK
      ((hQ i j).of_le (by exact_mod_cast hn))
  have hfn : eucNonlocal s M a F = fun y => ∑ i, ∑ j, M j i *
      HRS.Whole.convFun (rieszKernel d s) (D1 i (fun y => a y * D1 j F y)) y :=
    funext fun y => sa12z3_eucNL_eq hs0 hsd M ha1 hac hF y
  rw [hfn]
  have hin : ∀ i, ContDiff ℝ n (fun y => ∑ j, M j i *
      HRS.Whole.convFun (rieszKernel d s) (D1 i (fun y => a y * D1 j F y)) y) := fun i =>
    ContDiff.sum fun j _ => contDiff_const.mul (hcd i j)
  have h1 := sa12z3_pd_sum (Finset.univ : Finset (Fin d)) (fun i y => ∑ j, M j i *
      HRS.Whole.convFun (rieszKernel d s) (D1 i (fun y => a y * D1 j F y)) y) (fun _ => 1) (n := n)
    (fun i _ => hin i) idx x
  simp only [one_mul] at h1
  rw [h1]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 := sa12z3_pd_sum (Finset.univ : Finset (Fin d)) (fun j y =>
      HRS.Whole.convFun (rieszKernel d s) (D1 i (fun y => a y * D1 j F y)) y) (fun j => M j i) (n := n)
    (fun j _ => hcd i j) idx x
  rw [h2]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  have e1 := sa12z3_pd_conv hs0 hsd n (D1 i (fun y => a y * D1 j F y))
    ((hQ i j).of_le (by exact_mod_cast hn)) (hQc i j) idx x
  have hPn : ContDiff ℝ (n + 1) (fun y => a y * D1 j F y) :=
    (hP j).of_le (by exact_mod_cast Nat.succ_le_succ hn)
  have e2 : partialDeriv idx (D1 i (fun y => a y * D1 j F y)) =
      D1 i (partialDeriv idx (fun y => a y * D1 j F y)) := by
    funext y
    exact sa12z3_pd_D1_comm i n _ hPn idx y
  rw [e1, e2]
  have hΦ : ContDiff ℝ 1 (partialDeriv idx (fun y => a y * D1 j F y)) := by
    have := sa12z3_pd_contDiff (k := m + 1) (n := n) (hP j) (by omega) idx
    exact this.of_le (by norm_cast; omega)
  have := convFun_D1 hK hΦ (sa12z3_pd_compact (hPc j) idx) i x
  exact this.symm

end HRS.MH.AdjointRd.Phase2SA12Near
