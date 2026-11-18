import HRS.MS.SA16TLm2

/-!
# S.A.16 (SA16T) Lm3: the divergence test function of the smoothed drift

`sa16t_div_tendsto`: `sa16so_divFun (sa16t_bcv d n b) ψ x → movDiv (ψ • b) x` pointwise (`b, ψ ∈ C^1`).
`sa16t_div_bound`, `sa16t_div_vanish`: a bound by `d (B1 |ψ| + Cb |∇ψ|)` supported in `tsupport ψ`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R

open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16P

section Lm3
variable {d : ℕ}

lemma sa16t_divFun_eq {bc : Fin d → Euc d → ℝ} (hb : ∀ i, ContDiff ℝ 1 (bc i)) {ψ : Euc d → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (x : Euc d) :
    sa16so_divFun bc ψ x = ∑ i : Fin d, (ψ x * HRS.MS.UniqT3.D1 i (bc i) x + bc i x * HRS.MS.UniqT3.D1 i ψ x) := by
  unfold sa16so_divFun
  refine Finset.sum_congr rfl fun i _ => ?_
  have hdb : DifferentiableAt ℝ (bc i) x := ((hb i).differentiable (by norm_num)) x
  have hdψ : DifferentiableAt ℝ ψ x := (hψ.differentiable (by norm_num)) x
  have : fderiv ℝ (fun y => bc i y * ψ y) x = bc i x • fderiv ℝ ψ x + ψ x • fderiv ℝ (bc i) x :=
    (hdb.hasFDerivAt.mul hdψ.hasFDerivAt).fderiv
  rw [this]
  simp [HRS.MS.UniqT3.D1]
  ring

lemma sa16t_movDiv_eq {b : Euc d → Euc d} (hb : ContDiff ℝ 1 b) {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ) (x : Euc d) :
    movDiv (fun y => ψ y • b y) x = ∑ i : Fin d, (ψ x * HRS.MS.UniqT3.D1 i (fun y => b y i) x +
      b x i * HRS.MS.UniqT3.D1 i ψ x) := by
  unfold movDiv
  refine Finset.sum_congr rfl fun i _ => ?_
  have hF : DifferentiableAt ℝ (fun y => ψ y • b y) x :=
    (hψ.differentiable (by norm_num) x).smul (hb.differentiable (by norm_num) x)
  have hcomp := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).hasFDerivAt.comp x hF.hasFDerivAt
  have h1 : fderiv ℝ (fun y => ψ y * b y i) x = fderiv ℝ (fun y => (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) (ψ y • b y)) x := by
    congr 1
  have h2 := hcomp.fderiv
  have hdb : DifferentiableAt ℝ (fun y => b y i) x :=
    ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).differentiableAt.comp x (hb.differentiable (by norm_num) x))
  have hdψ : DifferentiableAt ℝ ψ x := (hψ.differentiable (by norm_num)) x
  have h3 : fderiv ℝ (fun y => ψ y * b y i) x = ψ x • fderiv ℝ (fun y => b y i) x + b x i • fderiv ℝ ψ x :=
    (hdψ.hasFDerivAt.mul hdb.hasFDerivAt).fderiv
  have h4 : (fderiv ℝ (fun y => ψ y • b y) x (EuclideanSpace.single i 1)) i =
      fderiv ℝ (fun y => ψ y * b y i) x (EuclideanSpace.single i 1) := by
    rw [h1]
    have : fderiv ℝ (fun y => (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) (ψ y • b y)) x =
        (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).comp (fderiv ℝ (fun y => ψ y • b y) x) := h2
    rw [this]; rfl
  rw [h4, h3]
  simp [HRS.MS.UniqT3.D1, mul_comm]

theorem sa16t_div_tendsto {b : Euc d → Euc d} (hb : ContDiff ℝ 1 b) {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (x : Euc d) :
    Tendsto (fun n => sa16so_divFun (sa16t_bcv d n b) ψ x) atTop (𝓝 (movDiv (fun y => ψ y • b y) x)) := by
  have hgi : ∀ i : Fin d, ContDiff ℝ 1 (fun y => b y i) := fun i =>
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff.comp hb
  rw [sa16t_movDiv_eq hb hψ x]
  have hsm : ∀ n, ∀ i, ContDiff ℝ 1 (sa16t_bcv d n b i) := fun n i =>
    (contDiff_infty.1 (sa16t_bc_smooth (hgi i).continuous n)) 1
  simp_rw [sa16t_divFun_eq (hsm _) hψ x]
  refine tendsto_finset_sum _ fun i _ => ?_
  have h1 : Tendsto (fun n => HRS.MS.UniqT3.D1 i (sa16t_bcv d n b i) x) atTop (𝓝 (HRS.MS.UniqT3.D1 i (fun y => b y i) x)) := by
    simp only [sa16t_D1_eq_pd]
    exact sa16t_pd1_tendsto (hgi i) i x
  exact (h1.const_mul _).add ((sa16t_bc_tendsto (hgi i).continuous x).mul_const _)

theorem sa16t_div_bound {bc : Fin d → Euc d → ℝ} (hb : ∀ i, ContDiff ℝ 1 (bc i)) {B1 Cb : ℝ}
    (hB1 : ∀ i j y, |HRS.MS.UniqT3.D1 j (bc i) y| ≤ B1) (hCb : ∀ i y, |bc i y| ≤ Cb) {ψ : Euc d → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (x : Euc d) :
    |sa16so_divFun bc ψ x| ≤ (d : ℝ) * (B1 * |ψ x| + Cb * ‖fderiv ℝ ψ x‖) := by
  rw [sa16t_divFun_eq hb hψ x]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i : Fin d, |ψ x * HRS.MS.UniqT3.D1 i (bc i) x + bc i x * HRS.MS.UniqT3.D1 i ψ x|
      ≤ ∑ i : Fin d, (B1 * |ψ x| + Cb * ‖fderiv ℝ ψ x‖) := by
        refine Finset.sum_le_sum fun i _ => (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul]
        have h1 := hB1 i i x
        have h2 := (HRS.MS.UniqN2b.n2b_D1_le i ψ x)
        have h0 : 0 ≤ B1 := (abs_nonneg _).trans h1
        have h0' : 0 ≤ Cb := (abs_nonneg _).trans (hCb i x)
        nlinarith [mul_le_mul_of_nonneg_left h1 (abs_nonneg (ψ x)), mul_le_mul (hCb i x) h2 (abs_nonneg _) h0',
          abs_nonneg (ψ x)]
    _ = _ := by simp [Finset.sum_const, Finset.card_univ]; ring

theorem sa16t_div_vanish {bc : Fin d → Euc d → ℝ} (hb : ∀ i, ContDiff ℝ 1 (bc i)) {ψ : Euc d → ℝ}
    (hψ : ContDiff ℝ 1 ψ) {x : Euc d} (hx : x ∉ tsupport ψ) : sa16so_divFun bc ψ x = 0 := by
  unfold sa16so_divFun
  refine Finset.sum_eq_zero fun i _ => ?_
  have h1 : fderiv ℝ (fun y => bc i y * ψ y) x = 0 := by
    by_contra hne
    exact hx (tsupport_mul_subset_right (support_fderiv_subset ℝ hne))
  rw [h1]; rfl

end Lm3

end HRS.Whole.AppendixA.Phase2SA16R
