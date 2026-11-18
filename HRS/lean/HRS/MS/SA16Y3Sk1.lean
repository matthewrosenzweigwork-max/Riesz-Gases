import HRS.MS.SA16ZR1
import HRS.MH.AdjointRdDefs
import HRS.MS.SA16Y3Lin1

/-!
# S.A.16 (SA16Y3) Sk1: the skew nonlocal operator `P^A_a ψ = ∑_{ij} A_{ji} ∂_i(g ⋆ (a ∂_jψ))` (packet P7, Hilbert corner)

`sa16y3_Q s i f = ∂_i (g ⋆ f)`; `sa16y3_PA`; `eucNonlocal s (-(λ•1) + A) a ψ = -λ P_a ψ + P^A_a ψ`.
`sa16y3_Q_deriv`: `∂_l Q^i f = Q^i ∂_l f` (`f ∈ C_c^∞`).
`sa16y3_PA_skew`: for `A^T = -A`: `P^A_a ψ = -∑_{ij} A_{ji} Q^i((∂_j a) ψ)` (symmetry of `∂_i∂_j (g ⋆ (aψ))`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.MH.AdjointRd

section Sk1
variable {d : ℕ} {s : ℝ}

/-- `Q^i f = ∂_i (g ⋆ f)` -/
def sa16y3_Q (s : ℝ) (i : Fin d) (f : Euc d → ℝ) (x : Euc d) : ℝ :=
  fderiv ℝ (convFun (rieszKernel d s) f) x (sa16z_e i)

/-- `P^A_a ψ = ∑_{ij} A_{ji} ∂_i (g ⋆ (a ∂_jψ))` -/
def sa16y3_PA (s : ℝ) (A : Matrix (Fin d) (Fin d) ℝ) (a ψ : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d, A j i * sa16y3_Q s i (sa16z_src a ψ j) x

lemma sa16y3_eucNonlocal_eq (M : Matrix (Fin d) (Fin d) ℝ) (a ψ : Euc d → ℝ) :
    eucNonlocal s M a ψ = fun x => ∑ i : Fin d, ∑ j : Fin d, M j i * sa16y3_Q s i (sa16z_src a ψ j) x := rfl

lemma sa16y3_eucNonlocal_split (lam : ℝ) (A : Matrix (Fin d) (Fin d) ℝ) (a ψ : Euc d → ℝ) (x : Euc d) :
    eucNonlocal s (-(lam • (1 : Matrix (Fin d) (Fin d) ℝ)) + A) a ψ x =
      -(lam * sa16z_P s a ψ x) + sa16y3_PA s A a ψ x := by
  rw [sa16y3_eucNonlocal_eq]
  simp only [sa16y3_PA, sa16z_P, sa16y3_Q, Matrix.add_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.one_apply,
    smul_eq_mul, add_mul, Finset.sum_add_distrib]
  congr 1
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [ite_mul, Finset.sum_ite_eq, sa16z_src]

lemma sa16y3_Q_add (hs0 : 0 ≤ s) (hsd : s < d) {f g : Euc d → ℝ} (hf : IsCcInfty f) (hg : IsCcInfty g) (i : Fin d)
    (x : Euc d) : sa16y3_Q s i (f + g) x = sa16y3_Q s i f x + sa16y3_Q s i g x := by
  unfold sa16y3_Q
  have h := sa16z_conv_add hs0 hsd hf hg
  have h' : convFun (rieszKernel d s) (f + g) = fun x => convFun (rieszKernel d s) f x + convFun (rieszKernel d s) g x := h
  rw [h', fderiv_fun_add ((sa16z_conv_smooth hs0 hsd hf).differentiable (by simp) x)
    ((sa16z_conv_smooth hs0 hsd hg).differentiable (by simp) x)]
  rfl

lemma sa16y3_Q_deriv (hs0 : 0 ≤ s) (hsd : s < d) {f : Euc d → ℝ} (hf : IsCcInfty f) (i l : Fin d) (x : Euc d) :
    fderiv ℝ (sa16y3_Q s i f) x (sa16z_e l) = sa16y3_Q s i (sa16z_dm f l) x := by
  unfold sa16y3_Q
  have hsm := sa16z_conv_smooth hs0 hsd hf
  rw [sa16sy_symm hsm (sa16z_e i) (sa16z_e l) x]
  have : (fun y => fderiv ℝ (convFun (rieszKernel d s) f) y (sa16z_e l)) =
      convFun (rieszKernel d s) (sa16z_dm f l) := by
    funext y; exact sa16z_conv_fderiv hs0 hsd hf _ y
  rw [this]

lemma sa16y3_dm_mul_cc {a ψ : Euc d → ℝ} (ha : ContDiff ℝ ∞ a) (hψ : IsCcInfty ψ) (j : Fin d) :
    IsCcInfty (fun y => sa16z_dm a j y * ψ y) :=
  ⟨(sa16z_dm_smooth ha j).mul hψ.1, hψ.2.mul_left⟩

theorem sa16y3_PA_skew (hs0 : 0 ≤ s) (hsd : s < d) {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.transpose = -A)
    {a ψ : Euc d → ℝ} (ha : ContDiff ℝ ∞ a) (hψ : IsCcInfty ψ) (x : Euc d) :
    sa16y3_PA s A a ψ x = -∑ i : Fin d, ∑ j : Fin d, A j i * sa16y3_Q s i (fun y => sa16z_dm a j y * ψ y) x := by
  have hAij : ∀ i j, A i j = -A j i := fun i j => by
    have := congrFun (congrFun hA j) i
    simpa [Matrix.transpose_apply] using this
  -- `∂_j (aψ) = a ∂_jψ + ∂_j a ψ`
  set h : Euc d → ℝ := fun y => a y * ψ y with hh
  have hhc : IsCcInfty h := ⟨ha.mul hψ.1, hψ.2.mul_left⟩
  have hsplit : ∀ j : Fin d, sa16z_dm h j = sa16z_src a ψ j + fun y => sa16z_dm a j y * ψ y := by
    intro j; funext y
    have hd1 : DifferentiableAt ℝ a y := (ha.differentiable (by simp)) y
    have hd2 : DifferentiableAt ℝ ψ y := (hψ.1.differentiable (by simp)) y
    simp only [sa16z_dm, hh, Pi.add_apply, sa16z_src]
    rw [fderiv_fun_mul hd1 hd2]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  -- symmetric second derivative
  set H : Fin d → Fin d → ℝ := fun i j => sa16y3_Q s i (sa16z_dm h j) x with hH
  have hsym : ∀ i j, H i j = H j i := by
    intro i j
    have e : ∀ i j, H i j = fderiv ℝ (fun y => fderiv ℝ (convFun (rieszKernel d s) h) y (sa16z_e j)) x
        (sa16z_e i) := by
      intro i j
      simp only [hH, sa16y3_Q]
      congr 2
      funext y
      exact (sa16z_conv_fderiv hs0 hsd hhc _ y).symm
    rw [e i j, e j i, sa16sy_symm (sa16z_conv_smooth hs0 hsd hhc) (sa16z_e j) (sa16z_e i) x]
  have hzero : ∑ i : Fin d, ∑ j : Fin d, A j i * H i j = 0 := by
    have h1 : ∑ i : Fin d, ∑ j : Fin d, A j i * H i j = ∑ i : Fin d, ∑ j : Fin d, A i j * H j i := by
      rw [Finset.sum_comm]
    have h2 : ∑ i : Fin d, ∑ j : Fin d, A i j * H j i = -∑ i : Fin d, ∑ j : Fin d, A j i * H i j := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hAij i j, hsym j i]; ring
    linarith
  have hsum : ∑ i : Fin d, ∑ j : Fin d, A j i * H i j =
      ∑ i : Fin d, ∑ j : Fin d, A j i * sa16y3_Q s i (sa16z_src a ψ j) x +
        ∑ i : Fin d, ∑ j : Fin d, A j i * sa16y3_Q s i (fun y => sa16z_dm a j y * ψ y) x := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hH, hsplit j]
    rw [sa16y3_Q_add hs0 hsd (sa16z_src_cc ha hψ j) (sa16y3_dm_mul_cc ha hψ j) i x]
    ring
  unfold sa16y3_PA
  linarith

end Sk1

end HRS.Whole.AppendixA.Phase2SA16R
