import HRS.PDE.MovSpec1
import HRS.PDE.TorusFPCompareAux1
import HRS.PDE.MeanFieldSchauder
import HRS.PDE.MeanFieldOneLe
import HRS.PDE.MeanFieldPairing
import HRS.PDE.TorusFPAdapter
import HRS.PDE.TorusFPExistAux15

/-!
# MOVA Aux1: calculus on the torus (partial derivatives of sums/products/logs, gradient components)

Helpers for the packet MOV-A (`movT_srcReg_decomp`).  All names carry the prefix `mova_`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem mova_lift_add (f g : Torus d → ℝ) :
    Torus.lift (fun y => f y + g y) = fun y => Torus.lift f y + Torus.lift g y := rfl

theorem mova_isCk_of_le {k l : WithTop ℕ∞} (h : l ≤ k) {f : Torus d → ℝ} (hf : Torus.IsCk k f) :
    Torus.IsCk l f := ContDiff.of_le hf h

theorem mova_isCk_one_of_two {f : Torus d → ℝ} (hf : Torus.IsCk 2 f) : Torus.IsCk 1 f :=
  ContDiff.of_le hf (by norm_num)

theorem mova_isCk_add {k : WithTop ℕ∞} {f g : Torus d → ℝ} (hf : Torus.IsCk k f)
    (hg : Torus.IsCk k g) : Torus.IsCk k (fun y => f y + g y) := ContDiff.add hf hg

theorem mova_isCk_sub {k : WithTop ℕ∞} {f g : Torus d → ℝ} (hf : Torus.IsCk k f)
    (hg : Torus.IsCk k g) : Torus.IsCk k (fun y => f y - g y) := ContDiff.sub hf hg

theorem mova_isCk_mul {k : WithTop ℕ∞} {f g : Torus d → ℝ} (hf : Torus.IsCk k f)
    (hg : Torus.IsCk k g) : Torus.IsCk k (fun y => f y * g y) := ContDiff.mul hf hg

theorem mova_isCk_const_mul {k : WithTop ℕ∞} {f : Torus d → ℝ} (c : ℝ) (hf : Torus.IsCk k f) :
    Torus.IsCk k (fun y => c * f y) := ContDiff.mul contDiff_const hf

theorem mova_isCk_const (k : WithTop ℕ∞) (c : ℝ) : Torus.IsCk k (fun _ : Torus d => c) :=
  contDiff_const

theorem mova_isCk_log {k : WithTop ℕ∞} {f : Torus d → ℝ} (hf : Torus.IsCk k f)
    (hpos : ∀ x, 0 < f x) : Torus.IsCk k (fun y => Real.log (f y)) := by
  unfold Torus.IsCk Torus.lift at *
  exact hf.log (fun z => (hpos _).ne')

theorem mova_isCk_exp {k : WithTop ℕ∞} {f : Torus d → ℝ} (hf : Torus.IsCk k f) :
    Torus.IsCk k (fun y => Real.exp (f y)) := Real.contDiff_exp.comp hf

theorem mova_isCk_sum {k : WithTop ℕ∞} {ι : Type*} (s : Finset ι) {f : ι → Torus d → ℝ}
    (hf : ∀ i ∈ s, Torus.IsCk k (f i)) : Torus.IsCk k (fun y => ∑ i ∈ s, f i y) := by
  unfold Torus.IsCk at *
  exact ContDiff.sum hf

theorem mova_continuous_of_isCk {k : WithTop ℕ∞} {f : Torus d → ℝ} (hf : Torus.IsCk k f) :
    Continuous f := Torus.continuous_of_continuous_lift hf.continuous

theorem mova_isCk_partialDeriv {f : Torus d → ℝ} (hf : Torus.IsCk 2 f) (j : Fin d) :
    Torus.IsCk 1 (Torus.partialDeriv j f) := d1c_isCk1_partialDeriv hf j

theorem mova_continuous_partialDeriv {f : Torus d → ℝ} (hf : Torus.IsCk 1 f) (j : Fin d) :
    Continuous (Torus.partialDeriv j f) := PDE.continuous_partialDeriv j f hf

theorem mova_partialDeriv_add (j : Fin d) {f g : Torus d → ℝ} (hf : Torus.IsCk 1 f)
    (hg : Torus.IsCk 1 g) (x : Torus d) :
    Torus.partialDeriv j (fun y => f y + g y) x =
      Torus.partialDeriv j f x + Torus.partialDeriv j g x := by
  unfold Torus.partialDeriv
  rw [mova_lift_add, fderiv_fun_add ((hf.differentiable one_ne_zero) _)
    ((hg.differentiable one_ne_zero) _)]
  rfl

theorem mova_partialDeriv_neg (j : Fin d) {f : Torus d → ℝ} (x : Torus d) :
    Torus.partialDeriv j (fun y => -f y) x = -Torus.partialDeriv j f x := by
  unfold Torus.partialDeriv
  have e : Torus.lift (fun y => -f y) = fun y => -Torus.lift f y := rfl
  rw [e, fderiv_fun_neg]
  rfl

theorem mova_partialDeriv_sub (j : Fin d) {f g : Torus d → ℝ} (hf : Torus.IsCk 1 f)
    (hg : Torus.IsCk 1 g) (x : Torus d) :
    Torus.partialDeriv j (fun y => f y - g y) x =
      Torus.partialDeriv j f x - Torus.partialDeriv j g x := by
  unfold Torus.partialDeriv
  have e : Torus.lift (fun y => f y - g y) = fun y => Torus.lift f y - Torus.lift g y := rfl
  rw [e, fderiv_fun_sub ((hf.differentiable one_ne_zero) _) ((hg.differentiable one_ne_zero) _)]
  rfl

theorem mova_partialDeriv_const_mul (j : Fin d) {f : Torus d → ℝ} (hf : Torus.IsCk 1 f) (c : ℝ)
    (x : Torus d) :
    Torus.partialDeriv j (fun y => c * f y) x = c * Torus.partialDeriv j f x := by
  unfold Torus.partialDeriv
  have e : Torus.lift (fun y => c * f y) = fun y => c * Torus.lift f y := rfl
  rw [e, fderiv_const_mul ((hf.differentiable one_ne_zero) _)]
  simp

theorem mova_partialDeriv_mul (j : Fin d) {f g : Torus d → ℝ} (hf : Torus.IsCk 1 f)
    (hg : Torus.IsCk 1 g) (x : Torus d) :
    Torus.partialDeriv j (fun y => f y * g y) x =
      Torus.partialDeriv j f x * g x + f x * Torus.partialDeriv j g x := by
  have e1 : Torus.lift (fun y => f y * g y) = fun y => Torus.lift f y * Torus.lift g y := rfl
  unfold Torus.partialDeriv
  rw [e1, fderiv_fun_mul ((hf.differentiable one_ne_zero) _) ((hg.differentiable one_ne_zero) _)]
  simp [Torus.lift, Torus.mk_rep]
  ring

theorem mova_partialDeriv_sum (j : Fin d) {ι : Type*} (s : Finset ι) {f : ι → Torus d → ℝ}
    (hf : ∀ i ∈ s, Torus.IsCk 1 (f i)) (x : Torus d) :
    Torus.partialDeriv j (fun y => ∑ i ∈ s, f i y) x = ∑ i ∈ s, Torus.partialDeriv j (f i) x := by
  unfold Torus.partialDeriv
  have e : Torus.lift (fun y => ∑ i ∈ s, f i y) = fun y => ∑ i ∈ s, Torus.lift (f i) y := rfl
  rw [e, fderiv_fun_sum (fun i hi => (hf i hi).differentiable one_ne_zero _)]
  simp

theorem mova_partialDeriv_log (j : Fin d) {f : Torus d → ℝ} (hf : Torus.IsCk 1 f)
    (hpos : ∀ x, 0 < f x) (x : Torus d) :
    Torus.partialDeriv j (fun y => Real.log (f y)) x = Torus.partialDeriv j f x / f x := by
  have e : Torus.lift (fun y => Real.log (f y)) = fun y => Real.log (Torus.lift f y) := rfl
  unfold Torus.partialDeriv
  rw [e, fderiv.log ((hf.differentiable one_ne_zero) _) (hpos _).ne']
  simp [div_eq_inv_mul, Torus.lift, Torus.mk_rep]

theorem mova_partialDeriv_exp (j : Fin d) {f : Torus d → ℝ} (hf : Torus.IsCk 1 f) (x : Torus d) :
    Torus.partialDeriv j (fun y => Real.exp (f y)) x =
      Real.exp (f x) * Torus.partialDeriv j f x := by
  unfold Torus.partialDeriv
  have e : Torus.lift (fun y => Real.exp (f y)) = fun y => Real.exp (Torus.lift f y) := rfl
  rw [e, fderiv_exp ((hf.differentiable one_ne_zero) _)]
  simp [Torus.lift, Torus.mk_rep]

theorem mova_partialDeriv_const (j : Fin d) (c : ℝ) (x : Torus d) :
    Torus.partialDeriv j (fun _ => c) x = 0 := by
  unfold Torus.partialDeriv
  have : Torus.lift (fun _ : Torus d => c) = fun _ => c := rfl
  rw [this]
  simp

theorem mova_grad_apply (f : Torus d → ℝ) (x : Torus d) (j : Fin d) :
    (Torus.grad f x).ofLp j = Torus.partialDeriv j f x := d1c_grad_component x j

theorem mova_inner_eq_sum (u v : Euc d) : inner ℝ u v = ∑ j, u.ofLp j * v.ofLp j := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [mul_comm]

theorem mova_norm_sq_eq_sum (u : Euc d) : ‖u‖ ^ 2 = ∑ j, u.ofLp j ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)]
  simp

theorem mova_norm_le_sum (v : Euc d) : ‖v‖ ≤ ∑ j, |v.ofLp j| := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_iff.mpr ⟨Finset.sum_nonneg fun j _ => abs_nonneg _, ?_⟩
  calc ∑ j, ‖v.ofLp j‖ ^ 2 = ∑ j, |v.ofLp j| ^ 2 := by simp
    _ ≤ (∑ j, |v.ofLp j|) ^ 2 := Finset.sum_sq_le_sq_sum_of_nonneg fun j _ => abs_nonneg _

theorem mova_laplacian_eq_sum {f : Torus d → ℝ} (hf : Torus.IsCk 2 f) (x : Torus d) :
    Torus.laplacian f x = ∑ j, Torus.partialDeriv j (Torus.partialDeriv j f) x :=
  PDE.laplacian_eq_sum f hf x

end HRS
