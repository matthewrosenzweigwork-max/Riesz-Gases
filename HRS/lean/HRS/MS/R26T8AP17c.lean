import HRS.MS.R26T8AP17b
import HRS.MS.R26T8AP06d10

/-!
# S8.2 local Newton layer, packet T8A.P17 (part c): the gradient difference `G(Y,w) = ∇f(Y + w/2) - ∇f(Y - w/2)`
For `TestBound k A f`: `r26t8a_p17_G_bound`: `‖nest p q G X z‖ <= 2 A` (`p + q + 1 <= k`) and
`r26t8a_p17_G_gain`: `‖nest p 0 G X z‖ <= A |z|` (`p + 2 <= k`), the mean value gain of one relative power.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff
open HRS HRS.Whole HRS.MS.Phase2S82

namespace HRS.MS.R26T8A

variable {d : ℕ}

/-- `G(Y,w) = ∇f(Y + w/2) - ∇f(Y - w/2)`. -/
def r26t8a_p17_G (f : Euc d → ℝ) (Yw : Euc d × Euc d) : Euc d :=
  gradient f (Yw.1 + (1 / 2 : ℝ) • Yw.2) - gradient f (Yw.1 + (-(1 / 2 : ℝ)) • Yw.2)

theorem r26t8a_p17_grad_jets {f : Euc d → ℝ} (n : ℕ) (x : Euc d) :
    ‖iteratedFDeriv ℝ n (gradient f) x‖ = ‖iteratedFDeriv ℝ (n + 1) f x‖ := by
  have h : gradient f = (InnerProductSpace.toDual ℝ (Euc d)).symm ∘ fderiv ℝ f := rfl
  rw [h, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left, norm_iteratedFDeriv_fderiv]

theorem r26t8a_p17_grad_contDiff {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (gradient f) := by
  have h : gradient f = (InnerProductSpace.toDual ℝ (Euc d)).symm ∘ fderiv ℝ f := rfl
  rw [h]
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.contDiff.comp (hf.fderiv_right (by simp))

theorem r26t8a_p17_D_le {k : ℕ} {A : ℝ} {f : Euc d → ℝ} (hf : TestBound k A f) (n : ℕ) (hn : n + 1 ≤ k) (x : Euc d) :
    ‖iteratedFDeriv ℝ n (gradient f) x‖ ≤ A := by
  rw [r26t8a_p17_grad_jets]
  exact hf.2 (n + 1) (by omega) hn x

theorem r26t8a_p17_G_bound {k : ℕ} {A : ℝ} {f : Euc d → ℝ} (hf : TestBound k A f) (p q : ℕ) (hpq : p + q + 1 ≤ k)
    (X z : Euc d) : ‖r26t8a_nest p q (r26t8a_p17_G f) X z‖ ≤ 2 * A := by
  have hg := r26t8a_p17_grad_contDiff hf.1
  have hgp : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (gradient f) := contDiff_infty.1 hg (p + q)
  have hl : ∀ a : ℝ, ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (fun Yw : Euc d × Euc d => gradient f (Yw.1 + a • Yw.2)) :=
    fun a => hgp.comp (contDiff_fst.add (contDiff_snd.const_smul a))
  have hD := r26t8a_p17_D_le hf (p + q) (by omega)
  have hA : 0 ≤ A := (norm_nonneg _).trans (hf.2 1 le_rfl (by omega) 0)
  have e : r26t8a_nest p q (r26t8a_p17_G f) X z =
      r26t8a_nest p q (fun Yw : Euc d × Euc d => gradient f (Yw.1 + (1 / 2 : ℝ) • Yw.2)) X z -
        r26t8a_nest p q (fun Yw : Euc d × Euc d => gradient f (Yw.1 + (-(1 / 2 : ℝ)) • Yw.2)) X z :=
    r26t8a_nest_sub p q z X (hl (1 / 2)) (hl (-(1 / 2)))
  rw [e]
  have h1 := r26t8a_p17_nest_affine (1 / 2 : ℝ) q p (gradient f) X z hgp
  have h2 := r26t8a_p17_nest_affine (-(1 / 2 : ℝ)) q p (gradient f) X z hgp
  have hq1 : (1 / 2 : ℝ) ^ q ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have c1 : |(1 / 2 : ℝ)| ^ q * ‖iteratedFDeriv ℝ (p + q) (gradient f) (X + (1 / 2 : ℝ) • z)‖ ≤ A := by
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    calc _ ≤ 1 * A := mul_le_mul hq1 (hD _) (norm_nonneg _) zero_le_one
      _ = A := one_mul _
  have c2 : |(-(1 / 2 : ℝ))| ^ q * ‖iteratedFDeriv ℝ (p + q) (gradient f) (X + (-(1 / 2 : ℝ)) • z)‖ ≤ A := by
    rw [abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    calc _ ≤ 1 * A := mul_le_mul hq1 (hD _) (norm_nonneg _) zero_le_one
      _ = A := one_mul _
  calc _ ≤ ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => gradient f (Yw.1 + (1 / 2 : ℝ) • Yw.2)) X z‖ +
        ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => gradient f (Yw.1 + (-(1 / 2 : ℝ)) • Yw.2)) X z‖ := norm_sub_le _ _
    _ ≤ 2 * A := by linarith

theorem r26t8a_p17_G_gain {k : ℕ} {A : ℝ} {f : Euc d → ℝ} (hf : TestBound k A f) (p : ℕ) (hp : p + 2 ≤ k)
    (X z : Euc d) : ‖r26t8a_nest p 0 (r26t8a_p17_G f) X z‖ ≤ A * ‖z‖ := by
  have hg := r26t8a_p17_grad_contDiff hf.1
  have hgp : ContDiff ℝ (p : WithTop ℕ∞) (gradient f) := contDiff_infty.1 hg p
  rw [r26t8a_nest_zero]
  have hfun : (fun Y : Euc d => r26t8a_p17_G f (Y, z)) =
      fun Y => gradient f (Y + (1 / 2 : ℝ) • z) - gradient f (Y + (-(1 / 2 : ℝ)) • z) := rfl
  rw [hfun]
  have c1 : ContDiffAt ℝ (p : WithTop ℕ∞) (fun Y : Euc d => gradient f (Y + (1 / 2 : ℝ) • z)) X :=
    (hgp.comp (contDiff_id.add contDiff_const)).contDiffAt
  have c2 : ContDiffAt ℝ (p : WithTop ℕ∞) (fun Y : Euc d => gradient f (Y + (-(1 / 2 : ℝ)) • z)) X :=
    (hgp.comp (contDiff_id.add contDiff_const)).contDiffAt
  rw [fun_iteratedFDeriv_sub_apply c1 c2, iteratedFDeriv_comp_add_right, iteratedFDeriv_comp_add_right]
  have hdiff : ∀ x ∈ (Set.univ : Set (Euc d)), DifferentiableAt ℝ (iteratedFDeriv ℝ p (gradient f)) x := fun x _ =>
    ((r26t8a_p17_grad_contDiff hf.1).differentiable_iteratedFDeriv (m := p) (by exact_mod_cast ENat.coe_lt_top p) x)
  have hbd : ∀ x ∈ (Set.univ : Set (Euc d)), ‖fderiv ℝ (iteratedFDeriv ℝ p (gradient f)) x‖ ≤ A := fun x _ => by
    rw [norm_fderiv_iteratedFDeriv]
    exact r26t8a_p17_D_le hf (p + 1) (by omega) x
  have := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbd convex_univ (Set.mem_univ (X + (-(1 / 2 : ℝ)) • z))
    (Set.mem_univ (X + (1 / 2 : ℝ) • z))
  have e : X + (1 / 2 : ℝ) • z - (X + (-(1 / 2 : ℝ)) • z) = z := by module
  rw [e] at this
  exact this

end HRS.MS.R26T8A
