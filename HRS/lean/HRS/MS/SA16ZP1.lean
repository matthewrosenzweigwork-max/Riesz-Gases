import HRS.MS.SA16ZEn1
import HRS.MS.S16FracAux3

/-!
# S.A.16 (SA16Z) P1: the isotropic nonlocal operator `P_a ψ = ∑_i ∂_i (g ⋆ (a ∂_i ψ))` on `C_c^∞` (packet P7, iso case)

`sa16z_P s a ψ`; for `a` smooth and `ψ ∈ C_c^∞`: `P_a ψ` is smooth (`sa16z_P_smooth`) and
`∂_l (P_a ψ) = P_{∂_l a} ψ + P_a (∂_l ψ)` (`sa16z_P_deriv`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff Convolution

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section P1
variable {d : ℕ}

/-- the coordinate vector `e_i` -/
abbrev sa16z_e (i : Fin d) : Euc d := EuclideanSpace.single i (1 : ℝ)

/-- the source `a ∂_i ψ` -/
def sa16z_src (a ψ : Euc d → ℝ) (i : Fin d) : Euc d → ℝ := fun y => a y * fderiv ℝ ψ y (sa16z_e i)

/-- `P_a ψ = ∑_i ∂_i (g ⋆ (a ∂_i ψ))` (this is `eucNonlocal s 1 a ψ`) -/
def sa16z_P (s : ℝ) (a ψ : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∑ i : Fin d, fderiv ℝ (convFun (rieszKernel d s) (sa16z_src a ψ i)) x (sa16z_e i)

lemma sa16z_src_cc {a ψ : Euc d → ℝ} (ha : ContDiff ℝ ∞ a) (hψ : IsCcInfty ψ) (i : Fin d) :
    IsCcInfty (sa16z_src a ψ i) :=
  ⟨ha.mul (sa16s_cc_fderiv hψ _).1, (sa16s_cc_fderiv hψ _).2.mul_left⟩

lemma sa16z_conv_smooth {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {f : Euc d → ℝ} (hf : IsCcInfty f) :
    ContDiff ℝ ∞ (convFun (rieszKernel d s) f) := by
  rw [sa16sp_convFun_eq_conv]
  exact hf.2.contDiff_convolution_right (ContinuousLinearMap.lsmul ℝ ℝ)
    (rieszKernel_locallyIntegrable hs0 hsd) hf.1

lemma sa16z_conv_add {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {f g : Euc d → ℝ} (hf : IsCcInfty f)
    (hg : IsCcInfty g) :
    convFun (rieszKernel d s) (fun y => f y + g y) = fun x =>
      convFun (rieszKernel d s) f x + convFun (rieszKernel d s) g x := by
  funext x
  rw [sa16sp_convFun_eq_conv, sa16sp_convFun_eq_conv, sa16sp_convFun_eq_conv]
  have hκ := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  have h1 := hf.2.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ) hκ hf.1.continuous
  have h2 := hg.2.convolutionExists_right (ContinuousLinearMap.lsmul ℝ ℝ) hκ hg.1.continuous
  exact (h1 x).distrib_add (h2 x)

lemma sa16z_P_smooth {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a ψ : Euc d → ℝ} (ha : ContDiff ℝ ∞ a)
    (hψ : IsCcInfty ψ) : ContDiff ℝ ∞ (sa16z_P s a ψ) := by
  have h : sa16z_P s a ψ = fun x => ∑ i : Fin d,
      fderiv ℝ (convFun (rieszKernel d s) (sa16z_src a ψ i)) x (sa16z_e i) := rfl
  rw [h]
  exact ContDiff.sum fun i _ => sa16so_dir_smooth (sa16z_conv_smooth hs0 hsd (sa16z_src_cc ha hψ i)) _

lemma sa16z_conv_fderiv {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {f : Euc d → ℝ} (hf : IsCcInfty f) (v : Euc d)
    (x : Euc d) :
    fderiv ℝ (convFun (rieszKernel d s) f) x v = convFun (rieszKernel d s) (fun y => fderiv ℝ f y v) x :=
  (sa16sp_convFun_fderiv (rieszKernel_locallyIntegrable hs0 hsd) (hf.1.of_le (by exact_mod_cast le_top))
    hf.2 x).2 v

lemma sa16z_P_deriv {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a ψ : Euc d → ℝ} (ha : ContDiff ℝ ∞ a)
    (hψ : IsCcInfty ψ) (l : Fin d) (x : Euc d) :
    fderiv ℝ (sa16z_P s a ψ) x (sa16z_e l) =
      sa16z_P s (fun y => fderiv ℝ a y (sa16z_e l)) ψ x +
        sa16z_P s a (fun y => fderiv ℝ ψ y (sa16z_e l)) x := by
  have hdl : IsCcInfty (fun y => fderiv ℝ ψ y (sa16z_e l)) := sa16s_cc_fderiv hψ _
  have hal : ContDiff ℝ ∞ (fun y => fderiv ℝ a y (sa16z_e l)) := sa16so_dir_smooth ha _
  -- derivative of each summand
  have hterm : ∀ i : Fin d, fderiv ℝ (fun x' => fderiv ℝ (convFun (rieszKernel d s) (sa16z_src a ψ i)) x'
        (sa16z_e i)) x (sa16z_e l) =
      fderiv ℝ (convFun (rieszKernel d s) (sa16z_src (fun y => fderiv ℝ a y (sa16z_e l)) ψ i)) x (sa16z_e i) +
        fderiv ℝ (convFun (rieszKernel d s) (sa16z_src a (fun y => fderiv ℝ ψ y (sa16z_e l)) i)) x (sa16z_e i) := by
    intro i
    have hsm := sa16z_conv_smooth hs0 hsd (sa16z_src_cc ha hψ i)
    rw [sa16sy_symm hsm (sa16z_e i) (sa16z_e l) x]
    have hfun : (fun y => fderiv ℝ (convFun (rieszKernel d s) (sa16z_src a ψ i)) y (sa16z_e l)) =
        fun y => convFun (rieszKernel d s) (sa16z_src (fun y => fderiv ℝ a y (sa16z_e l)) ψ i) y +
          convFun (rieszKernel d s) (sa16z_src a (fun y => fderiv ℝ ψ y (sa16z_e l)) i) y := by
      funext y
      rw [sa16z_conv_fderiv hs0 hsd (sa16z_src_cc ha hψ i)]
      have hsrc : (fun z => fderiv ℝ (sa16z_src a ψ i) z (sa16z_e l)) = fun z =>
          sa16z_src (fun y => fderiv ℝ a y (sa16z_e l)) ψ i z +
            sa16z_src a (fun y => fderiv ℝ ψ y (sa16z_e l)) i z := by
        funext z
        have hd1 : DifferentiableAt ℝ a z := (ha.differentiable (by simp)) z
        have hd2 : DifferentiableAt ℝ (fun y => fderiv ℝ ψ y (sa16z_e i)) z :=
          ((sa16so_dir_smooth hψ.1 (sa16z_e i)).differentiable (by simp)) z
        have : sa16z_src a ψ i = fun y => a y * fderiv ℝ ψ y (sa16z_e i) := rfl
        rw [this, fderiv_fun_mul hd1 hd2]
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, sa16z_src]
        rw [sa16sy_symm hψ.1 (sa16z_e i) (sa16z_e l) z]
        ring
      rw [hsrc]
      have := congrFun (sa16z_conv_add hs0 hsd (sa16z_src_cc hal hψ i) (sa16z_src_cc ha hdl i)) y
      exact this
    rw [hfun]
    have hA := sa16z_conv_smooth hs0 hsd (sa16z_src_cc hal hψ i)
    have hB := sa16z_conv_smooth hs0 hsd (sa16z_src_cc ha hdl i)
    rw [fderiv_fun_add (hA.differentiable (by simp) x) (hB.differentiable (by simp) x)]
    rfl
  have hP : sa16z_P s a ψ = fun x => ∑ i : Fin d,
      fderiv ℝ (convFun (rieszKernel d s) (sa16z_src a ψ i)) x (sa16z_e i) := rfl
  rw [hP, fderiv_fun_sum (fun i _ => ((sa16so_dir_smooth (sa16z_conv_smooth hs0 hsd (sa16z_src_cc ha hψ i))
    _).differentiable (by simp)) x)]
  simp only [ContinuousLinearMap.sum_apply]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  rfl

end P1

end HRS.Whole.AppendixA.Phase2SA16R
