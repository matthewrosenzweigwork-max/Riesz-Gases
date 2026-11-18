import HRS.Main.A8PAux11

/-!
# Packet A8P, part 12: the covariance integrand `⟨∇f,∇g⟩`: Lipschitz bound and the coercivity test
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

variable {d : ℕ}

theorem a8p_partialDeriv_eq_dirTor (f : Torus d → ℝ) (j : Fin d) :
    Torus.partialDeriv j f = KernelGrad.dirTor f (EuclideanSpace.single j (1 : ℝ)) := by
  funext x
  rw [← gfb2_inner_grad_eq_dirTor f _ x, ← a8p_grad_apply f x j]
  simp [EuclideanSpace.inner_single_right]

theorem a8p_prodgrad_lip {f g : Torus d → ℝ} (hf : Torus.IsCk 2 f) (hg : Torus.IsCk 2 g) :
    KernelGrad.IsLipschitz (2 * d * Torus.cbNorm 2 f * Torus.cbNorm 2 g)
      (fun x => inner ℝ (Torus.grad f x) (Torus.grad g x)) := by
  intro x y
  have hbf := gfb2_cbNorm_nonneg f 2
  have hbg := gfb2_cbNorm_nonneg g 2
  have htd : 0 ≤ KernelGrad.tdist x y := by unfold KernelGrad.tdist; exact norm_nonneg _
  have hLf : ∀ j : Fin d, |Torus.partialDeriv j f x - Torus.partialDeriv j f y| ≤
      Torus.cbNorm 2 f * KernelGrad.tdist x y := by
    intro j
    have := gfb2_dirTor_lipschitz hf (EuclideanSpace.single j (1 : ℝ)) x y
    rw [a8p_partialDeriv_eq_dirTor]
    simpa using this
  have hLg : ∀ j : Fin d, |Torus.partialDeriv j g x - Torus.partialDeriv j g y| ≤
      Torus.cbNorm 2 g * KernelGrad.tdist x y := by
    intro j
    have := gfb2_dirTor_lipschitz hg (EuclideanSpace.single j (1 : ℝ)) x y
    rw [a8p_partialDeriv_eq_dirTor]
    simpa using this
  have hbf' : ∀ j z, |Torus.partialDeriv j f z| ≤ Torus.cbNorm 2 f := fun j z =>
    HRS.PDE.MFPair.abs_partialDeriv_le (L := 2) (by norm_num) hf j z
  have hbg' : ∀ j z, |Torus.partialDeriv j g z| ≤ Torus.cbNorm 2 g := fun j z =>
    HRS.PDE.MFPair.abs_partialDeriv_le (L := 2) (by norm_num) hg j z
  simp only [a8p_inner_grad]
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ j : Fin d, |Torus.partialDeriv j f x * Torus.partialDeriv j g x -
      Torus.partialDeriv j f y * Torus.partialDeriv j g y| ≤
      2 * Torus.cbNorm 2 f * Torus.cbNorm 2 g * KernelGrad.tdist x y := by
    intro j
    have e : Torus.partialDeriv j f x * Torus.partialDeriv j g x -
        Torus.partialDeriv j f y * Torus.partialDeriv j g y =
        Torus.partialDeriv j f x * (Torus.partialDeriv j g x - Torus.partialDeriv j g y) +
        Torus.partialDeriv j g y * (Torus.partialDeriv j f x - Torus.partialDeriv j f y) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul]
    have h1 : |Torus.partialDeriv j f x| * |Torus.partialDeriv j g x - Torus.partialDeriv j g y| ≤
        Torus.cbNorm 2 f * (Torus.cbNorm 2 g * KernelGrad.tdist x y) :=
      mul_le_mul (hbf' j x) (hLg j) (abs_nonneg _) hbf
    have h2 : |Torus.partialDeriv j g y| * |Torus.partialDeriv j f x - Torus.partialDeriv j f y| ≤
        Torus.cbNorm 2 g * (Torus.cbNorm 2 f * KernelGrad.tdist x y) :=
      mul_le_mul (hbg' j y) (hLf j) (abs_nonneg _) hbg
    nlinarith
  calc ∑ j : Fin d, |Torus.partialDeriv j f x * Torus.partialDeriv j g x -
        Torus.partialDeriv j f y * Torus.partialDeriv j g y|
      ≤ ∑ _j : Fin d, 2 * Torus.cbNorm 2 f * Torus.cbNorm 2 g * KernelGrad.tdist x y :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = _ := by simp [Finset.sum_const]; ring

end HRS.Main.A8P
