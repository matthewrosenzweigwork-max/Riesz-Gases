/-
# HRS.Equilibrium.PairMomentsGrad -- the configuration gradient of `F_N(ψ)` (EQ-01b)
-/
import HRS.Equilibrium.PairMomentsBase

open MeasureTheory ProbabilityTheory Filter Topology Function
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.PairMom

open HRS HRS.External HRS.Quad

variable {d : ℕ} {s : ℝ}

section Grad

theorem measurable_rep (d : ℕ) : Measurable (Torus.rep : Torus d → Euc d) := by
  have h : Measurable (fun (x : Torus d) (i : Fin d) =>
      ((AddCircle.equivIco (1 : ℝ) 0 (x i) : Set.Ico (0 : ℝ) (0 + 1)) : ℝ)) :=
    measurable_pi_iff.2 fun i => measurable_subtype_coe.comp
      ((AddCircle.measurableEquivIco (1 : ℝ) 0).measurable.comp (measurable_pi_apply i))
  exact (WithLp.measurable_toLp 2 _).comp h

theorem mk_add' (a b : Euc d) : Torus.mk (a + b) = Torus.mk a + Torus.mk b := by
  funext i
  simp [Torus.mk]

/-- The `m`-th component of the gradient in the first variable of the lifted kernel. -/
def gradK (ψ : Torus d → Torus d → ℝ) (m : Fin d) (x y : Torus d) : ℝ :=
  fderiv ℝ (lift2 ψ) (Torus.rep x, Torus.rep y) (EuclideanSpace.single m 1, 0)

theorem measurable_gradK (ψ : Torus d → Torus d → ℝ) (m : Fin d) :
    Measurable (Function.uncurry (gradK ψ m)) := by
  have h1 : Measurable fun p : Euc d × Euc d => fderiv ℝ (lift2 ψ) p (EuclideanSpace.single m 1, 0) :=
    measurable_fderiv_apply_const ℝ (lift2 ψ) _
  have h2 : Measurable fun p : Torus d × Torus d => (Torus.rep p.1, Torus.rep p.2) :=
    ((measurable_rep d).comp measurable_fst).prodMk ((measurable_rep d).comp measurable_snd)
  exact h1.comp h2

theorem isOpen_offDiag (d : ℕ) : IsOpen (offDiag d) := by
  have hc : Continuous fun p : Euc d × Euc d => (Torus.mk p.1, Torus.mk p.2) := by
    have := (Torus.continuous_mk (d := d))
    exact (this.comp continuous_fst).prodMk (this.comp continuous_snd)
  have ho : IsOpen {q : Torus d × Torus d | q.1 ≠ q.2} := isOpen_ne_fun continuous_fst continuous_snd
  exact ho.preimage hc

theorem differentiableAt_lift2 {ψ : Torus d → Torus d → ℝ}
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d)) {p : Euc d × Euc d}
    (hp : p ∈ offDiag d) : DifferentiableAt ℝ (lift2 ψ) p :=
  ((hsm.contDiffAt ((isOpen_offDiag d).mem_nhds hp)).differentiableAt (by simp))

end Grad

section GradForm

theorem lift2_shift {ψ : Torus d → Torus d → ℝ} (x y : Torus d) (u : Euc d) :
    lift2 ψ (Torus.rep x + u, Torus.rep y) = ψ (x + Torus.mk u) y := by
  unfold lift2
  simp only [mk_add', Torus.mk_rep]

theorem hasFDerivAt_Fstat {ψ : Torus d → Torus d → ℝ} (hsymm : ∀ x y, ψ x y = ψ y x)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d)) {N : ℕ} (X : Config d N)
    (hX : ∀ a b : Fin N, a ≠ b → X a ≠ X b) (i : Fin N) :
    HasFDerivAt (fun u : Euc d => Fstat ψ (Function.update X i (X i + Torus.mk u)))
      (((N : ℝ) ^ (-(3 / 2 : ℝ)) * 2) • ∑ j ∈ Finset.univ.erase i,
        (fderiv ℝ (lift2 ψ) (Torus.rep (X i), Torus.rep (X j))).comp
          ((ContinuousLinearMap.id ℝ (Euc d)).prod (0 : Euc d →L[ℝ] Euc d))) 0 := by
  have key : (fun u : Euc d => Fstat ψ (Function.update X i (X i + Torus.mk u))) =
      fun u => (N : ℝ) ^ (-(3 / 2 : ℝ)) * (2 * ∑ j ∈ Finset.univ.erase i,
        lift2 ψ (Torus.rep (X i) + u, Torus.rep (X j)) + pairRest ψ i X) := by
    funext u
    unfold Fstat
    rw [pairSum_update ψ hsymm i X (X i + Torus.mk u)]
    congr 3
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [lift2_shift]
  rw [key]
  have hj : ∀ j ∈ Finset.univ.erase i, HasFDerivAt (fun u : Euc d => lift2 ψ (Torus.rep (X i) + u, Torus.rep (X j)))
      ((fderiv ℝ (lift2 ψ) (Torus.rep (X i), Torus.rep (X j))).comp
        ((ContinuousLinearMap.id ℝ (Euc d)).prod (0 : Euc d →L[ℝ] Euc d))) 0 := by
    intro j hj
    have hne : X i ≠ X j := hX i j (Finset.ne_of_mem_erase hj).symm
    have hp : (Torus.rep (X i), Torus.rep (X j)) ∈ offDiag d := by
      show Torus.mk (Torus.rep (X i)) ≠ Torus.mk (Torus.rep (X j))
      rw [Torus.mk_rep, Torus.mk_rep]; exact hne
    have hd := (differentiableAt_lift2 hsm hp).hasFDerivAt
    have hin : HasFDerivAt (fun u : Euc d => (Torus.rep (X i) + u, Torus.rep (X j)))
        ((ContinuousLinearMap.id ℝ (Euc d)).prod (0 : Euc d →L[ℝ] Euc d)) 0 :=
      ((hasFDerivAt_id (0 : Euc d)).const_add (Torus.rep (X i))).prodMk (hasFDerivAt_const _ _)
    have hd' : HasFDerivAt (lift2 ψ) (fderiv ℝ (lift2 ψ) (Torus.rep (X i), Torus.rep (X j)))
        (Torus.rep (X i) + 0, Torus.rep (X j)) := by simpa using hd
    exact hd'.comp (0 : Euc d) hin
  have hsum := HasFDerivAt.fun_sum hj
  have h2 := (hsum.const_mul 2).add_const (pairRest ψ i X)
  have h3 := h2.const_mul ((N : ℝ) ^ (-(3 / 2 : ℝ)))
  convert h3 using 1
  rw [smul_smul]

end GradForm

section GradNorm

theorem configGrad_norm_sq {ψ : Torus d → Torus d → ℝ} (hsymm : ∀ x y, ψ x y = ψ y x)
    (hsm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (lift2 ψ) (offDiag d)) {N : ℕ} (X : Config d N)
    (hX : ∀ a b : Fin N, a ≠ b → X a ≠ X b) (i : Fin N) :
    ‖configGrad (Fstat ψ) X i‖ₑ ^ 2 = ∑ m : Fin d, ENNReal.ofReal
      (((N : ℝ) ^ (-(3 / 2 : ℝ)) * 2 * ∑ j ∈ Finset.univ.erase i, gradK ψ m (X i) (X j)) ^ 2) := by
  have hd := hasFDerivAt_Fstat hsymm hsm X hX i
  have hf : fderiv ℝ (fun u : Euc d => Fstat ψ (Function.update X i (X i + Torus.mk u))) 0 = _ := hd.fderiv
  have hcomp : ∀ m : Fin d, (configGrad (Fstat ψ) X i) m =
      (N : ℝ) ^ (-(3 / 2 : ℝ)) * 2 * ∑ j ∈ Finset.univ.erase i, gradK ψ m (X i) (X j) := by
    intro m
    have h1 : (InnerProductSpace.toDual ℝ (Euc d) (configGrad (Fstat ψ) X i)) (EuclideanSpace.single m (1 : ℝ)) =
        inner ℝ (configGrad (Fstat ψ) X i) (EuclideanSpace.single m (1 : ℝ)) := InnerProductSpace.toDual_apply_apply
    have h2 : (InnerProductSpace.toDual ℝ (Euc d)) (configGrad (Fstat ψ) X i) =
        fderiv ℝ (fun u : Euc d => Fstat ψ (Function.update X i (X i + Torus.mk u))) 0 := by
      unfold configGrad
      simp
    rw [h2, hf] at h1
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply] at h1
    rw [EuclideanSpace.inner_single_right] at h1
    simp only [one_mul, conj_trivial] at h1
    rw [← h1]
    simp only [smul_eq_mul, gradK]
  have e1 : ‖configGrad (Fstat ψ) X i‖ₑ ^ 2 = ENNReal.ofReal (‖configGrad (Fstat ψ) X i‖ ^ 2) := by
    rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_pow (norm_nonneg _)]
  rw [e1, EuclideanSpace.norm_sq_eq, ENNReal.ofReal_sum_of_nonneg (fun m _ => by positivity)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [hcomp m, Real.norm_eq_abs, sq_abs]

end GradNorm

end HRS.PairMom

end
