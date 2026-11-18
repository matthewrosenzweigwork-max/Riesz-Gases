import HRS.MS.R26T8AO03b10

/-!
# S8.2 T8A O03b (part 11): linearity of the particle generator on functions that are `C²` at a configuration
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d N : ℕ}

theorem r26t8a_o03b_upd_cda {G : EucConfig d N → ℝ} {X : EucConfig d N} (hG : ContDiffAt ℝ 2 G X) (i : Fin N) :
    ContDiffAt ℝ 2 (fun y : Euc d => G (Function.update X i y)) (X i) := by
  have hu : ContDiff ℝ 2 (fun y : Euc d => Function.update X i y) := contDiff_update 2 X i
  have hG' : ContDiffAt ℝ 2 G (Function.update X i (X i)) := by
    rw [Function.update_eq_self]; exact hG
  exact hG'.comp (X i) hu.contDiffAt

theorem r26t8a_o03b_pG_lin (D : WholeDyn d) {F G H : EucConfig d N → ℝ} {X : EucConfig d N}
    (hG : ContDiffAt ℝ 2 G X) (hH : ContDiffAt ℝ 2 H X) (c1 c2 : ℝ) (hF : F = c1 • G + c2 • H) :
    particleGenerator D F X = c1 * particleGenerator D G X + c2 * particleGenerator D H X := by
  have hfun : ∀ i : Fin N, (fun y : Euc d => F (Function.update X i y)) =
      c1 • (fun y : Euc d => G (Function.update X i y)) + c2 • (fun y : Euc d => H (Function.update X i y)) := by
    intro i; funext y; simp [hF]
  have hL : ∀ i : Fin N, Laplacian.laplacian (fun y : Euc d => F (Function.update X i y)) (X i) =
      c1 * Laplacian.laplacian (fun y : Euc d => G (Function.update X i y)) (X i) +
        c2 * Laplacian.laplacian (fun y : Euc d => H (Function.update X i y)) (X i) := by
    intro i
    have h1 : ContDiffAt ℝ 2 (c1 • fun y : Euc d => G (Function.update X i y)) (X i) :=
      (r26t8a_o03b_upd_cda hG i).const_smul c1
    have h2 : ContDiffAt ℝ 2 (c2 • fun y : Euc d => H (Function.update X i y)) (X i) :=
      (r26t8a_o03b_upd_cda hH i).const_smul c2
    rw [hfun i, ContDiffAt.laplacian_add h1 h2, InnerProductSpace.laplacian_smul c1 (r26t8a_o03b_upd_cda hG i),
      InnerProductSpace.laplacian_smul c2 (r26t8a_o03b_upd_cda hH i)]
    simp
  have hg : ∀ i : Fin N, Phase2S82.configGrad F X i = c1 • Phase2S82.configGrad G X i + c2 • Phase2S82.configGrad H X i := by
    intro i
    have h1 := r26t8a_o03b_upd_cda hG i
    have h2 := r26t8a_o03b_upd_cda hH i
    unfold Phase2S82.configGrad gradient
    rw [hfun i]
    have d1 : DifferentiableAt ℝ (fun y : Euc d => G (Function.update X i y)) (X i) :=
      h1.differentiableAt (by norm_num)
    have d2 : DifferentiableAt ℝ (fun y : Euc d => H (Function.update X i y)) (X i) :=
      h2.differentiableAt (by norm_num)
    have e : fderiv ℝ (c1 • (fun y : Euc d => G (Function.update X i y)) +
        c2 • (fun y : Euc d => H (Function.update X i y))) (X i) =
        c1 • fderiv ℝ (fun y : Euc d => G (Function.update X i y)) (X i) +
          c2 • fderiv ℝ (fun y : Euc d => H (Function.update X i y)) (X i) := by
      rw [fderiv_add (d1.const_smul c1) (d2.const_smul c2), fderiv_const_smul d1, fderiv_const_smul d2]
    rw [e, map_add, map_smul, map_smul]
  unfold particleGenerator
  simp only [hL, hg, inner_add_right, inner_smul_right, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end HRS.MS.R26T8A
