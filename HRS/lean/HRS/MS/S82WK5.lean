import HRS.MS.S82WK4

/-!
# S8.2 A04 (S82W), part 6: linearity and continuity of the generator and gradient off collisions
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82W
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82U

section lin
variable {d N : ℕ}

lemma w_fderiv_sub {φ ψ : EucConfig d N → ℝ} (hφ : ContDiffOn ℝ 2 φ (eucCollisionSet d N)ᶜ)
    (hψ : ContDiffOn ℝ 2 ψ (eucCollisionSet d N)ᶜ) {X : EucConfig d N} (hX : X ∉ eucCollisionSet d N) :
    fderiv ℝ (fun Y => φ Y - ψ Y) X = fderiv ℝ φ X - fderiv ℝ ψ X := by
  have h1 : DifferentiableAt ℝ φ X := (hφ.differentiableOn (by norm_num)).differentiableAt (u4_D_open.mem_nhds hX)
  have h2 : DifferentiableAt ℝ ψ X := (hψ.differentiableOn (by norm_num)).differentiableAt (u4_D_open.mem_nhds hX)
  exact fderiv_sub h1 h2

lemma w_fderiv2_sub {φ ψ : EucConfig d N → ℝ} (hφ : ContDiffOn ℝ 2 φ (eucCollisionSet d N)ᶜ)
    (hψ : ContDiffOn ℝ 2 ψ (eucCollisionSet d N)ᶜ) {X : EucConfig d N} (hX : X ∉ eucCollisionSet d N) :
    fderiv ℝ (fderiv ℝ (fun Y => φ Y - ψ Y)) X = fderiv ℝ (fderiv ℝ φ) X - fderiv ℝ (fderiv ℝ ψ) X := by
  have hev : fderiv ℝ (fun Y => φ Y - ψ Y) =ᶠ[𝓝 X] fun Y => fderiv ℝ φ Y - fderiv ℝ ψ Y := by
    filter_upwards [u4_D_open.mem_nhds hX] with Y hY using w_fderiv_sub hφ hψ hY
  rw [hev.fderiv_eq]
  have h1 : DifferentiableAt ℝ (fderiv ℝ φ) X :=
    ((hφ.contDiffAt (u4_D_open.mem_nhds hX)).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have h2 : DifferentiableAt ℝ (fderiv ℝ ψ) X :=
    ((hψ.contDiffAt (u4_D_open.mem_nhds hX)).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  exact fderiv_sub h1 h2

lemma w_configGrad_sub {φ ψ : EucConfig d N → ℝ} (hφ : ContDiffOn ℝ 2 φ (eucCollisionSet d N)ᶜ)
    (hψ : ContDiffOn ℝ 2 ψ (eucCollisionSet d N)ᶜ) {X : EucConfig d N} (hX : X ∉ eucCollisionSet d N)
    (i : Fin N) :
    Phase2S82.configGrad (fun Y => φ Y - ψ Y) X i = Phase2S82.configGrad φ X i - Phase2S82.configGrad ψ X i := by
  rw [u4_configGrad_eq (hφ.sub hψ) hX i, u4_configGrad_eq hφ hX i, u4_configGrad_eq hψ hX i,
    w_fderiv_sub hφ hψ hX, ContinuousLinearMap.sub_comp, map_sub]

lemma w_laplacian_sub {φ ψ : EucConfig d N → ℝ} (hφ : ContDiffOn ℝ 2 φ (eucCollisionSet d N)ᶜ)
    (hψ : ContDiffOn ℝ 2 ψ (eucCollisionSet d N)ᶜ) {X : EucConfig d N} (hX : X ∉ eucCollisionSet d N)
    (i : Fin N) :
    Laplacian.laplacian (fun y => (fun Y => φ Y - ψ Y) (Function.update X i y)) (X i) =
      Laplacian.laplacian (fun y => φ (Function.update X i y)) (X i) -
        Laplacian.laplacian (fun y => ψ (Function.update X i y)) (X i) := by
  rw [u4_laplacian_eq (hφ.sub hψ) hX i, u4_laplacian_eq hφ hX i, u4_laplacian_eq hψ hX i,
    w_fderiv2_sub hφ hψ hX, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp

lemma w_gen_sub {a beta : ℝ} {φ ψ : EucConfig d N → ℝ} (hφ : ContDiffOn ℝ 2 φ (eucCollisionSet d N)ᶜ)
    (hψ : ContDiffOn ℝ 2 ψ (eucCollisionSet d N)ᶜ) {X : EucConfig d N} (hX : X ∉ eucCollisionSet d N) :
    particleGenerator (quadraticGradientDyn d (criticalS d) a beta) (fun Y => φ Y - ψ Y) X =
      particleGenerator (quadraticGradientDyn d (criticalS d) a beta) φ X -
        particleGenerator (quadraticGradientDyn d (criticalS d) a beta) ψ X := by
  unfold particleGenerator
  simp only [w_laplacian_sub hφ hψ hX, w_configGrad_sub hφ hψ hX, inner_sub_right, Finset.sum_sub_distrib,
    mul_sub]
  ring

lemma w_grad_cont {φ : EucConfig d N → ℝ} (hφ : ContDiffOn ℝ 2 φ (eucCollisionSet d N)ᶜ) (i : Fin N) :
    ContinuousOn (fun X => Phase2S82.configGrad φ X i) (eucCollisionSet d N)ᶜ := by
  have hDc : ContinuousOn (fun X => fderiv ℝ φ X) (eucCollisionSet d N)ᶜ :=
    hφ.continuousOn_fderiv_of_isOpen u4_D_open (by norm_num)
  have h1 : ContinuousOn (fun X : EucConfig d N => (InnerProductSpace.toDual ℝ (Euc d)).symm
      ((fderiv ℝ φ X).comp (u4L d N i))) (eucCollisionSet d N)ᶜ := by
    refine (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp_continuousOn ?_
    exact (((ContinuousLinearMap.compL ℝ (Euc d) (EucConfig d N) ℝ).flip (u4L d N i)).continuous.comp_continuousOn hDc)
  exact h1.congr fun X hX => u4_configGrad_eq hφ hX i

lemma w_gen_cont (hd : 2 ≤ d) (a beta : ℝ) {φ : EucConfig d N → ℝ}
    (hφ : ContDiffOn ℝ 2 φ (eucCollisionSet d N)ᶜ) :
    ContinuousOn (fun X => particleGenerator (quadraticGradientDyn d (criticalS d) a beta) φ X)
      (eucCollisionSet d N)ᶜ := by
  have hD2c : ContinuousOn (fun X => fderiv ℝ (fderiv ℝ φ) X) (eucCollisionSet d N)ᶜ :=
    (hφ.fderiv_of_isOpen u4_D_open (m := 1) (by norm_num)).continuousOn_fderiv_of_isOpen u4_D_open le_rfl
  have hgen : ∀ X : EucConfig d N, particleGenerator (quadraticGradientDyn d (criticalS d) a beta) φ X =
      beta⁻¹ * ∑ i, Laplacian.laplacian (fun y => φ (Function.update X i y)) (X i) +
        ∑ i, inner ℝ (particleDriftW (quadraticGradientDyn d (criticalS d) a beta) X i)
          (Phase2S82.configGrad φ X i) := fun X => rfl
  simp_rw [hgen]
  refine ContinuousOn.add (ContinuousOn.mul continuousOn_const (continuousOn_finsetSum _ fun i _ => ?_))
    (continuousOn_finsetSum _ fun i _ => ?_)
  · have : ContinuousOn (fun X : EucConfig d N => ∑ k, fderiv ℝ (fderiv ℝ φ) X
        (u4L d N i ((stdOrthonormalBasis ℝ (Euc d)) k)) (u4L d N i ((stdOrthonormalBasis ℝ (Euc d)) k)))
        (eucCollisionSet d N)ᶜ :=
      continuousOn_finsetSum _ fun k _ => (hD2c.clm_apply continuousOn_const).clm_apply continuousOn_const
    exact this.congr fun X hX => u4_laplacian_eq hφ hX i
  · exact (u4_drift_cont hd a beta i).inner (w_grad_cont hφ i)

end lin

end HRS.MS.S82W
