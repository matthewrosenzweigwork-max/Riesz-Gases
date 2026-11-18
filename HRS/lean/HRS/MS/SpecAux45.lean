import HRS.MS.SpecAux44
import HRS.MS.SpecAux36

/-!
# S8P: the profiles `w_n = √ρ e_n` of the eigenfunctions: ground-state derivative and orthogonality (S8.7, packet b6)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.
* `s8p_Dj_w`: if `w = √ρ · s8p_E φ` (Schwartz) then `D_j w = Z^φ_j` (`mov2eZ`), pointwise;
* `s8p_ZZ_orth`: for the eigen-data, `∫ ∑_j Z^{φ_k}_j Z^{φ_i}_j = ω_i δ_{ik}`;
* `s8p_w_pair`: `∫ w_i φ_k = δ_{ik}` (biorthogonality of `w_i = √ρ e_i` and `φ_k`).
-/

noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace ContDiff

namespace HRS.MS.Spec

open HRS HRS.Whole HRS.MS.MovDec HRS.MS.MovLin

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

theorem s8p_w_eq (hρ : Mov2eRho d ρ) (φ : 𝓢R) (c : ℝ) (hc : c = s8p_Cc d s ρ φ) (x : Euc d) (β : ℝ) :
    mov2eW d s β ρ φ x - c * Real.sqrt (ρ x) = Real.sqrt (ρ x) * s8p_E d s β ρ φ x := by
  have hp := hρ.psi_pos x
  have hss := hρ.psi_sq x
  subst hc
  unfold mov2eW s8p_E s8p_U mov2eH
  generalize Real.sqrt (ρ x) = p at hp hss ⊢
  field_simp

theorem s8p_Dj_w (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ)
    (β : ℝ) (φ : 𝓢R) (w : 𝓢R)
    (hw : (⇑w : Euc d → ℝ) = fun x => Real.sqrt (ρ x) * s8p_E d s β ρ φ x) (j : Fin d) (x : Euc d) :
    s8p_Dj ρ (⇑w) j x = mov2eZ d s β ρ φ j x := by
  have hψd : DifferentiableAt ℝ (fun y => Real.sqrt (ρ y)) x :=
    (hρ.data.sqrt_smooth.differentiable (by simp)) x
  have hρd : DifferentiableAt ℝ ρ x := (hρ.data.smooth.differentiable (by simp)) x
  have hEd : DifferentiableAt ℝ (s8p_E d s β ρ φ) x :=
    ((s8p_E_smooth hd hs0 hsd hρ hE β φ).differentiable (by simp)) x
  have h1 : fderiv ℝ (⇑w) x = Real.sqrt (ρ x) • fderiv ℝ (s8p_E d s β ρ φ) x +
      s8p_E d s β ρ φ x • fderiv ℝ (fun y => Real.sqrt (ρ y)) x := by
    rw [hw]; exact (hψd.hasFDerivAt.mul hEd.hasFDerivAt).fderiv
  have hsq := HRS.MS.MovForce.mv1_fderiv_sqrt hρd (hρ.pos x) (EuclideanSpace.single j 1)
  have hlog : fderiv ℝ (fun y => Real.log (ρ y)) x (EuclideanSpace.single j 1) =
      gradient (fun y => Real.log (ρ y)) x j := (movtr_gradient_apply _ x j).symm
  have hZ := s8p_E_fderiv hd hs0 hsd hρ hE β φ x j
  unfold s8p_Dj s8p_pd s8p_ell
  rw [h1]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hsq, hlog, ← hZ, congrFun hw x]
  ring

end HRS.MS.Spec
