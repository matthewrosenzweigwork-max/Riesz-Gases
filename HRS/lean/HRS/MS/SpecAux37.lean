import HRS.MS.SpecAux31
import HRS.Whole.CriticalNoise
import HRS.MS.Mov63CAux2

/-!
# S8P: the eigenfunction `e = A f` of a Schwartz core function in the ground-state frame (S8.7, packet b3)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  For a Schwartz `φ` (a vector `v = φ` in `L²_0`), `f = φ/√ρ`,
`U = g * (√ρ φ)`, `c = ∫ ρ U` and `e = ν f + U - c` (`= A f`, centered): `e` is `C^∞`, `√ρ ∂_i e = Z^φ_i` (`mov2eZ`) and
`weightedLaplacian ρ e = S φ / √ρ`.  So `Sφ = ω φ` becomes `L e = ω f` pointwise, the eigen-equation of `IsSpectralData`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace ContDiff

namespace HRS.MS.Spec

open HRS HRS.Whole HRS.MS.MovDec

variable {d : ℕ} {s : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

/-- The potential `U = g * (√ρ φ)`. -/
def s8p_U (d : ℕ) (s : ℝ) (ρ : Euc d → ℝ) (φ : Euc d → ℝ) : Euc d → ℝ :=
  HRS.Whole.convFun (rieszKernel d s) (mov2eH ρ φ)

/-- The centering constant `∫ ρ U`. -/
def s8p_Cc (d : ℕ) (s : ℝ) (ρ : Euc d → ℝ) (φ : Euc d → ℝ) : ℝ := ∫ x, ρ x * s8p_U d s ρ φ x

/-- The eigenfunction `e = ν φ/√ρ + U - c`. -/
def s8p_E (d : ℕ) (s β : ℝ) (ρ : Euc d → ℝ) (φ : Euc d → ℝ) (x : Euc d) : ℝ :=
  β⁻¹ * (φ x / Real.sqrt (ρ x)) + s8p_U d s ρ φ x - s8p_Cc d s ρ φ

theorem s8p_U_smooth (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ)
    (φ : 𝓢R) : ContDiff ℝ ∞ (s8p_U d s ρ φ) := by
  obtain ⟨hgrad, hdiff, -, -⟩ := mov2e_U_data hd hs0 hsd hρ hE φ
  rw [contDiff_infty_iff_fderiv]
  refine ⟨hdiff, ?_⟩
  have hfd : fderiv ℝ (s8p_U d s ρ φ) = fun x => (InnerProductSpace.toDual ℝ (Euc d))
      (movForce d s (mov2eH ρ φ) x) := by
    funext x
    show fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) (mov2eH ρ φ)) x = _
    rw [hgrad x]
    simp [gradient]
  rw [hfd]
  have hF : ContDiff ℝ ∞ (movForce d s (mov2eH ρ φ)) := by
    rw [contDiff_infty]
    intro k
    have hsm : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (mov2eH ρ φ) :=
      (hρ.data.sqrt_smooth.of_le (by exact_mod_cast le_top)).mul (φ.smooth _)
    exact HRS.MS.MovForce.mv1_force_contDiff hd hs0 hsd k hsm
      (HRS.MS.MovForce.mv1_h_movGauss hρ.data φ (k + 1))
  exact (InnerProductSpace.toDual ℝ (Euc d)).toContinuousLinearEquiv.contDiff.comp hF

theorem s8p_E_smooth (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ)
    (β : ℝ) (φ : 𝓢R) : ContDiff ℝ ∞ (s8p_E d s β ρ φ) := by
  have h1 : ContDiff ℝ ∞ (fun x => φ x / Real.sqrt (ρ x)) :=
    (φ.smooth ⊤).div hρ.data.sqrt_smooth (fun x => (hρ.psi_pos x).ne')
  unfold s8p_E
  exact ((contDiff_const.mul h1).add (s8p_U_smooth hd hs0 hsd hρ hE φ)).sub contDiff_const

theorem s8p_E_fderiv (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ)
    (β : ℝ) (φ : 𝓢R) (x : Euc d) (i : Fin d) :
    Real.sqrt (ρ x) * fderiv ℝ (s8p_E d s β ρ φ) x (EuclideanSpace.single i 1) =
      mov2eZ d s β ρ φ i x := by
  obtain ⟨hgrad, hUd, -, -⟩ := mov2e_U_data hd hs0 hsd hρ hE φ
  have hψd : DifferentiableAt ℝ (fun y => Real.sqrt (ρ y)) x :=
    (hρ.data.sqrt_smooth.differentiable (by simp)) x
  have hρd : DifferentiableAt ℝ ρ x := (hρ.data.smooth.differentiable (by simp)) x
  have hne : Real.sqrt (ρ x) ≠ 0 := (hρ.psi_pos x).ne'
  have hinv : HasFDerivAt (fun y => (Real.sqrt (ρ y))⁻¹)
      ((-((Real.sqrt (ρ x)) ^ 2)⁻¹) • fderiv ℝ (fun y => Real.sqrt (ρ y)) x) x :=
    (hasDerivAt_inv hne).comp_hasFDerivAt x hψd.hasFDerivAt
  have hq := φ.differentiableAt.hasFDerivAt.mul hinv
  have hEfun : s8p_E d s β ρ φ = fun y => β⁻¹ * (φ y * (Real.sqrt (ρ y))⁻¹) + s8p_U d s ρ φ y -
      s8p_Cc d s ρ φ := by
    funext y; simp [s8p_E, div_eq_mul_inv]
  have hE' : HasFDerivAt (s8p_E d s β ρ φ)
      (β⁻¹ • (φ x • ((-((Real.sqrt (ρ x)) ^ 2)⁻¹) • fderiv ℝ (fun y => Real.sqrt (ρ y)) x) +
        (Real.sqrt (ρ x))⁻¹ • fderiv ℝ (⇑φ) x) + fderiv ℝ (s8p_U d s ρ φ) x) x := by
    rw [hEfun]
    exact ((hq.const_mul β⁻¹).add (hUd x).hasFDerivAt).sub_const (s8p_Cc d s ρ φ)
  rw [hE'.fderiv]
  have hsq := HRS.MS.MovForce.mv1_fderiv_sqrt hρd (hρ.pos x) (EuclideanSpace.single i 1)
  have hlog : fderiv ℝ (fun y => Real.log (ρ y)) x (EuclideanSpace.single i 1) =
      gradient (fun y => Real.log (ρ y)) x i := (movtr_gradient_apply _ x i).symm
  have hUi : fderiv ℝ (s8p_U d s ρ φ) x (EuclideanSpace.single i 1) =
      movForce d s (mov2eH ρ φ) x i := by
    show fderiv ℝ (HRS.Whole.convFun (rieszKernel d s) (mov2eH ρ φ)) x _ = _
    rw [hgrad x, movtr_gradient_apply]
  have hUi' : fderiv ℝ (s8p_U d s ρ φ) x (EuclideanSpace.single i 1) =
      movForce d s (mov2eH ρ φ) x i := hUi
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    smul_eq_mul]
  rw [hsq, hlog, hUi']
  unfold mov2eZ
  have hss : Real.sqrt (ρ x) ^ 2 = ρ x := Real.sq_sqrt (hρ.pos x).le
  field_simp
  ring

theorem s8p_E_grad (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ)
    (β : ℝ) (φ : 𝓢R) (y : Euc d) (i : Fin d) :
    gradient (s8p_E d s β ρ φ) y i = mov2eZ d s β ρ φ i y / Real.sqrt (ρ y) := by
  rw [movtr_gradient_apply, eq_div_iff (hρ.psi_pos y).ne', mul_comm]
  exact s8p_E_fderiv hd hs0 hsd hρ hE β φ y i

theorem s8p_E_wlap (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ)
    (β : ℝ) (φ : 𝓢R) (x : Euc d) :
    weightedLaplacian ρ (s8p_E d s β ρ φ) x = movS d s β ρ φ x / Real.sqrt (ρ x) := by
  have hsm := s8p_E_smooth hd hs0 hsd hρ hE β φ
  have hlap : Laplacian.laplacian (s8p_E d s β ρ φ) x = movDiv (fun y => gradient (s8p_E d s β ρ φ) y) x :=
    (HRS.MS.S98.s98_movDiv_gradient (by simpa using (contDiff_infty.1 hsm 2)) x).symm
  have hgd : DifferentiableAt ℝ (fun y => gradient (s8p_E d s β ρ φ) y) x :=
    HRS.MS.MovLin.mov2a_gradient_diff hsm x
  have hψd : DifferentiableAt ℝ (fun y => Real.sqrt (ρ y)) x :=
    (hρ.data.sqrt_smooth.differentiable (by simp)) x
  have hρd : DifferentiableAt ℝ ρ x := (hρ.data.smooth.differentiable (by simp)) x
  have hne : Real.sqrt (ρ x) ≠ 0 := (hρ.psi_pos x).ne'
  have hinv : HasFDerivAt (fun y => (Real.sqrt (ρ y))⁻¹)
      ((-((Real.sqrt (ρ x)) ^ 2)⁻¹) • fderiv ℝ (fun y => Real.sqrt (ρ y)) x) x :=
    (hasDerivAt_inv hne).comp_hasFDerivAt x hψd.hasFDerivAt
  have hkey : ∀ i : Fin d, fderiv ℝ (fun y => gradient (s8p_E d s β ρ φ) y i) x (EuclideanSpace.single i 1) =
      (fderiv ℝ (mov2eZ d s β ρ φ i) x (EuclideanSpace.single i 1) -
        (1 / 2) * gradient (fun y => Real.log (ρ y)) x i * mov2eZ d s β ρ φ i x) / Real.sqrt (ρ x) := by
    intro i
    have hZd : DifferentiableAt ℝ (mov2eZ d s β ρ φ i) x :=
      ((mov2e_Z_GD hd hs0 hsd hρ hE β φ i).1.differentiable (by norm_num)) x
    have hfun : (fun y => gradient (s8p_E d s β ρ φ) y i) =
        fun y => mov2eZ d s β ρ φ i y * (Real.sqrt (ρ y))⁻¹ := by
      funext y; rw [s8p_E_grad hd hs0 hsd hρ hE β φ y i, div_eq_mul_inv]
    have hmul : HasFDerivAt (fun y => mov2eZ d s β ρ φ i y * (Real.sqrt (ρ y))⁻¹)
        (mov2eZ d s β ρ φ i x • ((-((Real.sqrt (ρ x)) ^ 2)⁻¹) • fderiv ℝ (fun y => Real.sqrt (ρ y)) x) +
          (Real.sqrt (ρ x))⁻¹ • fderiv ℝ (mov2eZ d s β ρ φ i) x) x := hZd.hasFDerivAt.mul hinv
    rw [hfun, hmul.fderiv]
    have hsq := HRS.MS.MovForce.mv1_fderiv_sqrt hρd (hρ.pos x) (EuclideanSpace.single i 1)
    have hlog : fderiv ℝ (fun y => Real.log (ρ y)) x (EuclideanSpace.single i 1) =
        gradient (fun y => Real.log (ρ y)) x i := (movtr_gradient_apply _ x i).symm
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hsq, hlog]
    have hss : Real.sqrt (ρ x) ^ 2 = ρ x := Real.sq_sqrt (hρ.pos x).le
    field_simp
    ring
  have hsum : Laplacian.laplacian (s8p_E d s β ρ φ) x = ∑ i : Fin d,
      (fderiv ℝ (mov2eZ d s β ρ φ i) x (EuclideanSpace.single i 1) -
        (1 / 2) * gradient (fun y => Real.log (ρ y)) x i * mov2eZ d s β ρ φ i x) / Real.sqrt (ρ x) := by
    rw [hlap, mov2e_movDiv_coord hgd]
    exact Finset.sum_congr rfl fun i _ => hkey i
  have hin : inner ℝ (gradient (fun y => Real.log (ρ y)) x) (gradient (s8p_E d s β ρ φ) x) =
      ∑ i : Fin d, gradient (fun y => Real.log (ρ y)) x i * (mov2eZ d s β ρ φ i x / Real.sqrt (ρ x)) := by
    rw [HRS.MS.Mov63.mnc_inner_eq_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [s8p_E_grad hd hs0 hsd hρ hE β φ x i]
  unfold weightedLaplacian
  rw [hsum, hin, mov2e_S_eq hd hs0 hsd hρ hE β φ x, ← Finset.sum_add_distrib, neg_div, Finset.sum_div]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp
  ring

end HRS.MS.Spec
