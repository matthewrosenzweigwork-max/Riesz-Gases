import HRS.MS.Fp81S21WeightedGen
import HRS.MS.WhoAux1
import HRS.MS.WhoAux4
import HRS.MS.WhoAux12

/-!
# S2.1(iii), packet 32b B3: local generator calculus

The local part is stated with the viscosity read from the actual coefficient
used by `generatorW`. For the quadratic gradient dynamics this coefficient is
constant along the trajectory and reduces to `p.β⁻¹`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

/-- The viscosity in the stationary coefficient underlying the moving
trajectory coefficient. -/
def fp81s21_b3_viscosity (p : Parameters) : ℝ :=
  ((quadraticGradientDyn p.d p.s p.a p.β).coeff (fun _ => 0)).ν

/-- The real local part of `generatorW`, with an arbitrary drift field. The
viscosity is taken from the actual quadratic-gradient coefficient. -/
def fp81s21_b3_local (p : Parameters) (b : Euc p.d → Euc p.d)
    (f : Euc p.d → ℝ) : Euc p.d → ℝ := fun x =>
  fp81s21_b3_viscosity p * Laplacian.laplacian f x +
    inner ℝ (b x) (gradient f x)

/-- The viscosity of every trajectory coefficient is the static viscosity
from the quadratic-gradient dynamics. -/
theorem fp81s21_b3_viscosity_eq_actual (p : Parameters) {δ : ℝ}
    (R : Trajectory p δ) :
    (r26t3_coeff R).ν = fp81s21_b3_viscosity p := rfl

/-- In particular, the coefficient used by the real local part agrees with
the inverse-temperature shorthand in the proposed header. -/
theorem fp81s21_b3_viscosity_eq_beta (p : Parameters) :
    fp81s21_b3_viscosity p = p.β⁻¹ := rfl

/-- Smooth input and drift give the regularity of the actual local operator. -/
theorem fp81s21_b3_local_contDiff (p : Parameters)
    (b : Euc p.d → Euc p.d) (f : Euc p.d → ℝ)
    (hb : ContDiff ℝ (2 * p.d + 6) b)
    (hf : ContDiff ℝ (2 * p.d + 8) f) :
    ContDiff ℝ (2 * p.d + 6) (fp81s21_b3_local p b f) := by
  let q : ℕ := 2 * p.d + 6
  have hfq : ContDiff ℝ ((q + 2 : ℕ) : WithTop ℕ∞) f := by
    change ContDiff ℝ (2 * p.d + 8) f
    exact hf
  have hblap := HRS.MS.Who.who_lap_iter (i := q) hfq
  have hbq : ContDiff ℝ (q : WithTop ℕ∞) b := by simpa [q] using hb
  have hfd : ContDiff ℝ (2 * p.d + 7) (fderiv ℝ f) := by
    exact hf.fderiv_right (m := (2 * p.d + 7 : ℕ)) (by norm_cast)
  have hfdq : ContDiff ℝ (q : WithTop ℕ∞) (fderiv ℝ f) :=
    hfd.of_le (by
      have hn : q ≤ 2 * p.d + 7 := by dsimp [q]; omega
      exact_mod_cast hn)
  have htransport : ContDiff ℝ (q : WithTop ℕ∞)
      (fun x => fderiv ℝ f x (b x)) := hfdq.clm_apply hbq
  have htransport_eq : (fun x => fderiv ℝ f x (b x)) =
      fun x => inner ℝ (b x) (gradient f x) := by
    funext x
    symm
    rw [real_inner_comm]
    exact inner_gradient_left
  have hsum : ContDiff ℝ (q : WithTop ℕ∞)
      (fun x => fp81s21_b3_viscosity p * Laplacian.laplacian f x +
        fderiv ℝ f x (b x)) :=
    (contDiff_const.mul hblap.1).add htransport
  have hlocalEq : fp81s21_b3_local p b f =
      (fun x => fp81s21_b3_viscosity p * Laplacian.laplacian f x +
        fderiv ℝ f x (b x)) := by
    funext x
    simp only [fp81s21_b3_local]
    congr 1
    exact (congrFun htransport_eq x).symm
  rw [hlocalEq]
  simpa [q] using hsum

#print axioms fp81s21_b3_viscosity_eq_actual
#print axioms fp81s21_b3_viscosity_eq_beta
#print axioms fp81s21_b3_local_contDiff

end HRS.Fp81.S21
