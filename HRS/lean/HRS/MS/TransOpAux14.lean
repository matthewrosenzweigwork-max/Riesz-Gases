import HRS.MS.TransOpAux13
import HRS.MS.SuppA0Aux1

/-!
# S611 packet P4a: conjugation of the linear coefficients by a time-dependent translation

For `c, c' : ℝ → ℝ^d` with `c' = ċ`, and coefficients `Cc` with `drift_c(r,x) = drift'(r, x - c_r) + c'_r`,
`ρ_c(r,x) = ρ'(r, x - c_r)` (same `s, M, ν`):
* `s611_generator_shift`: `L^c_r (g(· - c_r))(x) = L'_r g (x - c_r) + c'_r · ∇g(x - c_r)`;
* `s611_adjoint_shift`: classical adjoint solutions of `C'` (terminal datum `φ`) are carried to classical adjoint solutions
  of `Cc` (datum `φ(· - c_t)`) by `f ↦ f(r, · - c_r)`.
Specialisation to the quadratic gradient dynamics and `c_r = movShift q b r` (`c' = -q c`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.TransOp

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s611_conv_shift (G : Euc d → Euc d) (ρ : Euc d → ℝ) (a x : Euc d) :
    convGradConvW G (fun y => ρ (y - a)) x = convGradConvW G ρ (x - a) := by
  have h : ∀ y : Euc d, (if ‖x - (y + a)‖ ≤ 1 / 4 then (ρ (y + a - a) - ρ (x - a)) • G (x - (y + a))
      else ρ (y + a - a) • G (x - (y + a))) =
      (if ‖(x - a) - y‖ ≤ 1 / 4 then (ρ y - ρ (x - a)) • G ((x - a) - y) else ρ y • G ((x - a) - y)) := by
    intro y
    have e : x - (y + a) = x - a - y := by abel
    simp only [add_sub_cancel_right, e]
  calc convGradConvW G (fun y => ρ (y - a)) x
      = ∫ y, (if ‖x - y‖ ≤ 1 / 4 then (ρ (y - a) - ρ (x - a)) • G (x - y)
          else ρ (y - a) • G (x - y)) := rfl
    _ = ∫ y, (if ‖x - (y + a)‖ ≤ 1 / 4 then (ρ (y + a - a) - ρ (x - a)) • G (x - (y + a))
          else ρ (y + a - a) • G (x - (y + a))) :=
        (integral_add_right_eq_self (fun y => if ‖x - y‖ ≤ 1 / 4 then (ρ (y - a) - ρ (x - a)) • G (x - y)
          else ρ (y - a) • G (x - y)) a).symm
    _ = ∫ y, (if ‖(x - a) - y‖ ≤ 1 / 4 then (ρ y - ρ (x - a)) • G ((x - a) - y)
          else ρ y • G ((x - a) - y)) := integral_congr_ae (Filter.Eventually.of_forall h)
    _ = convGradConvW G ρ (x - a) := rfl

theorem s611_drift_shift (s q β : ℝ) (ρ : Euc d → ℝ) (a x : Euc d) :
    meanFieldDriftW (quadraticGradientDyn d s q β) (fun y => ρ (y - a)) x =
      meanFieldDriftW (quadraticGradientDyn d s q β) ρ (x - a) - q • a := by
  unfold meanFieldDriftW
  rw [s611_conv_shift]
  have e1 : gradient (quadraticGradientDyn d s q β).V x = q • x := movtr_gradient_confinement q x
  have e2 : gradient (quadraticGradientDyn d s q β).V (x - a) = q • (x - a) :=
    movtr_gradient_confinement q (x - a)
  rw [e1, e2, smul_sub]
  abel

theorem s611_generator_shift {C' Cc : WholeCoeff d} (c c' : Euc d) (r : ℝ)
    (hs : Cc.s = C'.s) (hM : Cc.M = C'.M) (hν : Cc.ν = C'.ν)
    (hdrift : ∀ x, Cc.drift r x = C'.drift r (x - c) + c')
    (hρ : ∀ x, Cc.ρ r x = C'.ρ r (x - c)) (g : Euc d → ℝ) (x : Euc d) :
    generatorW Cc r (fun y => g (y - c)) x =
      generatorW C' r g (x - c) + inner ℝ c' (gradient g (x - c)) := by
  have hlap : Laplacian.laplacian (fun y => g (y - c)) x = Laplacian.laplacian g (x - c) := by
    have := HRS.MS.A0.a0_laplacian_comp_add g (-c) x
    simpa [sub_eq_add_neg] using this
  have hgrad : ∀ y, gradient (fun y => g (y - c)) y = gradient g (y - c) := fun y => by
    have := HRS.MS.A0.a0_gradient_comp_add g (-c) y
    simpa [sub_eq_add_neg] using this
  unfold generatorW
  rw [hlap, hdrift x, hν, hs, hM]
  have hconv : ∀ j : Fin d,
      (convGradConvW (rieszKernelGrad d C'.s)
        (fun y => Cc.ρ r y * (Torus.matVec C'.M.transpose (gradient g (y - c))) j) x) j =
      (convGradConvW (rieszKernelGrad d C'.s)
        (fun z => C'.ρ r z * (Torus.matVec C'.M.transpose (gradient g z)) j) (x - c)) j := by
    intro j
    have := s611_conv_shift (rieszKernelGrad d C'.s)
      (fun z => C'.ρ r z * (Torus.matVec C'.M.transpose (gradient g z)) j) c x
    have e : (fun y => Cc.ρ r y * (Torus.matVec C'.M.transpose (gradient g (y - c))) j) =
        fun y => (fun z => C'.ρ r z * (Torus.matVec C'.M.transpose (gradient g z)) j) (y - c) := by
      funext y
      simp only [hρ y]
    rw [e, this]
  simp only [hgrad, hconv, inner_add_left]
  ring

end HRS.MS.TransOp

end
