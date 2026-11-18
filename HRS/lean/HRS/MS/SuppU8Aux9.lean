import HRS.MS.SuppU8Aux6
import HRS.MS.SuppU8Aux4

/-!
# Worker U8 aux 9: Fourier representation of the forward differences of a Schwartz function
-/

noncomputable section

open MeasureTheory
open scoped FourierTransform

namespace HRS.U8

variable {d : ℕ}

theorem u8_fd_cont_joint {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (σ : List ℤ) {U : V → V → E}
    (hU : Continuous (fun p : V × V => U p.1 p.2)) :
    Continuous (fun p : V × V => u8_fd (σ.map (fun s => s • p.1)) (U p.1) p.2) := by
  induction σ generalizing U with
  | nil =>
    simp only [List.map_nil, u8_fd_nil]
    exact hU
  | cons s σ ih =>
    simp only [List.map_cons, u8_fd_cons]
    apply ih (U := fun y z => U y (z + s • y) - U y z)
    have h0 : Continuous (fun p : V × V => (p.1, p.2 + s • p.1)) := by fun_prop
    exact (hU.comp h0).sub hU

theorem u8_L_cont_joint {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (m : ℕ) {u : V → E} (hu : Continuous u) :
    Continuous (fun p : V × V => u8_fd (u8_L m p.1) u p.2) :=
  u8_fd_cont_joint _ (U := fun _ z => u z) (hu.comp continuous_snd)

/-- The exponential `x ↦ e^{2π i ⟪ξ,x⟫}`. -/
def u8_E (ξ x : EuclideanSpace ℝ (Fin d)) : ℂ :=
  Complex.exp (((2 * Real.pi * inner ℝ ξ x : ℝ) : ℂ) * Complex.I)

theorem u8_E_add (ξ x h : EuclideanSpace ℝ (Fin d)) : u8_E ξ (x + h) = u8_E ξ h * u8_E ξ x := by
  unfold u8_E
  rw [← Complex.exp_add, inner_add_right]
  congr 1
  push_cast; ring

theorem u8_E_norm (ξ x : EuclideanSpace ℝ (Fin d)) : ‖u8_E ξ x‖ = 1 := by
  unfold u8_E
  rw [Complex.norm_exp_ofReal_mul_I]

theorem u8_E_cont (x : EuclideanSpace ℝ (Fin d)) : Continuous (fun ξ => u8_E ξ x) := by
  unfold u8_E
  fun_prop

theorem u8_E_cont' (ξ : EuclideanSpace ℝ (Fin d)) : Continuous (fun x => u8_E ξ x) := by
  unfold u8_E
  fun_prop

theorem u8_E_mul_neg (ξ y : EuclideanSpace ℝ (Fin d)) :
    (u8_E ξ y - 1) * (u8_E ξ (-y) - 1) =
      ((2 - 2 * Real.cos (2 * Real.pi * inner ℝ y ξ) : ℝ) : ℂ) := by
  have h1 : u8_E ξ (-y) = Complex.exp (-(((2 * Real.pi * inner ℝ ξ y : ℝ) : ℂ) * Complex.I)) := by
    unfold u8_E
    congr 1
    rw [inner_neg_right]; push_cast; ring
  have h2 : (2 : ℂ) * Complex.cos ((2 * Real.pi * inner ℝ ξ y : ℝ) : ℂ) =
      u8_E ξ y + u8_E ξ (-y) := by
    rw [Complex.two_cos, h1]
    unfold u8_E
    congr 2
    ring
  have h3 : u8_E ξ y * u8_E ξ (-y) = 1 := by
    rw [h1]; unfold u8_E
    rw [← Complex.exp_add]; simp
  have h4 : (u8_E ξ y - 1) * (u8_E ξ (-y) - 1) =
      2 - (u8_E ξ y + u8_E ξ (-y)) := by
    ring_nf
    rw [h3]; ring
  rw [h4, ← h2, real_inner_comm ξ y]
  push_cast
  try rfl

end HRS.U8
