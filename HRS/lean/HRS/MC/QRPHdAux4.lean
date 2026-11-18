import HRS.MC.QRPHdAux3

/-!
# Packet HD, part 4: complex expansion of the real modes, their gradients and of `hTransport`
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped BigOperators ComplexConjugate

namespace HRS.MC.QRSpec.Hd

open HRS HRS.KernelGrad

variable {d : ℕ} {s : ℝ}

/-- sign `±1` indexed by `Bool`. -/
def hdsg (b : Bool) : ℤ := if b then 1 else -1

/-- coefficient of `e_{±a}` in the expansion of `realMode a`. -/
def hdcf (a : Lattice d) (b : Bool) : ℂ := if b then Torus.realCoef a else conj (Torus.realCoef a)

theorem hdsg_true : hdsg true = 1 := rfl
theorem hdsg_false : hdsg false = -1 := rfl

theorem hd_sg_smul_true (a : Lattice d) : hdsg true • a = a := by simp [hdsg]
theorem hd_sg_smul_false (a : Lattice d) : hdsg false • a = -a := by simp [hdsg]

theorem hd_realMode_expand (a : NonzeroLattice d) (x : Torus d) :
    ((Torus.realMode a x : ℝ) : ℂ) = ∑ b : Bool, hdcf a.1 b * Torus.mode (hdsg b • a.1) x := by
  rw [Fintype.sum_bool, hd_sg_smul_true, hd_sg_smul_false, Torus.realMode_cplx]
  simp [hdcf]

theorem hd_grad_comp (f : Euc d → ℝ) (y : Euc d) (i : Fin d) :
    (gradient f y) i = fderiv ℝ f y (EuclideanSpace.single i 1) := by
  have := InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (x := EuclideanSpace.single i (1 : ℝ))
    (y := fderiv ℝ f y)
  rw [EuclideanSpace.inner_single_right] at this
  simpa [gradient] using this

theorem hd_freq_single (κ : Lattice d) (i : Fin d) :
    Torus.freqFunctional κ (EuclideanSpace.single i (1 : ℝ)) = 2 * Real.pi * (κ i : ℝ) := by
  rw [Torus.freqFunctional_apply]
  simp [Lattice.dot, EuclideanSpace.single_apply]

open Classical in
theorem hd_grad_real (κ : NonzeroLattice d) (x : Torus d) (i : Fin d) :
    (Torus.grad (Torus.realMode κ) x) i =
      if Lattice.IsPosHalf κ.1 then -(Real.sqrt 2 * Torus.sinMode κ.1 x) * (2 * Real.pi * (κ.1 i : ℝ))
      else (Real.sqrt 2 * Torus.cosMode κ.1 x) * (2 * Real.pi * (κ.1 i : ℝ)) := by
  unfold Torus.grad
  rw [hd_grad_comp]
  have hfl : ∀ y : Euc d, Torus.freqFunctional κ.1 y = 2 * Real.pi * Lattice.dot κ.1 y :=
    fun y => Torus.freqFunctional_apply κ.1 y
  by_cases hp : Lattice.IsPosHalf κ.1
  · have hlift : Torus.lift (Torus.realMode κ) = fun y => Real.sqrt 2 * Real.cos (Torus.freqFunctional κ.1 y) := by
      funext y
      simp only [Torus.lift, Function.comp, Torus.realMode, hp, if_true, Torus.cosMode_mk, hfl]
    have hd : HasFDerivAt (fun y : Euc d => Real.sqrt 2 * Real.cos (Torus.freqFunctional κ.1 y))
        (Real.sqrt 2 • (-Real.sin (Torus.freqFunctional κ.1 (Torus.rep x)) • Torus.freqFunctional κ.1))
        (Torus.rep x) :=
      ((Torus.freqFunctional κ.1).hasFDerivAt.cos).const_mul (Real.sqrt 2)
    rw [hlift, hd.fderiv]
    simp only [if_pos hp, ContinuousLinearMap.smul_apply, hd_freq_single, smul_eq_mul]
    have : Torus.sinMode κ.1 x = Real.sin (Torus.freqFunctional κ.1 (Torus.rep x)) := by
      rw [← Torus.mk_rep x, Torus.sinMode_mk, hfl]
      simp [Torus.mk_rep]
    rw [this]; ring
  · have hlift : Torus.lift (Torus.realMode κ) = fun y => Real.sqrt 2 * Real.sin (Torus.freqFunctional κ.1 y) := by
      funext y
      simp only [Torus.lift, Function.comp, Torus.realMode, hp, if_false, Torus.sinMode_mk, hfl]
    have hd : HasFDerivAt (fun y : Euc d => Real.sqrt 2 * Real.sin (Torus.freqFunctional κ.1 y))
        (Real.sqrt 2 • (Real.cos (Torus.freqFunctional κ.1 (Torus.rep x)) • Torus.freqFunctional κ.1))
        (Torus.rep x) :=
      ((Torus.freqFunctional κ.1).hasFDerivAt.sin).const_mul (Real.sqrt 2)
    rw [hlift, hd.fderiv]
    simp only [if_neg hp, ContinuousLinearMap.smul_apply, hd_freq_single, smul_eq_mul]
    have : Torus.cosMode κ.1 x = Real.cos (Torus.freqFunctional κ.1 (Torus.rep x)) := by
      rw [← Torus.mk_rep x, Torus.cosMode_mk, hfl]
      simp [Torus.mk_rep]
    rw [this]; ring

end HRS.MC.QRSpec.Hd

end
