import HRS.MS.Fp81S21InitialCoord2
import HRS.MS.Fp81S21InitialUncentered2

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open S45
open HRS.Whole
open HRS (Euc)
open HRS.MS.R26T3

/-- `initialBq` uses the S99 gradient-corrector convention, while `initial_Bcoord`
uses the physical velocity `γ⁻¹∇χ`. This bridge records the exact scaling. -/
theorem fp81s21_initial_Bq_eq_gamma_mul_Bcoord
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (hγ : 0 < p.γ) {φ : ℕ → Euc p.d → ℝ}
    (F : InitialFamData R φ) (N j : ℕ)
    (X : EucConfig p.d N) :
    fp81s21_initialBq R (F.χ j) N X =
      p.γ * fp81s21_initial_Bcoord F N j X := by
  have hkernel :
      commutatorKernel p.d p.s (gradient (F.χ j)) =
        fun x y => p.γ * commutatorKernel p.d p.s
          (fun z => p.γ⁻¹ • gradient (F.χ j) z) x y := by
    funext x y
    simp only [commutatorKernel]
    have hγinv : p.γ * p.γ⁻¹ = 1 := mul_inv_cancel₀ hγ.ne'
    rw [← smul_sub, real_inner_smul_left]
    calc
      _ = (p.γ * p.γ⁻¹) *
          ⟪gradient (F.χ j) x - gradient (F.χ j) y,
            rieszKernelGrad p.d p.s (x - y)⟫ := by
          rw [hγinv, one_mul]
      _ = _ := by ring
  have henergy : ∀ Y : EucConfig p.d N,
      pairEnergy (commutatorKernel p.d p.s (gradient (F.χ j))) Y
          (r26t3_mu R 0) =
        p.γ * pairEnergy
          (commutatorKernel p.d p.s
            (fun z => p.γ⁻¹ • gradient (F.χ j) z)) Y (r26t3_mu R 0) := by
    intro Y
    rw [hkernel]
    unfold pairEnergy
    simp only [integral_const_mul, ← Finset.mul_sum]
    ring
  rw [fp81s21_initialBq, fp81s21_initial_Bcoord]
  rw [henergy X]
  have hinter :
      (∫ Y, pairEnergy
          (commutatorKernel p.d p.s (gradient (F.χ j))) Y (r26t3_mu R 0)
          ∂(r26t3_Q R N)) =
        p.γ * ∫ Y, pairEnergy
          (commutatorKernel p.d p.s
            (fun z => p.γ⁻¹ • gradient (F.χ j) z)) Y (r26t3_mu R 0)
          ∂(r26t3_Q R N) := by
    have hpY : ∀ Y : EucConfig p.d N,
        pairEnergy (commutatorKernel p.d p.s (gradient (F.χ j))) Y
            (r26t3_mu R 0) =
          p.γ * pairEnergy
            (commutatorKernel p.d p.s
              (fun z => p.γ⁻¹ • gradient (F.χ j) z)) Y (r26t3_mu R 0) :=
      henergy
    rw [show (fun Y : EucConfig p.d N => pairEnergy
        (commutatorKernel p.d p.s (gradient (F.χ j))) Y (r26t3_mu R 0)) =
      fun Y => p.γ * pairEnergy
        (commutatorKernel p.d p.s
          (fun z => p.γ⁻¹ • gradient (F.χ j) z)) Y (r26t3_mu R 0) from funext hpY,
      integral_const_mul]
  rw [hinter]
  ring

/-- Alias the family-indexed `initial_Cf` by the public `initialCf` interface. -/
theorem fp81s21_initialCf_eq_initial_Cf
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    {φ : ℕ → Euc p.d → ℝ} (F : InitialFamData R φ) (j l : ℕ) :
    fp81s21_initialCf R (φ j) (φ l) = fp81s21_initial_Cf F j l := rfl

#print axioms fp81s21_initial_Bq_eq_gamma_mul_Bcoord
#print axioms fp81s21_initialCf_eq_initial_Cf

end HRS.Fp81.S21

end
