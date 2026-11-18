import HRS.MS.Fp81S21AdjointAll
import HRS.MS.R2InterpAux11

/-!
# S2.1(iii) wR31: the linearity hypothesis `S102Lin` for the moving coefficient

`S102Lin (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) T` asserts that the propagator
`propagatorW C u t` is linear on finite dual combinations for `0 ≤ u ≤ t ≤ T`.
It is obtained from `fp81s21_U_linear_of_hermite_combo` (which needs only `0 ≤ t`
and `u ∈ Icc 0 t`), the bound `t ≤ T` being simply not used.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole

/-- The linearity hypothesis `S102Lin` of the moving Ito contract, for the
moving coefficient `r26t3_coeff R`, holds unconditionally (for every `T`). -/
theorem fp81s21_S102Lin (p : HRS.MS.R26T3.Parameters) {δ : ℝ}
    (R : HRS.MS.R26T3.Trajectory p δ) (T : ℝ) :
    HRS.MS.R2Interp.S102Lin (HRS.MS.R26T3.r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) T := by
  unfold HRS.MS.R2Interp.S102Lin
  intro u t hu hut _htT φ ψ c hφ hψ
  have ht : 0 ≤ t := le_trans hu hut
  have hu' : u ∈ Set.Icc (0 : ℝ) t := ⟨hu, hut⟩
  have key := fp81s21_U_linear_of_hermite_combo p R hφ hψ c ht hu'
  have key' : propagatorW (HRS.MS.R26T3.r26t3_coeff R) u t (fun x => φ x + c * ψ x) =
      fun x => propagatorW (HRS.MS.R26T3.r26t3_coeff R) u t φ x +
        c * propagatorW (HRS.MS.R26T3.r26t3_coeff R) u t ψ x := key
  have hsum : (φ + c • ψ) = fun x => φ x + c * ψ x := by
    funext x
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hsum, key']
  funext x
  simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

#print axioms fp81s21_S102Lin
