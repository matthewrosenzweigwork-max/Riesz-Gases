import HRS.MC.E214A1
import HRS.MC.E214A2
import HRS.MC.E214A3
import HRS.MC.E214B3
import HRS.MC.E214CFin

/-!
# Uniqueness of the window tensor

Two families `K, K'` satisfying the clauses of `IsWindowEdgeworth` (Theorem 2.13) agree for all `a ≥ 0`.  The
expansion clause alone determines `K a`: testing it with `Φ = (1/6) sin (t L)` shows that `K a - K' a` vanishes on
cubes `L ⊗ L ⊗ L` of continuous linear functionals (`E214B`), and a symmetric element of the projective tensor
product that vanishes on all cubes is zero (`E214C`).  The existence of particle systems and of Gaussians
satisfying the antecedents of the expansion is `E214A`.  The clause `formula` is not used.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214U

open HRS HRS.Sec7 HRS.Main

variable {d : ℕ}

theorem windowEdgeworth_tensor_unique (S : PreparedData d) (β₀ m T : ℝ) (hE : EdgeworthHyp S β₀ m)
    (hT : 0 < T) {K K' : ℝ → projTensor (PathSpace d m T) 3} {ε ε' : ℕ → ℝ}
    (h : IsWindowEdgeworth S β₀ m T K ε) (h' : IsWindowEdgeworth S β₀ m T K' ε') :
    ∀ a : ℝ, 0 ≤ a → K a = K' a := by
  intro a ha
  have hcube := fun L => HRS.MC.E214B.e214_tensor_diff_cube S β₀ m T hE hT h h'
    (fun a ha N hN => HRS.MC.E214A.e214_exists_selected S β₀ m hE N hN T a hT ha)
    (fun a ha => HRS.MC.E214A.e214_exists_gaussian S β₀ m T hE hT a ha) a ha L
  have hzero := HRS.MC.E214C.e214_tensor_zero_of_cubes d m T hT
    (((K a - K' a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3))
    (K a - K' a).2
    (fun M σ => by
      have h1 := h.symmetric a ha M σ
      have h2 := h'.symmetric a ha M σ
      change ((K a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3) (M.domDomCongr σ) -
          ((K' a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3) (M.domDomCongr σ) =
        ((K a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3) M -
          ((K' a : projTensor (PathSpace d m T) 3) : TensorDual (PathSpace d m T) 3) M
      rw [h1, h2])
    hcube
  have : K a - K' a = 0 := Subtype.ext hzero
  exact sub_eq_zero.1 this

end HRS.MC.E214U

end
