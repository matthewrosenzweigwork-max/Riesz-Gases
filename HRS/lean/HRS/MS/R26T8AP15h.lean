import HRS.MS.R26T8AP15g
import HRS.MS.R26T8AP13

/-!
# S8.2 T8A P15h: algebra of the defect (Bochner-safe)
With `Lop C g x = nu Δg(x) + <b(x), ∇g(x)>` and `generatorW C 0 g = Lop C g + oneJ C g` (the definition of `oneJ`):
`pairA C mu Q x y - pairJ C mu Q x y = (Lop Q(.,y) - ∫ Lop Q(.,y) dmu)(x) + (Lop Q(x,.) - ∫ Lop Q(x,.) dmu)(y)`
as soon as `Lop Q(.,y)` and `oneJ Q(.,y)` (resp. in the second variable) are `mu`-integrable.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

/-- The local part `nu Δ + b·∇` of the generator. -/
def r26t8a_Lop (C : WholeCoeff d) (g : Euc d → ℝ) (x : Euc d) : ℝ :=
  C.ν * Laplacian.laplacian g x + inner ℝ (C.drift 0 x) (gradient g x)

theorem r26t8a_generatorW_split (C : WholeCoeff d) (g : Euc d → ℝ) :
    generatorW C 0 g = fun x => r26t8a_Lop C g x + oneJ C g x := by
  funext x
  unfold r26t8a_Lop oneJ
  ring

theorem r26t8a_projGen_sub_projMean (C : WholeCoeff d) (mu : Measure (Euc d)) (g : Euc d → ℝ)
    (h1 : Integrable (r26t8a_Lop C g) mu) (h2 : Integrable (oneJ C g) mu) (x : Euc d) :
    HRS.Whole.projGeneratorW C mu 0 g x - HRS.Whole.projMean mu (oneJ C g) x =
      r26t8a_Lop C g x - ∫ x', r26t8a_Lop C g x' ∂mu := by
  unfold HRS.Whole.projGeneratorW HRS.Whole.projMean HRS.Whole.pair
  rw [r26t8a_generatorW_split]
  simp only
  rw [integral_add h1 h2]
  ring

theorem r26t8a_p15_defect_alg (C : WholeCoeff d) (mu : Measure (Euc d)) (Q : Euc d → Euc d → ℝ) (x y : Euc d)
    (h1 : Integrable (r26t8a_Lop C (fun w => Q w y)) mu) (h2 : Integrable (oneJ C (fun w => Q w y)) mu)
    (h3 : Integrable (r26t8a_Lop C (Q x)) mu) (h4 : Integrable (oneJ C (Q x)) mu) :
    pairA C mu Q x y - pairJ C mu Q x y =
      (r26t8a_Lop C (fun w => Q w y) x - ∫ x', r26t8a_Lop C (fun w => Q w y) x' ∂mu) +
      (r26t8a_Lop C (Q x) y - ∫ y', r26t8a_Lop C (Q x) y' ∂mu) := by
  have e1 := r26t8a_projGen_sub_projMean C mu (fun w => Q w y) h1 h2 x
  have e2 := r26t8a_projGen_sub_projMean C mu (Q x) h3 h4 y
  unfold pairA pairJ
  linarith

end HRS.MS.R26T8A
