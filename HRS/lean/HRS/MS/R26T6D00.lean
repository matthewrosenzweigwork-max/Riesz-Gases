import HRS.Whole.Window
import HRS.Whole.Round2
import HRS.MS.S111TermAux2
import HRS.MS.S111K2B02
import HRS.MS.S111K2B04h
import HRS.MS.S111TermB3

/-! Original proposed boundary vocabulary R26-T6.D00 (definition-only, no proof). -/
set_option autoImplicit false
set_option maxSynthPendingDepth 3
noncomputable section
open Classical MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff
open HRS HRS.Whole
namespace HRS.MS.R26T6

def r26t6_thermalCoeff (d : ℕ) (s a β : ℝ) (ρ : Euc d → ℝ) : WholeCoeff d :=
  (quadraticGradientDyn d s a β).coeff (fun _ => ρ)

def r26t6_clock (u T t : ℝ) : ℝ := (u+t)/(u+T)

def r26t6_unitTrace {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    (H : ℝ) (D : ℝ → K →L[ℝ] K →L[ℝ] ℝ) (q : ℝ) : K →L[ℝ] K →L[ℝ] ℝ :=
  H • D (H*q)

def r26t6_wickFinite {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → Ω → ℝ) (w : Ω) : ℝ :=
  ∑ i, ∑ j, A i j * (z i w*z j w - ∫ η, z i η*z j η ∂P)

def r26t6_screenedForcing {d : ℕ} (s β : ℝ) (μ : Measure (Euc d))
    (f h : Fin 3 → ℝ → Euc d → ℝ) (r : ℝ) : ℝ :=
  -(∑ i : Fin 3, ∫ xy, commutatorKernel d s (gradient (f i r)) xy.1 xy.2 *
      h (i+1) r xy.1 * h (i+2) r xy.2 ∂(μ.prod μ)) +
    (2/β) * ∑ i : Fin 3, ∫ x, inner ℝ (gradient (f i r) x)
      (gradient (f (i+1) r) x) * h (i+2) r x ∂μ

end HRS.MS.R26T6
