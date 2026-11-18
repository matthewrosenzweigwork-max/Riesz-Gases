import HRS.MS.CritForceAssemblyMaj
import HRS.MS.S82P2Mom

/-!
# S8.2 observed-time layer, packet T8A.C00: same-N fractional pin and influence objects (definitions, verbatim from the packet)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MS.R26T8A
open HRS.MS.Phase2S82

def r26t8a_fractionalLaw {d p : ℕ} (q : Euc d → ℝ) (h : ℕ → Euc d → ℝ)
    (mu : Measure (Euc d)) (beta : ℝ) (N n : ℕ) (pins : Fin p → Euc d)
    (weights : Fin p → ℝ) : Measure (HRS.Whole.EucConfig d n) :=
  exponentialTilt (Measure.pi (fun _ : Fin n => mu)) (fun X =>
    referenceExponent q h mu beta N (fun i : Fin 0 => Fin.elim0 i) X -
      ∑ i, ∑ j, weights j * q (X i - pins j))

def r26t8a_density {d n : ℕ} (mu : Measure (Euc d)) (P : Measure (HRS.Whole.EucConfig d n))
    (i : Fin n) (x : Euc d) : ℝ := ((P.map (fun X => X i)).rnDeriv mu x).toReal

def r26t8a_cutCost {d : ℕ} (q : Euc d → ℝ) (t : ℝ) (x y : Euc d) : ℝ :=
  1 - Real.exp (-t * q (x - y))

def r26t8a_influence {d : ℕ} (mu : Measure (Euc d)) (q : Euc d → ℝ)
    (beta : ℝ) (N n : ℕ) (A0 : ℝ) (f : Euc d → ℝ) (x : Euc d) : ℝ :=
  (n - 1 : ℝ) * (8 * ∫ y, r26t8a_cutCost q (beta / N) x y * f y ∂mu +
    64 * (beta / N) * A0 * ∫ y, f y ∂mu)

def r26t8a_boundary {d p : ℕ} (q : Euc d → ℝ) (mu : Measure (Euc d))
    (A0 : ℝ) (pins : Fin p → Euc d) (weights : Fin p → ℝ) (x : Euc d) : ℝ :=
  8 * ∑ j, r26t8a_cutCost q (weights j) x (pins j) + 64 * A0 * ∑ j, weights j

def r26t8a_cavityLog {d : ℕ} (mu : Measure (Euc d)) (q : Euc d → ℝ)
    (h : ℕ → Euc d → ℝ) (beta : ℝ) (N : ℕ) (z : Euc d) (t : ℝ) : ℝ :=
  Real.log (∫ X, Real.exp (-t * ∑ i, q (z - X i))
    ∂referenceLaw q h mu beta N (N - 1) (fun i : Fin 0 => Fin.elim0 i))

end HRS.MS.R26T8A
