import HRS.MS.S82P2Local
import HRS.MS.WrPoleAux3

/-!
# S8.2: weighted weak-reference moments, definitions (port of the fixed skeleton Moments file)
Only definitions and structures; the producer theorems are not ported.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Phase2S82
open HRS HRS.Whole

def logN (N : ℕ) : ℝ := Real.log (Real.exp 1 * N)
def deltaN (N : ℕ) : ℝ := logN N / N

def pole {d : ℕ} (x y : Euc d) : ℝ := 1 + smallRadius x y ^ (-criticalS d)

def triplePole {d : ℕ} (x y z : Euc d) : ℝ :=
  pole x y * pole x z + pole x y * pole y z + pole x z * pole y z

def exponentialTilt {E : Type*} [MeasurableSpace E] (P : Measure E) (V : E → ℝ) : Measure E :=
  (ENNReal.ofReal (∫ x, Real.exp (V x) ∂P))⁻¹ •
    P.withDensity (fun x => ENNReal.ofReal (Real.exp (V x)))

def referenceExponent {d p n : ℕ} (q : Euc d → ℝ) (h : ℕ → Euc d → ℝ)
    (mu : Measure (Euc d)) (beta : ℝ) (N : ℕ) (pins : Fin p → Euc d)
    (X : EucConfig d n) : ℝ :=
  (∑ i, (beta * HRS.Whole.convMeasure q mu (X i) + h N (X i))) -
    (beta / (2 * N)) * pairSum (fun x y => q (x - y)) X -
    (beta / N) * ∑ i, ∑ j, q (X i - pins j)

def referenceLaw {d p : ℕ} (q : Euc d → ℝ) (h : ℕ → Euc d → ℝ)
    (mu : Measure (Euc d)) (beta : ℝ) (N n : ℕ) (pins : Fin p → Euc d) :
    Measure (EucConfig d n) :=
  exponentialTilt (Measure.pi fun _ => mu) (referenceExponent q h mu beta N pins)

def unpinnedReference {d : ℕ} (q : Euc d → ℝ) (h : ℕ → Euc d → ℝ)
    (mu : Measure (Euc d)) (beta : ℝ) (N : ℕ) : Measure (EucConfig d N) :=
  referenceLaw q h mu beta N N (fun i : Fin 0 => i.elim0)

def resampleLaw {d p n : ℕ} (q : Euc d → ℝ) (h : ℕ → Euc d → ℝ)
    (mu : Measure (Euc d)) (beta : ℝ) (N : ℕ) (pins : Fin p → Euc d)
    (i : Fin n) (X : EucConfig d n) : Measure (Euc d) :=
  exponentialTilt mu (fun y => beta * HRS.Whole.convMeasure q mu y + h N y -
    (beta / N) * ((∑ j ∈ Finset.univ.erase i, q (y - X j)) + ∑ j, q (y - pins j)))

def refMarginal {d : ℕ} (q : Euc d → ℝ) (h : ℕ → Euc d → ℝ)
    (mu : Measure (Euc d)) (beta : ℝ) (N : ℕ) : Measure (Euc d) :=
  if hn : 0 < N then
    (unpinnedReference q h mu beta N).map (fun X => X ⟨0, hn⟩) else mu

/-- The small heat-cutoff singular kernel; constants are independent of pins. -/
structure ShortRangePole (d : ℕ) (q : Euc d → ℝ) : Prop where
  measurable : Measurable q
  smooth : ContDiffOn ℝ ∞ q {z | z ≠ 0}
  even : ∀ z, q (-z) = q z
  nonneg : ∀ z, 0 ≤ q z
  near : ∃ r c C : ℝ, 0 < r ∧ r ≤ 1 ∧ 0 < c ∧
    ∀ z, 0 < ‖z‖ → ‖z‖ ≤ r →
      c * ‖z‖ ^ (-criticalS d) ≤ q z ∧ q z ≤ C * ‖z‖ ^ (-criticalS d)
  far : ∃ r c C : ℝ, 0 < r ∧ 0 < c ∧
    ∀ z, r ≤ ‖z‖ → q z ≤ C * Real.exp (-c * ‖z‖ ^ 2)

/-- Existing calibrated-law facts, with the harmless small-N field switch.
The uniform field bound makes the arbitrary finite-pin Wu adapter independent.
-/
structure CalibratedReferenceData (d : ℕ) (a beta : ℝ) (rho : Euc d → ℝ)
    (q : Euc d → ℝ) (h : ℕ → Euc d → ℝ) (C : ℝ) : Prop where
  positive : 0 < C
  short : ShortRangePole d q
  hmeas : ∀ N, Measurable (h N)
  hbound : ∀ N, 2 ≤ N → ∀ x, |h N x| ≤ C * deltaN N
  hsmall : ∀ N, 2 ≤ N → ∀ x, |h N x| ≤ 1
  small_row : ∀ x, beta * HRS.Whole.convMeasure q (HRS.Whole.withDensityReal rho) x ≤ 1 / 1000
  domination : ∀ N, 2 ≤ N →
    canonicalP d N a beta ≤ ENNReal.ofReal C •
      unpinnedReference q h (HRS.Whole.withDensityReal rho) beta N
  relative_L2 : ∀ N, 2 ≤ N →
    eLpNorm (fun x => ((refMarginal q h (HRS.Whole.withDensityReal rho) beta N).rnDeriv
      (HRS.Whole.withDensityReal rho) x).toReal - 1) 2 (HRS.Whole.withDensityReal rho) ≤
        ENNReal.ofReal (C * deltaN N)
  relative_small : Tendsto (fun N => eLpNorm (fun x =>
    ((refMarginal q h (HRS.Whole.withDensityReal rho) beta N).rnDeriv
      (HRS.Whole.withDensityReal rho) x).toReal - 1) ∞ (HRS.Whole.withDensityReal rho)) atTop (𝓝 0)

/-- Native calibration inputs needed for the new pointwise pin comparison.
The resampling inequality is on the displayed reference law. -/
structure WeakReferenceSetup (d : ℕ) (a beta : ℝ) (rho : Euc d → ℝ)
    (q : Euc d → ℝ) (h : ℕ → Euc d → ℝ) (C : ℝ) : Prop where
  positive : 0 < C
  short : ShortRangePole d q
  hmeas : ∀ N, Measurable (h N)
  hbound : ∀ N, 2 ≤ N → ∀ x, |h N x| ≤ C * deltaN N
  small_row : ∀ x, beta * HRS.Whole.convMeasure q (HRS.Whole.withDensityReal rho) x ≤ 1 / 1000
  probability : ∀ N, 2 ≤ N → ∀ p n : ℕ, p ≤ 6 → n + p ≤ N →
    ∀ pins : Fin p → Euc d, IsProbabilityMeasure
      (referenceLaw q h (HRS.Whole.withDensityReal rho) beta N n pins)
  domination : ∀ N, 2 ≤ N →
    canonicalP d N a beta ≤ ENNReal.ofReal C •
      unpinnedReference q h (HRS.Whole.withDensityReal rho) beta N
  conditional : ∀ N, 2 ≤ N → ∀ p n : ℕ, p ≤ 6 → n + p ≤ N →
    ∀ pins : Fin p → Euc d, ∀ i : Fin n, ∀ X : EucConfig d n,
      resampleLaw q h (HRS.Whole.withDensityReal rho) beta N pins i X ≤
        ENNReal.ofReal C • (HRS.Whole.withDensityReal rho).withDensity (fun y =>
          ENNReal.ofReal (Real.exp (-(beta / N) *
            ((∑ j ∈ Finset.univ.erase i, q (y - X j)) + ∑ j, q (y - pins j)))))
  resampling : ∀ N, 2 ≤ N → ∀ p n : ℕ, p ≤ 2 → n + p ≤ N → N - (n + p) ≤ 2 →
    ∀ pins : Fin p → Euc d, ∀ F : EucConfig d n → ℝ,
      MemLp F 2 (referenceLaw q h (HRS.Whole.withDensityReal rho) beta N n pins) →
      evariance F (referenceLaw q h (HRS.Whole.withDensityReal rho) beta N n pins) ≤
        ENNReal.ofReal C * ∑ i,
          ∫⁻ X, (∫⁻ y, ENNReal.ofReal
            ((F (Function.update X i y) - F X) ^ 2)
              ∂resampleLaw q h (HRS.Whole.withDensityReal rho) beta N pins i X)
            ∂referenceLaw q h (HRS.Whole.withDensityReal rho) beta N n pins
  relative_L2 : ∀ N, 2 ≤ N →
    eLpNorm (fun x => ((refMarginal q h (HRS.Whole.withDensityReal rho) beta N).rnDeriv
      (HRS.Whole.withDensityReal rho) x).toReal - 1) 2 (HRS.Whole.withDensityReal rho) ≤
        ENNReal.ofReal (C * deltaN N)
  relative_small : Tendsto (fun N => eLpNorm (fun x =>
    ((refMarginal q h (HRS.Whole.withDensityReal rho) beta N).rnDeriv
      (HRS.Whole.withDensityReal rho) x).toReal - 1) ∞ (HRS.Whole.withDensityReal rho)) atTop (𝓝 0)

def PinComparison {d : ℕ} (beta : ℝ) (rho : Euc d → ℝ)
    (q : Euc d → ℝ) (h : ℕ → Euc d → ℝ) (C : ℝ) : Prop :=
  (∀ N, 2 ≤ N →
    eLpNorm (fun x => ((refMarginal q h (HRS.Whole.withDensityReal rho) beta N).rnDeriv
      (HRS.Whole.withDensityReal rho) x).toReal - 1) ∞ (HRS.Whole.withDensityReal rho) ≤
        ENNReal.ofReal (C * deltaN N)) ∧
  ∀ N, 2 ≤ N → ∀ p n : ℕ, p ≤ 2 → n + p ≤ N → N - (n + p) ≤ 2 →
    ∀ pins : Fin p → Euc d, ∀ i : Fin n,
      ∀ᵐ z ∂HRS.Whole.withDensityReal rho,
        |(((referenceLaw q h (HRS.Whole.withDensityReal rho) beta N n pins).map
            (fun X => X i)).rnDeriv (HRS.Whole.withDensityReal rho) z).toReal -
          ((refMarginal q h (HRS.Whole.withDensityReal rho) beta N).rnDeriv
            (HRS.Whole.withDensityReal rho) z).toReal| ≤
          C * min 1 ((1 + ∑ j, q (z - pins j)) / N)

def CanonicalTriple {d : ℕ} (mu : Measure (Euc d))
    (G : Euc d → Euc d → Euc d → ℝ) : Prop :=
  (∀ x y z, G x y z = G y x z ∧ G x y z = G x z y) ∧
  ∀ x y, x ≠ y → Integrable (G x y) mu ∧ ∫ z, G x y z ∂mu = 0


end HRS.MS.Phase2S82
