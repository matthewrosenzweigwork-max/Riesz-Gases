import HRS.MS.S21F_D01
import HRS.MS.S21E_Kappa0
import HRS.MS.ProClosureS111WindowRestriction

/-!
# S2.1(iii): concrete initial-window objects

The initial statistic is centered by the actual first marginal of the exact
preparation `r26t3_Q`.  The Gaussian future remains an explicit input.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.S21E

variable {p : Parameters} {δ : ℝ}

/-- The initial empirical fluctuation, centered by the actual `Q_N` mean.
This is the scalar functional used to define the transported initial path. -/
def initialFunctional (R : Trajectory p δ) (N : ℕ)
    (X : EucConfig p.d N) (f : Euc p.d → ℝ) : ℝ :=
  Real.sqrt N *
    (HRS.Whole.pair (HRS.Whole.empirical X) f -
      HRS.Whole.pair (HRS.Whole.meanEmpirical (r26t3_Q R N)) f)

/-- The transported initial fluctuation on the physical window `[b,b+T]`.
The definition uses `windowPathOf`; its fallback is excluded by the
continuity theorem in the companion file. -/
def initialWindow (R : Trajectory p δ) (N : ℕ) (b : ℝ)
    (X : EucConfig p.d N) : Window p :=
  windowPathOf (wholeSpaceIndex p.d) p.T b (fun t =>
    r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d) t 0
      (initialFunctional R N X))

/-- The time-zero response representative transported over `[b,b+T]`.
As for `initialWindow`, path genuineness is a separate continuity fact. -/
def responseWindow (R : Trajectory p δ) (b : ℝ) (x : Euc p.d) : Window p :=
  windowPathOf (wholeSpaceIndex p.d) p.T b (fun t =>
    r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d) t 0
      (fun f => r26t3_a R f x))

/-- The initial cubic tensor.  The explicit probability witness is required
because the trajectory record does not register its time-zero probability as
a global typeclass instance. -/
def initialKappa (R : Trajectory p δ)
    (b : ℝ) [IsProbabilityMeasure (r26t3_mu R 0)] :
    TensorDual (Window p) 3 :=
  s21eKappa0 (r26t3_mu R 0) (responseWindow R b)

/-- Restrict an explicit full-history Gaussian family to the observation
window beginning at `b`.  No Gaussian family is constructed here. -/
def windowFuture
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d) H))
    (b : ℝ) (hb : 0 ≤ b) (v : ℝ) : Measure (Window p) :=
  Measure.map
    (HRS.MS.ProClosureS111.physicalWindowRestriction
      (d := p.d) (m := wholeSpaceIndex p.d) (T := p.T)
      (H := b + p.T) hb le_rfl)
    (future (b + p.T) v)

/-- The heat operator for the restricted explicit Gaussian future. -/
def initialHeat
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d) H))
    (b : ℝ) (hb : 0 ≤ b) (Φ : Window p → ℝ) (v : ℝ)
    (y : Window p) : ℝ :=
  r2HeatFn (windowFuture future b hb) Φ v y

/-- The signed, non-vacuous initial remainder.  Its static law is exactly
`r26t3_Q R N`, and its Gaussian comparison uses the supplied full-history
realization. -/
def initialRemainder (R : Trajectory p δ)
    [IsProbabilityMeasure (r26t3_mu R 0)]
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d) H))
    (N : ℕ) (G : GaussianRealization R) (b : ℝ) (hb : 0 ≤ b)
    (Φ : Window p → ℝ) : ℝ :=
  Real.sqrt N *
      ((∫ X, initialHeat future b hb Φ 0 (initialWindow R N b X)
          ∂(r26t3_Q R N)) -
        ∫ ω, Φ (r26t3_Zpath G b ω) ∂G.P) -
    (1 / 6) *
      ∫ ω, initialKappa R b
        (iteratedFDeriv ℝ 3 Φ (r26t3_Zpath G b ω)) ∂G.P

/-- The scalar path coordinate is the Round2 initial functional with the
same actual preparation law. -/
theorem fp81s21_initial_functional_formula
    (R : Trajectory p δ) (N : ℕ) (X : EucConfig p.d N)
    (t : ℝ) (α : MultiIndex p.d) :
    initialFunctional R N X (propagatorW (r26t3_coeff R) 0 t
        (oscTestFun (wholeSpaceIndex p.d) α)) =
      Real.sqrt N *
        (HRS.Whole.pair (HRS.Whole.empirical X)
            (propagatorW (r26t3_coeff R) 0 t (oscTestFun (wholeSpaceIndex p.d) α)) -
          HRS.Whole.pair (HRS.Whole.meanEmpirical (r26t3_Q R N))
            (propagatorW (r26t3_coeff R) 0 t (oscTestFun (wholeSpaceIndex p.d) α))) := by
  rfl

/-- `r26t3_Q` is the exact modulated preparation at the trajectory's initial
density; no thermal replacement is made. -/
theorem fp81s21_initial_Q_normalization
    (R : Trajectory p δ) (N : ℕ) :
    HRS.MS.R26T3.r26t3_Q R N =
      HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel p.d p.s) N p.γ
        (HRS.Whole.withDensityReal (R.ρ 0)) := by
  simp [r26t3_Q, r26t3_mu]

#print axioms fp81s21_initial_functional_formula
#print axioms fp81s21_initial_Q_normalization

end HRS.Fp81.S21

end
