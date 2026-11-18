import HRS.MS.MfeConfAux105
import HRS.MS.MfeConfAux99
import HRS.MS.MfeConfAux16
import HRS.Whole.Basic

/-!
# S21F, packet R26-T3.E00: cutoff Gibbs weights and measurable Picard evaluation

Definitions only.  The exact cutoff kernel `sb1kM`, the singular Gibbs weight set to zero on collisions
(an a.e. modification), and the Picard evaluation `sb1Ψ` with diffusion coefficient `β⁻¹`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R26T3
open HRS HRS.Whole

def r26t3_regKernel (d : ℕ) (s : ℝ) (M : ℕ) : Euc d → ℝ :=
  HRS.MS.MfeConf.sb1kM d s M
def r26t3_Gamma (d N : ℕ) (s a β : ℝ) : Measure (EucConfig d N) :=
  HRS.Whole.canonicalGibbs (rieszKernel d s) (confinement a) N β
def r26t3_GammaM (d N : ℕ) (s a β : ℝ) (M : ℕ) : Measure (EucConfig d N) :=
  HRS.Whole.canonicalGibbs (r26t3_regKernel d s M) (confinement a) N β
def r26t3_ZM (d N : ℕ) (s a β : ℝ) (M : ℕ) : ℝ :=
  HRS.Whole.canonicalPartition (r26t3_regKernel d s M) (confinement a) N β
open Classical in
def r26t3_weight (d N : ℕ) (s a β : ℝ) (X : EucConfig d N) : ℝ :=
  if X ∈ eucCollisionSet d N then 0 else
    Real.exp (-β * HRS.Whole.canonicalHamiltonian (rieszKernel d s) (confinement a) X)
def r26t3_weightM (d N : ℕ) (s a β : ℝ) (M : ℕ) (X : EucConfig d N) : ℝ :=
  Real.exp (-β * HRS.Whole.canonicalHamiltonian (r26t3_regKernel d s M) (confinement a) X)
def r26t3_flow (d N : ℕ) (s a β : ℝ) (M : ℕ) (t : ℝ) :
    EucConfig d N × C(ℝ≥0, (Fin N × Fin d) → ℝ) → EucConfig d N :=
  HRS.MS.MfeConf.sb1Ψ
    (fun _ => HRS.MS.MfeConf.sb1DriftM (quadraticGradientDyn d s a β) (r26t3_regKernel d s M) N)
    (HRS.MP.SelfSimP4Impl.p4r_sigma d N β⁻¹) t

end HRS.MS.R26T3
