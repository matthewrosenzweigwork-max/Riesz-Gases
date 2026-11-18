import HRS.Whole.AppendixAAdjoint
import HRS.MH.AdjointRdDefs
import HRS.PDE.ToolboxRd.Weighted

/-!
# S.A.12 near regimes: the shared definitions of `skeleton/cores/SA12-NEAR-REGIMES.lean`

`firstRiesz`, `hessRiesz`, `matrixHess`, `EucNlBoundPositive`, copied verbatim (the header and namespace are the
only differences), so that the near-estimate packets N1-N9 share one set of definitions.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd

def firstRiesz (d : ℕ) (s : ℝ) (i : Fin d) (v : Euc d → ℝ) (x : Euc d) : ℝ :=
  fderiv ℝ (fun x' => ∫ y, rieszKernel d s (x' - y) * v y) x
    (EuclideanSpace.single i (1 : ℝ))

def hessRiesz (d : ℕ) (s : ℝ) (i j : Fin d) (v : Euc d → ℝ) (x : Euc d) : ℝ :=
  iteratedFDeriv ℝ 2 (fun x' => ∫ y, rieszKernel d s (x' - y) * v y) x
    (fun l => EuclideanSpace.single (if l = 0 then i else j) (1 : ℝ))

def matrixHess (d : ℕ) (s : ℝ) (M : Matrix (Fin d) (Fin d) ℝ)
    (v : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∑ i : Fin d, ∑ j : Fin d, M j i * hessRiesz d s i j v x

/-- The source regularity predicate does not assert nonnegativity.
R2c must consume this positivity-explicit version of the near contract. -/
def EucNlBoundPositive (d : ℕ) (s : ℝ) (m : ℕ) (Λ Cb T : ℝ)
    (χ χh : Euc d → ℝ) (E : Finset (Fin d → ℤ)) (A κ : ℝ)
    (hreg : Matrix (Fin d) (Fin d) ℝ → Prop) : Prop :=
  ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d),
    IsAdvectingDrift m Cb T b → IsNegDriftFlow T b Ψ →
    ∀ M : Matrix (Fin d) (Fin d) ℝ, hreg M →
    ∀ μ : Euc d → ℝ, IsRegularDensityW (m + 3) Λ μ → (∀ x, 0 ≤ μ x) →
    ∀ F : Euc d → ℝ, BddJets m F → ∀ τ ∈ Icc (0 : ℝ) T, ∀ z : Fin d → ℤ,
      -(2 * jetPair m (advCutoff χ Ψ τ (cellPt d z)) F
        (eucNonlocal s M (fun y => advCutoff χh Ψ τ (cellPt d z) y * μ y) F)) ≤
        κ * ∑ k ∈ E, cellDissip m χ Ψ τ (cellPt d (z + k)) F +
        A * ∑ k ∈ E, cellEnergy m χ Ψ τ (cellPt d (z + k)) F

end HRS.MH.AdjointRd.Phase2SA12Near
