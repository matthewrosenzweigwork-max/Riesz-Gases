import HRS.MS.CritWholeTaylorRemainder
import HRS.MS.CritWholeResponse
import HRS.MS.WrInsAux2
import HRS.MS.WrMargBAux2
import HRS.MS.WrStatic
import HRS.MS.SharpBiasAux1
import HRS.Equilibrium.CavityResponse
import HRS.Equilibrium.L49Aux14

/-!
# S8.1 XS: definitions of the conditional-response packets CR01-CR12 (copied from the Pro skeleton
`S8.1-ConditionalResponse`, checked against the merged sources; namespace `HRS.Whole.S81b`)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole

namespace HRS.Whole.S81b

variable {d : ℕ} {M βm βp : ℝ}

def rate (N : ℕ) : ℝ := Real.sqrt (Real.log N) / N

def theta (D : Data d M βm βp) (N : ℕ) : Euc d → ℝ :=
  HRS.MS.Wr.wr13d_theta d ((d : ℝ) / 2) (N - 1) D.beta (mu D)

def defect (D : Data d M βm βp) (N : ℕ) : Euc d → ℝ :=
  insertionDefect d ((d : ℝ) / 2) N D.beta (mu D)

def poleFactor (D : Data d M βm βp) (N : ℕ) (x : Euc d) (t : ℝ) (y : Euc d) : ℝ :=
  Real.exp (-(t * (D.beta / N)) * critG d (x - y))

def othersSigma {n : ℕ} (i : Fin n) : MeasurableSpace (EucConfig d n) :=
  MeasurableSpace.comap (fun (Y : EucConfig d n) (j : {j : Fin n // j ≠ i}) => Y j)
    MeasurableSpace.pi

def condZ (D : Data d M βm βp) (N : ℕ) (i : Fin (N - 1))
    (x : Euc d) (t : ℝ) (Y : EucConfig d (N - 1)) : ℝ :=
  ∫ y, poleFactor D N x t y * Real.exp (-field D N i Y y) ∂(mu D)

def condMean (D : Data d M βm βp) (N : ℕ) (i : Fin (N - 1))
    (x : Euc d) (t : ℝ) (f : Euc d → ℝ) (Y : EucConfig d (N - 1)) : ℝ :=
  (∫ y, f y * poleFactor D N x t y * Real.exp (-field D N i Y y) ∂(mu D)) /
    condZ D N i x t Y

def prefactor (D : Data d M βm βp) (N : ℕ) (i : Fin (N - 1))
    (x : Euc d) (t : ℝ) (y : Euc d) : ℝ :=
  ∫ Y, Real.exp (-field D N i Y y) / condZ D N i x t Y ∂(pole D N x t)

def weightedTests (D : Data d M βm βp) (N : ℕ) (x : Euc d) (t : ℝ) :
    Set (Euc d → ℝ) :=
  {poleFactor D N x t, fun y => critG d (x - y) * poleFactor D N x t y}

def linearPart (D : Data d M βm βp) (N : ℕ) (i : Fin (N - 1))
    (f : Euc d → ℝ) (Y : EucConfig d (N - 1)) : ℝ :=
  (D.beta / N) * ∑ j ∈ Finset.univ.erase i,
      (∫ y, f y * critG d (y - Y j) ∂(mu D)) -
    D.beta * ∫ y, f y * convMeasure (critG d) (mu D) y ∂(mu D)

def poleB (D : Data d M βm βp) (N : ℕ) (x : Euc d) (t : ℝ) : ℝ :=
  ∫ y, poleFactor D N x t y ∂(mu D)

def poleF (D : Data d M βm βp) (N : ℕ) (x : Euc d) (t : ℝ) : ℝ :=
  ∫ y, critG d (x - y) * poleFactor D N x t y ∂(mu D)

def singularConditional (D : Data d M βm βp) (N : ℕ) (i : Fin (N - 1))
    (x : Euc d) (t : ℝ) : EucConfig d (N - 1) → ℝ :=
  (pole D N x t)[(fun Y => critG d (x - Y i)) | othersSigma i]

def poleSum (d N : ℕ) (x : Euc d) (Y : EucConfig d (N - 1)) : ℝ :=
  ∑ i, critG d (x - Y i)

def squareRow (D : Data d M βm βp) (N : ℕ) (x : Euc d) (t : ℝ) : ℝ :=
  ∫ y, critG d (x - y) ^ 2 * poleFactor D N x t y ∂(mu D)

def logMajorant (D : Data d M βm βp) (N : ℕ) (t : ℝ) : ℝ :=
  1 + |Real.log (t * (D.beta / N))|

def responseError (D : Data d M βm βp) (N : ℕ) (x : Euc d) : ℝ :=
  (theta D N x - 1) + D.beta * Kop (critG d) (mu D) (fun y => theta D N y - 1) x -
    projMean (mu D) (defect D N) x


end HRS.Whole.S81b
