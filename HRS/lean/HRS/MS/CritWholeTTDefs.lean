import HRS.Whole.Critical
import HRS.MS.WrPress
import HRS.MS.WrCavAux2
import HRS.MS.WrPoleAux3
import HRS.MS.WrKernAux1
import HRS.Equilibrium.ProductTransfer
import HRS.Equilibrium.TaylorAux7

/-!
# S8.1 XS: shared definitions of the critical Taylor transfer and conditional response (copied from the
Pro skeleton `S8.1-TaylorTransfer`, checked against the merged sources; namespace `HRS.Whole.S81b`, prefix `s81b_`)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole

namespace HRS.Whole.S81b

/-- Constants in all producers are selected before this datum. -/
structure Data (d : ℕ) (M βm βp : ℝ) where
  rho : Euc d → ℝ
  prob : IsProbDensity rho
  bound : ∀ x, rho x ≤ M
  beta : ℝ
  beta_mem : beta ∈ Set.Icc βm βp

variable {d : ℕ} {M βm βp : ℝ}

abbrev critG (d : ℕ) : Euc d → ℝ := rieszKernel d ((d : ℝ) / 2)
abbrev mu (D : Data d M βm βp) : Measure (Euc d) := withDensityReal D.rho
abbrev product (D : Data d M βm βp) (n : ℕ) : Measure (EucConfig d n) :=
  Measure.pi fun _ : Fin n => mu D
abbrev cavity (D : Data d M βm βp) (N : ℕ) :=
  cavityLaw d ((d : ℝ) / 2) N D.beta (mu D)
abbrev pole (D : Data d M βm βp) (N : ℕ) (x : Euc d) (t : ℝ) :=
  poleLaw d ((d : ℝ) / 2) N D.beta (mu D) x t

def tailG (d : ℕ) (H : ℝ) (z : Euc d) : ℝ :=
  critG d z - truncKernel d ((d : ℝ) / 2) H z

def field (D : Data d M βm βp) (N : ℕ) (i : Fin (N - 1))
    (Y : EucConfig d (N - 1)) (y : Euc d) : ℝ :=
  (D.beta / N) * ∑ j ∈ Finset.univ.erase i, critG d (y - Y j) -
    D.beta * convMeasure (critG d) (mu D) y

def fieldH (D : Data d M βm βp) (N : ℕ) (i : Fin (N - 1)) (H : ℝ)
    (Y : EucConfig d (N - 1)) (y : Euc d) : ℝ :=
  (D.beta / N) * ∑ j ∈ Finset.univ.erase i,
      truncKernel d ((d : ℝ) / 2) H (y - Y j) -
    D.beta * convMeasure (critG d) (mu D) y

def fieldLowerBound (d : ℕ) (M βp : ℝ) : ℝ :=
  max βp 0 * max (potentialBound d ((d : ℝ) / 2) M) 0

def tailConv (D : Data d M βm βp) (φ : Euc d → ℝ) (H : ℝ) (z : Euc d) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (φ y) * ENNReal.ofReal (tailG d H (y - z)) ∂(mu D)

def twoPole (ρ : Euc d → ℝ) (x z : Euc d) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (critG d (x - y) * critG d (y - z)) ∂(withDensityReal ρ)

def tests (d : ℕ) (x : Euc d) : Set (Euc d → ℝ) :=
  {fun _ => 1, fun y => critG d (x - y)}

def quadraticEnvelope (D : Data d M βm βp) (N : ℕ) (i : Fin (N - 1))
    (H : ℝ) (φ : Euc d → ℝ) (Y : EucConfig d (N - 1)) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (φ y) *
    ENNReal.ofReal (Real.exp (fieldLowerBound d M βp) * fieldH D N i H Y y ^ 2) ∂(mu D)

def remainder (D : Data d M βm βp) (N : ℕ) (i : Fin (N - 1))
    (f : Euc d → ℝ) (Y : EucConfig d (N - 1)) : ℝ :=
  ∫ y, f y * taylorH (field D N i Y y) ∂(mu D)

end HRS.Whole.S81b
