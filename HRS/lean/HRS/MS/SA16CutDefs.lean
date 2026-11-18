import HRS.Whole.AppendixAAdjoint

/-!
# S.A.16 compatible-cutoff core: literal definitions

Literal copies of the self-contained definitions of `skeleton/cores/SA16-COMPATIBLE-CUTOFF.lean`
(everything before K1; `compatibleTest`, which needs the coefficient class, is not copied).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Cutoff
open HRS HRS.Whole HRS.Whole.AppendixA

def jumpCut (d : ℕ) (θ δ : ℝ) (u : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∫ z in {z : Euc d | δ < ‖z‖},
    (u x-u (x-z))/‖z‖^((d : ℝ)+θ)

def rawOdd (d : ℕ) (θ δ : ℝ) (i : Fin d)
    (u : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∫ z in {z : Euc d | δ < ‖z‖}, z i/‖z‖^((d : ℝ)+θ)*u (x-z)

/-- Normal flux matches at radius delta. The value at zero is immaterial. -/
def spliceKernel (d : ℕ) (θ δ : ℝ) (i : Fin d) (z : Euc d) : ℝ :=
  if δ < ‖z‖ then z i/‖z‖^((d : ℝ)+θ)
  else δ^(-θ)*z i/‖z‖^(d : ℝ)

def spliceOdd (d : ℕ) (θ δ : ℝ) (i : Fin d)
    (u : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∫ z, spliceKernel d θ δ i z*u (x-z)

def oddBlend (d : ℕ) (θ δ a : ℝ) (i : Fin d)
    (u : Euc d → ℝ) (x : Euc d) : ℝ :=
  rawOdd d θ δ i u x+a*(spliceOdd d θ δ i u x-rawOdd d θ δ i u x)

/-- Exact original Leibniz-first operator, with grad g_delta=-gamma L_delta. -/
def compatibleNl (d : ℕ) (θ δ gamma : ℝ)
    (M : Matrix (Fin d) (Fin d) ℝ) (μ u : Euc d → ℝ) (x : Euc d) : ℝ :=
  -gamma*∑ i : Fin d, ∑ j : Fin d, M j i*
    spliceOdd d θ δ i
      (fun y => μ y*partialDeriv (fun _ : Fin 1 => j) u y) x

def quadOuter (d q : ℕ) (θ δ : ℝ) (μ : Euc d → ℝ)
    (V : Euc d → Euc q) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ z in {z : Euc d | δ < ‖z‖},
    ENNReal.ofReal (μ x*‖V x-V (x-z)‖^2/‖z‖^((d : ℝ)+θ))

def quadInner (d q : ℕ) (θ δ r : ℝ) (μ : Euc d → ℝ)
    (V : Euc d → Euc q) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ z in Metric.ball (0 : Euc d) r,
    ENNReal.ofReal (δ^(-θ-1)*‖z‖^(1-(d : ℝ))*μ x*‖V x-V (x-z)‖^2)

def cutDiss (d q : ℕ) (θ p δ : ℝ) (μ : Euc d → ℝ)
    (W : Euc d → Fin q → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ z in {z : Euc d | δ < ‖z‖},
    ENNReal.ofReal (μ x*(vnorm (W x)+vnorm (W (x-z)))^(p-2)*
      vnorm (fun i => W x i-W (x-z) i)^2/‖z‖^((d : ℝ)+θ))

def tensorMass (d q : ℕ) (p : ℝ) (W : Euc d → Fin q → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (vnorm (W x)^p)

def jetTensor (d j : ℕ) (u : Euc d → ℝ) (x : Euc d) :
    (Fin j → Fin d) → ℝ := fun idx => partialDeriv idx u x

def jetPairDensity (d j : ℕ) (p : ℝ) (u v : Euc d → ℝ) (x : Euc d) : ℝ :=
  vnorm (jetTensor d j u x)^(p-2)*
    ∑ idx : Fin j → Fin d, partialDeriv idx u x*partialDeriv idx v x

def jetMass (d k : ℕ) (p : ℝ) (u : Euc d → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k+1), ∫ x, vnorm (jetTensor d j u x)^p

def jetPair (d k : ℕ) (p : ℝ) (u v : Euc d → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k+1), ∫ x, jetPairDensity d j p u v x

/-- The actual derivative budget: k=m+2 costs at most m+3. -/
def SliceBounds (d k : ℕ) (B : ℝ) (μ : Euc d → ℝ) : Prop :=
  ContDiff ℝ (max (k+1) 3) μ ∧ (∀ x, 0 ≤ μ x) ∧
    ∀ j ≤ max (k+1) 3, ∀ x,
      jbracket x^((d : ℝ)+3)*‖iteratedFDeriv ℝ j μ x‖ ≤ B


end HRS.Whole.AppendixA.Phase2SA16Cutoff
