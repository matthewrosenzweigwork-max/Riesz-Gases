import HRS.Whole.AppendixAAdjoint

/-!
# S.A.16 energy-transfer core: literal definitions

Literal copies of the self-contained definitions of `skeleton/cores/SA16-ENERGY-TRANSFER.lean`
(`closedTensor`, `jetEnergy`, `jetNorm`, `closedPairDensity`, `IsSmoothNorm`, `PositiveLpMatrix`,
`cutoffRadius`, `cutoffRate`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16Transfer
open HRS HRS.Whole HRS.Whole.AppendixA

def closedTensor (d k : ℕ) (p : ℝ) [Fact (2 ≤ p)] (G : WmpSpace d k p)
    (j : Fin (k+1)) (x : Euc d) : (Fin j → Fin d) → ℝ :=
  fun idx => ((G : WLp d k p) : Euc d → WIndex d k → ℝ) x ⟨j,idx⟩

def jetEnergy (d k : ℕ) (p : ℝ) [Fact (2 ≤ p)] (G : WmpSpace d k p) : ℝ :=
  ∑ j : Fin (k+1), ∫ x, vnorm (closedTensor d k p G j x)^p

def jetNorm (d k : ℕ) (p : ℝ) [Fact (2 ≤ p)] (G : WmpSpace d k p) : ℝ :=
  (jetEnergy d k p G)^(1/p)

def closedPairDensity (d k : ℕ) (p : ℝ) [Fact (2 ≤ p)]
    (G H : WmpSpace d k p) (x : Euc d) : ℝ :=
  ∑ j : Fin (k+1), vnorm (closedTensor d k p G j x)^(p-2)*
    ∑ idx : Fin j → Fin d, closedTensor d k p G j x idx*closedTensor d k p H j x idx

structure IsSmoothNorm {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (p : ℝ) (N : X → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ N x
  zero : ∀ x, N x=0 ↔ x=0
  smul : ∀ a : ℝ, ∀ x, N (a • x) = |a| * N x
  add : ∀ x y, N (x+y) ≤ N x+N y
  equivalent : ∃ c C : ℝ, 0<c ∧ 0<C ∧ ∀ x, c*‖x‖ ≤ N x ∧ N x ≤ C*‖x‖
  differentiable : Differentiable ℝ (fun x => (N x)^p)
  cont_deriv : Continuous (fderiv ℝ (fun x => (N x)^p))

def PositiveLpMatrix {d : ℕ} (p : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  (∃ lam : ℝ, 0 ≤ lam ∧ M=-(lam • 1)) ∨
    (p=2 ∧ ∃ lam : ℝ, 0 ≤ lam ∧ ∃ A : Matrix (Fin d) (Fin d) ℝ,
      A.transpose = -A ∧ M=-(lam • 1)+A)

def cutoffRadius (n : ℕ) : ℝ := ((n : ℝ)+1)⁻¹
def cutoffRate (d : ℕ) (s : ℝ) (n : ℕ) : ℝ := cutoffRadius n^((d : ℝ)-s)

end HRS.Whole.AppendixA.Phase2SA16Transfer
