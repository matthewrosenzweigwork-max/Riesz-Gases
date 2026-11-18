import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.S67NlBD55
import HRS.MS.S67NlBD56
import HRS.MS.S67NlBD57A
import HRS.MS.S67NlBD57D
import HRS.MS.S67NlBD57E

/-!
# S6.7 nonlinear breakdown, packet 57: commutator bound

Namespace `HRS.MS.BreakdownS67`, helper prefix `s67bd_`. TeX S:4842-4851 (finiteness
prerequisite), nonlinear part of `S:W:lem:r2mov-global-adjoint`. No owned definitions.
The bound is the `q = 0` bounded commutator (57E) plus the exact affine shift residual (57D).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

theorem s67bd_commutator_bound (d n : ℕ) (hn : 1 ≤ n) (q Mb : ℝ) (hMb : 0 ≤ Mb) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A MJ : ℝ, 0 ≤ A → 0 ≤ MJ →
      ∀ (B : Euc d → Euc d) (J u : Euc d → ℝ),
      ContDiff ℝ (n : WithTop ℕ∞) B →
      (∀ i ≤ n, ∀ x, ‖iteratedFDeriv ℝ i B x‖ ≤ Mb) →
      ContDiff ℝ (n : WithTop ℕ∞) J →
      (∀ i ≤ n, ∀ x, ‖iteratedFDeriv ℝ i J x‖ ≤ MJ) →
      ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) u →
      (∀ i < n, ∀ x, ‖iteratedFDeriv ℝ i (fun y => gradient u y) x‖ ≤ A) →
      ∀ (h : Fin n → ℝ) (e : Fin n → Euc d),
      (∀ i, h i ≠ 0) → (∀ i, ‖e i‖ = 1) → ∀ x,
        |s67bd_commutator q n h e B J u x| ≤ C * (A + MJ) := by
  obtain ⟨Cb, hCb, hb⟩ := s67bd_bounded_commutator d n hn Mb hMb
  refine ⟨Cb + |q| * (n : ℝ), by positivity, ?_⟩
  intro A MJ hA hMJ B J u hB hBb hJ hJb hu hlower h e hh he x
  have ha := s67bd_affine_commutator d n hn q A hA h e hh he B J u hu hlower
  calc |s67bd_commutator q n h e B J u x|
      ≤ |s67bd_commutator 0 n h e B J u x| +
        |q * ∑ k : Fin n, inner ℝ (e k)
          (s67bd_subsetDiff n h e (Finset.univ.erase k)
            (fun y => gradient u y) (x + h k • e k))| := by
        rw [ha.1 x]
        exact abs_sub _ _
    _ ≤ Cb * (A + MJ) + |q| * (n : ℝ) * A :=
      add_le_add (hb A MJ hA hMJ B J u hB hBb hJ hJb hu hlower h e hh he x) (ha.2 x)
    _ ≤ (Cb + |q| * (n : ℝ)) * (A + MJ) := by
      nlinarith [mul_nonneg (mul_nonneg (abs_nonneg q) (Nat.cast_nonneg n)) hMJ]

end HRS.MS.BreakdownS67
