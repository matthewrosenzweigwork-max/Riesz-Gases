import HRS.Whole.Window

/-!
# S21G2 W00 -- concrete weighted jet space, its test closure, the weighted field and strong field (R26-T3.W00)

Definitions only (no `sorry` in the original contract; nothing to prove).  Checked: the contract elaborates against the
integration tree.  Copied verbatim except for the header, the `open scoped` list (`ContDiff` makes `ω` a notation token) and one elaboration
repair: `r26t3_jetfun` needs `WithLp.toLp 2` because `EuclideanSpace` is a `WithLp` structure type at this pin.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R26T3
open HRS HRS.Whole

abbrev JetIndex (d r : ℕ) := (j : Fin (r+1)) × (Fin j.val → Fin d)
def r26t3_weightMeasure (d : ℕ) (P : ℝ) : Measure (Euc d) :=
  volume.withDensity (fun x => ENNReal.ofReal (jbracket x^(-2*P)))
abbrev JetSpace (d r : ℕ) (P : ℝ) := Lp (EuclideanSpace ℝ (JetIndex d r)) 2 (r26t3_weightMeasure d P)
def r26t3_jetfun {d : ℕ} (r : ℕ) (f : Euc d → ℝ) (x : Euc d) : EuclideanSpace ℝ (JetIndex d r) :=
  WithLp.toLp 2 fun i : JetIndex d r => partialDeriv i.2 f x
open Classical in
def r26t3_jet {d : ℕ} (r : ℕ) (P : ℝ) (f : Euc d → ℝ) : JetSpace d r P :=
  if h : MemLp (r26t3_jetfun r f) 2 (r26t3_weightMeasure d P) then h.toLp (r26t3_jetfun r f) else 0
def r26t3_testClosure (d r : ℕ) (P : ℝ) : Submodule ℝ (JetSpace d r P) :=
  (Submodule.span ℝ {z | ∃ f : Euc d → ℝ, IsR2Test f ∧ z=r26t3_jet r P f}).topologicalClosure
abbrev TestE (d r : ℕ) (P : ℝ) := r26t3_testClosure d r P
abbrev FieldF (d r : ℕ) (P : ℝ) := StrongDual ℝ (TestE d r P)
open Classical in
def r26t3_test {d : ℕ} (r : ℕ) (P : ℝ) (f : Euc d → ℝ) : TestE d r P :=
  if h : r26t3_jet r P f ∈ r26t3_testClosure d r P then ⟨r26t3_jet r P f,h⟩ else 0
def r26t3_r (d : ℕ) : ℕ := 2*d+8
def r26t3_P (d : ℕ) : ℝ := d+2
abbrev Field (d : ℕ) := FieldF d (r26t3_r d) (r26t3_P d)
abbrev StrongField (d : ℕ) := FieldF d (r26t3_r d-2) (r26t3_P d+2)
def r26t3_eval {d r : ℕ} {P : ℝ} (z : FieldF d r P) (f : Euc d → ℝ) : ℝ := z (r26t3_test r P f)

end HRS.MS.R26T3
