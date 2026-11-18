import HRS.MS.ProClosureS111WeightedCompletion
import HRS.MS.R26T6CD01

/-!
An actual weighted chart at the exact frozen normalization. Compactly
supported smooth tests are dense in the finite weighted-jet completion;
Gram--Schmidt within this dense subspace supplies compact smooth basis
tests. The Hilbert-basis coordinate isometry gives the chart on every
finite-norm weighted test, with no additional bounded-jet hypothesis.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.R26T6

variable {d r : ℕ} {Pw : ℝ}

/-- The full frozen weighted chart exists from its dimension and weight
conditions alone. The coordinate norm is the original ordered-jet norm,
and every coordinate vector is represented by an actual compact smooth
test, rather than only an element of a completion. -/
theorem physical_weighted_chart (hd : 0 < d) (hP : (d : ℝ) < 2 * Pw) :
    Nonempty (r26t6_WeightedChart d r Pw) := by
  obtain ⟨b, hb⟩ := hilbert_basis_in_dense_submodule
    (compactCompletionSubmodule (r := r) hP) (compactCompletion_dense hP)
    (weightedCompletion_infinite_dimensional hd hP)
  have hpre : ∀ n : ℕ, ∃ f : compactSmoothSubmodule d,
      compactCompletionMap (r := r) hP f = b n := hb
  choose f hf using hpre
  let enc : (Euc d → ℝ) → r26t6_Coeff := fun phi =>
    if hphi : IsR2WeightedTest r Pw phi then
      b.repr (weightedCompletionMap d r Pw
        ⟨phi, weightedTestSubmodule_iff.2 hphi⟩)
    else 0
  have henc : ∀ g : weightedTestSubmodule d r Pw,
      enc (g : Euc d → ℝ) = b.repr (weightedCompletionMap d r Pw g) := by
    intro g
    simp only [enc, dif_pos (weightedTestSubmodule_iff.1 g.property)]
  have htest : ∀ n, enc (f n : Euc d → ℝ) = b.repr (b n) := by
    intro n
    change enc ((compactWeightedMap (r := r) hP (f n)) : Euc d → ℝ) = _
    rw [henc]
    change b.repr (compactCompletionMap hP (f n)) = _
    rw [hf n]
  have hD : DenseRange (compactCompletionMap (r := r) hP) :=
    compactCompletion_dense hP
  refine ⟨{
    encode := enc
    test := fun n => f n
    add := ?_
    smul := ?_
    norm := ?_
    test_smooth := fun n => (f n).property
    test_coord := ?_
    dense := ?_
  }⟩
  · intro phi psi hphi hpsi
    let p : weightedTestSubmodule d r Pw :=
      ⟨phi, weightedTestSubmodule_iff.2 hphi⟩
    let q : weightedTestSubmodule d r Pw :=
      ⟨psi, weightedTestSubmodule_iff.2 hpsi⟩
    change enc ((p + q : weightedTestSubmodule d r Pw) : Euc d → ℝ) =
      enc (p : Euc d → ℝ) + enc (q : Euc d → ℝ)
    simp only [henc, map_add]
  · intro c phi hphi
    let p : weightedTestSubmodule d r Pw :=
      ⟨phi, weightedTestSubmodule_iff.2 hphi⟩
    change enc ((c • p : weightedTestSubmodule d r Pw) : Euc d → ℝ) =
      c • enc (p : Euc d → ℝ)
    simp only [henc, map_smul]
  · intro phi hphi
    let p : weightedTestSubmodule d r Pw :=
      ⟨phi, weightedTestSubmodule_iff.2 hphi⟩
    change ‖enc (p : Euc d → ℝ)‖ = (weightedSobolevE r Pw (p : Euc d → ℝ)).toReal
    rw [henc, b.repr.norm_map, weightedCompletionMap_norm]
  · intro i j
    rw [htest, b.repr_self]
    simp [lp.single_apply, Pi.single_apply, eq_comm]
  · change DenseRange (fun g : {g : Euc d → ℝ // IsR2Test g} => enc g)
    refine Metric.denseRange_iff.2 fun z eps heps => ?_
    obtain ⟨g, hg⟩ := Metric.denseRange_iff.1 hD (b.repr.symm z) eps heps
    refine ⟨⟨g, g.property⟩, ?_⟩
    change dist z (enc ((compactWeightedMap (r := r) hP g) : Euc d → ℝ)) < eps
    rw [henc]
    change dist z (b.repr (compactCompletionMap hP g)) < eps
    calc
      _ = dist (b.repr.symm z) (compactCompletionMap hP g) := by
        simpa only [LinearIsometryEquiv.apply_symm_apply] using
          b.repr.dist_map (b.repr.symm z) (compactCompletionMap hP g)
      _ < eps := hg

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.physical_weighted_chart

