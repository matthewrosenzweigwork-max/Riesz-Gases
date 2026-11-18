import HRS.MS.ProClosureS111WeightedDensity
import HRS.MS.ProClosureS111DenseHilbertBasis
import Mathlib.MeasureTheory.Measure.SeparableMeasure

/-!
The exact weighted completion is the closed range-span of its finite jet
map in L2. Every finite-norm weighted test maps into it, and actual compact
smooth tests have dense image. Nonzero bumps with separated centers prove
infinite dimensionality without assuming a basis or a chart.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.FixEq

variable {d r : ℕ} {Pw : ℝ}

theorem weightedJetMap_injective : Function.Injective (weightedJetMap d r Pw) := by
  intro f g hfg
  have hn : (weightedSobolevE r Pw
      ((f - g : weightedTestSubmodule d r Pw) : Euc d → ℝ)).toReal = 0 := by
    rw [← weightedJetMap_norm, map_sub, hfg, sub_self, norm_zero]
  have hfin := (weightedTestSubmodule_iff.1 (f - g).property).2
  have hzero : weightedSobolevE r Pw
      ((f - g : weightedTestSubmodule d r Pw) : Euc d → ℝ) = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff _).1 hn with h | h
    · exact h
    · exact (hfin.ne h).elim
  have he := s57p_E_zero (f - g).property.1 hzero
  apply Subtype.ext
  exact sub_eq_zero.1 he

abbrev weightedCompletionSubmodule (d r : ℕ) (Pw : ℝ) :
    Submodule ℝ (WeightedJetHilbert d r) :=
  (weightedJetMap d r Pw).range.topologicalClosure

abbrev WeightedCompletion (d r : ℕ) (Pw : ℝ) : Type :=
  ↥(weightedCompletionSubmodule d r Pw)

def weightedCompletionMap (d r : ℕ) (Pw : ℝ) :
    weightedTestSubmodule d r Pw →ₗ[ℝ] WeightedCompletion d r Pw :=
  (weightedJetMap d r Pw).codRestrict (weightedCompletionSubmodule d r Pw)
    (fun f => (LinearMap.range (weightedJetMap d r Pw)).le_topologicalClosure ⟨f, rfl⟩)

theorem weightedCompletionMap_injective :
    Function.Injective (weightedCompletionMap d r Pw) := by
  intro f g h
  exact weightedJetMap_injective (congrArg Subtype.val h)

theorem weightedCompletionMap_norm (f : weightedTestSubmodule d r Pw) :
    ‖weightedCompletionMap d r Pw f‖ = (weightedSobolevE r Pw (f : Euc d → ℝ)).toReal :=
  weightedJetMap_norm f

theorem weightedCompletionMap_dense : DenseRange (weightedCompletionMap d r Pw) := by
  refine Metric.denseRange_iff.2 fun x eps heps => ?_
  obtain ⟨y, hy, hxy⟩ := Metric.mem_closure_iff.1 x.property eps heps
  obtain ⟨f, rfl⟩ := hy
  exact ⟨f, hxy⟩

def compactSmoothSubmodule (d : ℕ) : Submodule ℝ (Euc d → ℝ) where
  carrier := {f | IsR2Test f}
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero⟩
  add_mem' := fun hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' := fun c f hf => ⟨hf.1.const_smul c, hf.2.smul_left⟩

def compactWeightedMap (hP : (d : ℝ) < 2 * Pw) :
    compactSmoothSubmodule d →ₗ[ℝ] weightedTestSubmodule d r Pw where
  toFun f := ⟨f, weighted_test_of_compact_smooth hP f.property⟩
  map_add' := fun _ _ => rfl
  map_smul' := fun _ _ => rfl

def compactCompletionMap (hP : (d : ℝ) < 2 * Pw) :
    compactSmoothSubmodule d →ₗ[ℝ] WeightedCompletion d r Pw :=
  (weightedCompletionMap d r Pw).comp (compactWeightedMap hP)

def compactCompletionSubmodule (hP : (d : ℝ) < 2 * Pw) :
    Submodule ℝ (WeightedCompletion d r Pw) := (compactCompletionMap hP).range

theorem compactCompletion_dense (hP : (d : ℝ) < 2 * Pw) :
    Dense (compactCompletionSubmodule (r := r) hP : Set (WeightedCompletion d r Pw)) := by
  have hcontains : Set.range (weightedCompletionMap d r Pw) ⊆
      closure (compactCompletionSubmodule (r := r) hP : Set (WeightedCompletion d r Pw)) := by
    rintro _ ⟨f, rfl⟩
    obtain ⟨g, hg, ht⟩ := weighted_smooth_approximation hP f
    have ht' : Tendsto (fun n => weightedCompletionMap d r Pw (g n)) atTop
        (𝓝 (weightedCompletionMap d r Pw f)) := tendsto_subtype_rng.2 ht
    apply mem_closure_of_tendsto ht'
    exact Eventually.of_forall fun n => ⟨⟨g n, hg n⟩, rfl⟩
  intro x
  exact closure_minimal hcontains isClosed_closure (weightedCompletionMap_dense x)

/-- A concrete infinite linearly independent family of compact smooth
functions, obtained from bumps equal to delta functions at their centers. -/
theorem compact_smooth_infinite_independent (hd : 0 < d) :
    ∃ f : ℕ → Euc d → ℝ, (∀ n, IsR2Test (f n)) ∧ LinearIndependent ℝ f := by
  let i0 : Fin d := ⟨0, hd⟩
  let c : ℕ → Euc d := fun n => EuclideanSpace.single i0 (3 * (n : ℝ))
  let b : ℕ → Euc d → ℝ := fun n =>
    (⟨(1 / 2 : ℝ), 1, by norm_num, by norm_num⟩ : ContDiffBump (c n))
  have hsep : ∀ n m : ℕ, n ≠ m → 1 ≤ dist (c n) (c m) := by
    intro n m hnm
    have hcoord := PiLp.dist_apply_le (c n) (c m) i0
    have he : dist ((c n) i0) ((c m) i0) = |3 * (n : ℝ) - 3 * (m : ℝ)| := by
      simp [c, Real.dist_eq]
    rw [he] at hcoord
    apply le_trans _ hcoord
    rcases lt_or_gt_of_ne hnm with hlt | hgt
    · have hc : (n : ℝ) + 1 ≤ m := by exact_mod_cast Nat.succ_le_of_lt hlt
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hc : (m : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hgt
      rw [abs_of_nonneg (by linarith)]
      linarith
  have hdelta : ∀ m n, b m (c n) = if m = n then 1 else 0 := by
    intro m n
    by_cases hmn : m = n
    · subst m
      rw [if_pos rfl]
      exact (show ContDiffBump (c n) from
        ⟨(1 / 2 : ℝ), 1, by norm_num, by norm_num⟩).one_of_mem_closedBall (by simp)
    · rw [if_neg hmn]
      exact (show ContDiffBump (c m) from
        ⟨(1 / 2 : ℝ), 1, by norm_num, by norm_num⟩).zero_of_le_dist
          (hsep n m (fun h => hmn h.symm))
  refine ⟨b, fun n => ?_, ?_⟩
  · exact ⟨(show ContDiffBump (c n) from
      ⟨(1 / 2 : ℝ), 1, by norm_num, by norm_num⟩).contDiff,
      (show ContDiffBump (c n) from
      ⟨(1 / 2 : ℝ), 1, by norm_num, by norm_num⟩).hasCompactSupport⟩
  · refine linearIndependent_iff'.2 fun S a ha n hn => ?_
    have h := congrFun ha (c n)
    simpa [Finset.sum_apply, Pi.smul_apply, hdelta, hn] using h

theorem weightedCompletion_infinite_dimensional (hd : 0 < d)
    (hP : (d : ℝ) < 2 * Pw) : ¬ FiniteDimensional ℝ (WeightedCompletion d r Pw) := by
  intro hfin
  letI := hfin
  obtain ⟨b, hb, hli⟩ := compact_smooth_infinite_independent hd
  let v : ℕ → weightedTestSubmodule d r Pw :=
    fun n => ⟨b n, weighted_test_of_compact_smooth hP (hb n)⟩
  have hv : LinearIndependent ℝ v :=
    LinearIndependent.of_comp (weightedTestSubmodule d r Pw).subtype hli
  have hw : LinearIndependent ℝ (weightedCompletionMap d r Pw ∘ v) :=
    hv.map' (weightedCompletionMap d r Pw)
      (LinearMap.ker_eq_bot.2 weightedCompletionMap_injective)
  have hN := (hw.comp
    (fun n : Fin (Module.finrank ℝ (WeightedCompletion d r Pw) + 1) => (n : ℕ))
    Fin.val_injective).fintype_card_le_finrank
  simp only [Fintype.card_fin] at hN
  omega

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.compactCompletion_dense
#print axioms HRS.MS.ProClosureS111.weightedCompletion_infinite_dimensional

