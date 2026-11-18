import HRS.MS.ProClosureS111ChartMeas
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Algebra.BigOperators.Fin

/-!
The exact frozen weighted Sobolev norm is realized by the finite vector
of weighted spatial jets in a genuine L2 Hilbert space. This includes
every C^r function of finite frozen norm, not just bounded jets.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.FixEq

abbrev WeightedJetIndex (d r : ℕ) := Σ j : Fin (r + 1), Fin (j : ℕ) → Fin d

abbrev WeightedJetVector (d r : ℕ) := EuclideanSpace ℝ (WeightedJetIndex d r)

abbrev WeightedJetHilbert (d r : ℕ) :=
  Lp (WeightedJetVector d r) 2 (volume : Measure (Euc d))

def weightedJets {d : ℕ} (r : ℕ) (Pw : ℝ) (f : Euc d → ℝ)
    (x : Euc d) : WeightedJetVector d r :=
  WithLp.toLp 2 (fun p : WeightedJetIndex d r =>
    jbracket x ^ (-Pw) * partialDeriv p.2 f x)

variable {d r : ℕ} {Pw : ℝ}

theorem weightedJets_continuous {f : Euc d → ℝ} (hf : ContDiff ℝ r f) :
    Continuous (weightedJets r Pw f) := by
  have hw : Continuous (fun x : Euc d => jbracket x ^ (-Pw)) := by
    apply Continuous.rpow_const
    · unfold jbracket
      fun_prop
    · intro x
      exact Or.inl (s57p_jbracket_pos x).ne'
  apply (PiLp.continuous_toLp 2 _).comp
  refine continuous_pi fun p => ?_
  exact hw.mul (s57p_partialDeriv_contDiff hf 0
    (by have hp := p.1.isLt; omega) p.2).continuous

theorem weightedJets_norm_sq (f : Euc d → ℝ) (x : Euc d) :
    ‖weightedJets r Pw f x‖ ^ 2 =
      ∑ p : WeightedJetIndex d r,
        jbracket x ^ (-2 * Pw) * (partialDeriv p.2 f x) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  refine Finset.sum_congr rfl fun p _ => ?_
  change (jbracket x ^ (-Pw) * partialDeriv p.2 f x) ^ 2 = _
  rw [mul_pow]
  have hw : (jbracket x ^ (-Pw)) ^ 2 = jbracket x ^ (-2 * Pw) := by
    rw [← Real.rpow_two, ← Real.rpow_mul (s57p_jbracket_pos x).le]
    congr 1
    ring
  rw [hw]

theorem weightedJets_enorm_sq (f : Euc d → ℝ) (x : Euc d) :
    ‖weightedJets r Pw f x‖ₑ ^ (2 : ℝ) =
      ∑ p : WeightedJetIndex d r,
        ENNReal.ofReal (jbracket x ^ (-2 * Pw) * (partialDeriv p.2 f x) ^ 2) := by
  calc
    _ = ENNReal.ofReal (‖weightedJets r Pw f x‖ ^ 2) := by
      rw [← ofReal_norm_eq_enorm]
      exact (ENNReal.rpow_natCast _ 2).trans
        (ENNReal.ofReal_pow (norm_nonneg _) 2).symm
    _ = _ := by
      rw [weightedJets_norm_sq]
      exact ENNReal.ofReal_sum_of_nonneg fun p _ =>
        mul_nonneg (Real.rpow_nonneg (s57p_jbracket_pos x).le _) (sq_nonneg _)

/-- The finite ordered-derivative definition of the frozen norm agrees
exactly with the Bochner L2 norm of the weighted jet vector. -/
theorem weightedJets_eLpNorm {f : Euc d → ℝ} (hf : ContDiff ℝ r f) :
    eLpNorm (weightedJets r Pw f) 2 volume = weightedSobolevE r Pw f := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)
    (weightedJets_continuous hf).aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat]
  unfold weightedSobolevE
  congr 1
  simp_rw [weightedJets_enorm_sq]
  rw [lintegral_finsetSum]
  · rw [Fintype.sum_sigma]
    exact Fin.sum_univ_eq_sum_range
      (fun j : ℕ => ∑ i : Fin j → Fin d,
        ∫⁻ x : Euc d, ENNReal.ofReal
          (jbracket x ^ (-2 * Pw) * (partialDeriv i f x) ^ 2)) (r + 1)
  · intro p _
    have hw : Continuous (fun x : Euc d => jbracket x ^ (-2 * Pw)) := by
      apply Continuous.rpow_const
      · unfold jbracket
        fun_prop
      · intro x
        exact Or.inl (s57p_jbracket_pos x).ne'
    exact (hw.measurable.mul
      ((s57p_partialDeriv_contDiff hf 0
        (by have hp := p.1.isLt; omega) p.2).continuous.measurable.pow_const 2)).ennreal_ofReal

theorem weightedJets_memLp_iff {f : Euc d → ℝ} (hf : ContDiff ℝ r f) :
    MemLp (weightedJets r Pw f) 2 volume ↔ weightedSobolevE r Pw f < ⊤ := by
  constructor
  · intro h
    simpa only [weightedJets_eLpNorm hf] using h.eLpNorm_lt_top
  · intro h
    change eLpNorm (weightedJets r Pw f) 2 volume < ⊤
    rw [weightedJets_eLpNorm hf]
    exact h

theorem weightedJets_add {f g : Euc d → ℝ}
    (hf : ContDiff ℝ r f) (hg : ContDiff ℝ r g) :
    weightedJets r Pw (f + g) = weightedJets r Pw f + weightedJets r Pw g := by
  funext x
  ext p
  change jbracket x ^ (-Pw) * partialDeriv p.2 (f + g) x =
    jbracket x ^ (-Pw) * partialDeriv p.2 f x +
      jbracket x ^ (-Pw) * partialDeriv p.2 g x
  have hp : (p.1 : ℕ) ≤ r := Nat.lt_succ_iff.1 p.1.isLt
  unfold partialDeriv
  rw [iteratedFDeriv_add_apply
    (hf.of_le (by exact_mod_cast hp)).contDiffAt
    (hg.of_le (by exact_mod_cast hp)).contDiffAt,
    ContinuousMultilinearMap.add_apply]
  ring

theorem weightedJets_smul (c : ℝ) {f : Euc d → ℝ}
    (hf : ContDiff ℝ r f) :
    weightedJets r Pw (c • f) = c • weightedJets r Pw f := by
  funext x
  ext p
  change jbracket x ^ (-Pw) * partialDeriv p.2 (c • f) x =
    c * (jbracket x ^ (-Pw) * partialDeriv p.2 f x)
  have hp : (p.1 : ℕ) ≤ r := Nat.lt_succ_iff.1 p.1.isLt
  unfold partialDeriv
  rw [iteratedFDeriv_const_smul_apply
    (a := c) (i := (p.1 : ℕ)) (f := f)
    (hf.of_le (by exact_mod_cast hp)).contDiffAt,
    ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring

theorem weightedJets_zero : weightedJets r Pw (0 : Euc d → ℝ) = 0 := by
  have h := weightedJets_smul (r := r) (Pw := Pw) (0 : ℝ)
    (f := (0 : Euc d → ℝ)) contDiff_const
  simpa only [zero_smul] using h

def weightedTestSubmodule (d r : ℕ) (Pw : ℝ) : Submodule ℝ (Euc d → ℝ) where
  carrier := {f | ContDiff ℝ r f ∧ MemLp (weightedJets r Pw f) 2 volume}
  zero_mem' := ⟨contDiff_const, by rw [weightedJets_zero]; exact MemLp.zero⟩
  add_mem' := by
    intro f g hf hg
    refine ⟨hf.1.add hg.1, ?_⟩
    rw [weightedJets_add hf.1 hg.1]
    exact hf.2.add hg.2
  smul_mem' := by
    intro c f hf
    refine ⟨hf.1.const_smul c, ?_⟩
    rw [weightedJets_smul c hf.1]
    exact hf.2.const_smul c

theorem weightedTestSubmodule_iff {f : Euc d → ℝ} :
    f ∈ weightedTestSubmodule d r Pw ↔ IsR2WeightedTest r Pw f := by
  constructor
  · intro h
    exact ⟨h.1, (weightedJets_memLp_iff h.1).1 h.2⟩
  · intro h
    exact ⟨h.1, (weightedJets_memLp_iff h.1).2 h.2⟩

/-- The actual linear map of all finite-norm weighted tests into L2. -/
def weightedJetMap (d r : ℕ) (Pw : ℝ) :
    weightedTestSubmodule d r Pw →ₗ[ℝ] WeightedJetHilbert d r where
  toFun f := f.property.2.toLp (weightedJets r Pw f)
  map_add' f g := by
    exact (MemLp.toLp_congr (f + g).property.2
      (f.property.2.add g.property.2)
      (Filter.Eventually.of_forall fun x =>
        congrFun (weightedJets_add f.property.1 g.property.1) x)).trans
      (MemLp.toLp_add f.property.2 g.property.2)
  map_smul' c f := by
    exact (MemLp.toLp_congr (c • f).property.2
      (f.property.2.const_smul c)
      (Filter.Eventually.of_forall fun x =>
        congrFun (weightedJets_smul c f.property.1) x)).trans
      (MemLp.toLp_const_smul c f.property.2)

theorem weightedJetMap_norm (f : weightedTestSubmodule d r Pw) :
    ‖weightedJetMap d r Pw f‖ = (weightedSobolevE r Pw (f : Euc d → ℝ)).toReal := by
  dsimp only [weightedJetMap, LinearMap.coe_mk, AddHom.coe_mk]
  exact (Lp.norm_toLp _ f.property.2).trans
    (congrArg ENNReal.toReal (weightedJets_eLpNorm f.property.1))

/-- Compactly supported smooth tests are genuine finite-norm weighted
tests whenever the weight is integrable. -/
theorem weighted_test_of_compact_smooth (hP : (d : ℝ) < 2 * Pw)
    {f : Euc d → ℝ} (hf : IsR2Test f) :
    f ∈ weightedTestSubmodule d r Pw :=
  weightedTestSubmodule_iff.2 (chart_weighted_of_memCb hP (chart_memCb_of_test hf))

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.weightedJets_eLpNorm
#print axioms HRS.MS.ProClosureS111.weightedJetMap_norm

