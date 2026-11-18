import HRS.MS.ProClosureS111WeightedEvaluation
import HRS.MS.ProClosureS111WeightedCompletion
import HRS.MS.R26T6CD01

/-!
The actual value and spatial-jet trace bounds for every frozen weighted
chart. Finite-combination duality proves Bessel's inequality directly from
the chart's exact norm and coordinate axioms. In particular no trace or
Gaussian field bound is a premise of the physical result.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.FixEq

variable {d r : ℕ} {Pw : ℝ}

def compactFrozenEncode (E : r26t6_WeightedChart d r Pw)
    (hP : (d : ℝ) < 2 * Pw) : compactSmoothSubmodule d →ₗ[ℝ] r26t6_Coeff where
  toFun f := E.encode f
  map_add' f g := E.add _ _
    (weightedTestSubmodule_iff.1 (weighted_test_of_compact_smooth hP f.property))
    (weightedTestSubmodule_iff.1 (weighted_test_of_compact_smooth hP g.property))
  map_smul' c f := E.smul c f
    (weightedTestSubmodule_iff.1 (weighted_test_of_compact_smooth hP f.property))

theorem compactFrozenEncode_norm (E : r26t6_WeightedChart d r Pw)
    (hP : (d : ℝ) < 2 * Pw) (f : compactSmoothSubmodule d) :
    ‖compactFrozenEncode E hP f‖ =
      (weightedSobolevE r Pw (f : Euc d → ℝ)).toReal :=
  E.norm (f : Euc d → ℝ)
    (weightedTestSubmodule_iff.1 (weighted_test_of_compact_smooth hP f.property))

def frozenChartTest (E : r26t6_WeightedChart d r Pw) (i : ℕ) :
    compactSmoothSubmodule d := ⟨E.test i, E.test_smooth i⟩

theorem frozenChartTest_orthonormal (E : r26t6_WeightedChart d r Pw)
    (hP : (d : ℝ) < 2 * Pw) :
    Orthonormal ℝ (fun i => compactFrozenEncode E hP (frozenChartTest E i)) := by
  let b : HilbertBasis ℕ ℝ r26t6_Coeff :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℝ r26t6_Coeff)
  have he : ∀ i, compactFrozenEncode E hP (frozenChartTest E i) = b i := by
    intro i
    apply b.repr.injective
    rw [b.repr_self]
    ext j
    change E.encode (E.test i) j =
      (lp.single 2 i (1 : ℝ) : r26t6_Coeff) j
    rw [E.test_coord]
    simp [lp.single_apply, Pi.single_apply, eq_comm]
  simpa only [he] using b.orthonormal

theorem orthonormal_finset_norm_sq {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] (b : ℕ → V) (hb : Orthonormal ℝ b)
    (c : ℕ → ℝ) (S : Finset ℕ) :
    ‖∑ i ∈ S, c i • b i‖ ^ 2 = ∑ i ∈ S, c i ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, sum_inner]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [inner_sum]
  simp only [real_inner_smul_left, real_inner_smul_right,
    orthonormal_iff_ite.1 hb]
  simp [Finset.sum_ite_eq, hi, pow_two]

/-- Bessel's inequality for any bounded linear observation of compact
smooth tests, stated using the frozen chart itself. -/
theorem frozen_chart_functional_trace (E : r26t6_WeightedChart d r Pw)
    (hP : (d : ℝ) < 2 * Pw) (ell : compactSmoothSubmodule d →ₗ[ℝ] ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ f, |ell f| ≤ K * ‖compactFrozenEncode E hP f‖) :
    Summable (fun i => ell (frozenChartTest E i) ^ 2) ∧
      (∑' i, ell (frozenChartTest E i) ^ 2) ≤ K ^ 2 := by
  let c : ℕ → ℝ := fun i => ell (frozenChartTest E i)
  have hfinite : ∀ S : Finset ℕ, (∑ i ∈ S, c i ^ 2) ≤ K ^ 2 := by
    intro S
    let f : compactSmoothSubmodule d := ∑ i ∈ S, c i • frozenChartTest E i
    have hell : ell f = ∑ i ∈ S, c i ^ 2 := by
      simp only [f, map_sum, map_smul, smul_eq_mul, c, pow_two]
    have hnorm : ‖compactFrozenEncode E hP f‖ ^ 2 = ∑ i ∈ S, c i ^ 2 := by
      simp only [f, map_sum, map_smul]
      exact orthonormal_finset_norm_sq _ (frozenChartTest_orthonormal E hP) c S
    have hpos : 0 ≤ ∑ i ∈ S, c i ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    have he := hbound f
    rw [hell, abs_of_nonneg hpos, ← hnorm] at he
    have hn : ‖compactFrozenEncode E hP f‖ ≤ K := by
      by_contra! hlt
      have ha : 0 < ‖compactFrozenEncode E hP f‖ := hK.trans_lt hlt
      have hm := mul_lt_mul_of_pos_right hlt ha
      nlinarith
    rw [← hnorm]
    exact pow_le_pow_left₀ (norm_nonneg _) hn 2
  exact ⟨summable_of_sum_le (fun _ => sq_nonneg _) hfinite,
    Real.tsum_le_of_sum_le (fun _ => sq_nonneg _) hfinite⟩

def compactPartialEvaluation (j : ℕ) (i : Fin j → Fin d) (x : Euc d) :
    compactSmoothSubmodule d →ₗ[ℝ] ℝ where
  toFun f := partialDeriv i f x
  map_add' f g := by
    unfold partialDeriv
    change iteratedFDeriv ℝ j
        ((f : Euc d → ℝ) + (g : Euc d → ℝ)) x
        (fun l => EuclideanSpace.single (i l) 1) =
      iteratedFDeriv ℝ j (f : Euc d → ℝ) x
          (fun l => EuclideanSpace.single (i l) 1) +
        iteratedFDeriv ℝ j (g : Euc d → ℝ) x
          (fun l => EuclideanSpace.single (i l) 1)
    rw [iteratedFDeriv_add_apply
      (f.property.1.of_le (by exact_mod_cast le_top)).contDiffAt
      (g.property.1.of_le (by exact_mod_cast le_top)).contDiffAt,
      ContinuousMultilinearMap.add_apply]
  map_smul' c f := by
    unfold partialDeriv
    change iteratedFDeriv ℝ j
        (c • (f : Euc d → ℝ)) x
        (fun l => EuclideanSpace.single (i l) 1) =
      c • iteratedFDeriv ℝ j (f : Euc d → ℝ) x
        (fun l => EuclideanSpace.single (i l) 1)
    rw [iteratedFDeriv_const_smul_apply
      (a := c) (i := j) (f := (f : Euc d → ℝ))
      (f.property.1.of_le (by exact_mod_cast le_top)).contDiffAt,
      ContinuousMultilinearMap.smul_apply]

/-- Uniform trace bounds for every scalar entry of the value, gradient,
and Hessian evaluations of the chart basis. -/
theorem physical_chart_partial_trace (d r : ℕ) (Pw : ℝ)
    (hr : (2 : ℝ) + (d : ℝ) / 2 < r) (hP : (d : ℝ) < 2 * Pw) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E : r26t6_WeightedChart d r Pw,
      ∀ j ≤ 2, ∀ i : Fin j → Fin d, ∀ x,
        Summable (fun n => (partialDeriv i (E.test n) x) ^ 2) ∧
        (∑' n, (partialDeriv i (E.test n) x) ^ 2) ≤
          C ^ 2 * jbracket x ^ (2 * Pw) := by
  obtain ⟨C, hC, hbound⟩ := weighted_test_jet_evaluation d r Pw hr hP
  refine ⟨C, hC, fun E j hj i x => ?_⟩
  have hK : 0 ≤ C * jbracket x ^ Pw :=
    mul_nonneg hC (Real.rpow_nonneg (s57p_jbracket_pos x).le _)
  have hb : ∀ f : compactSmoothSubmodule d,
      |compactPartialEvaluation j i x f| ≤
        (C * jbracket x ^ Pw) * ‖compactFrozenEncode E hP f‖ := by
    intro f
    change |partialDeriv i f x| ≤ _
    rw [compactFrozenEncode_norm]
    exact (u2_partial_le j i x).trans (hbound f f.property j hj x)
  have h := frozen_chart_functional_trace E hP (compactPartialEvaluation j i x)
    (C * jbracket x ^ Pw) hK hb
  refine ⟨h.1, h.2.trans_eq ?_⟩
  have hw : (jbracket x ^ Pw) ^ 2 = jbracket x ^ (2 * Pw) := by
    rw [← Real.rpow_two, ← Real.rpow_mul (s57p_jbracket_pos x).le]
    congr 1
    ring
  rw [mul_pow, hw]

/-- The pointwise trace of chart values, with the constant chosen before
the chart and spatial point. -/
theorem physical_chart_value_trace (d r : ℕ) (Pw : ℝ)
    (hr : (2 : ℝ) + (d : ℝ) / 2 < r) (hP : (d : ℝ) < 2 * Pw) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ E : r26t6_WeightedChart d r Pw, ∀ x,
      Summable (fun n => E.test n x ^ 2) ∧
      (∑' n, E.test n x ^ 2) ≤ C ^ 2 * jbracket x ^ (2 * Pw) := by
  obtain ⟨C, hC, hb⟩ := physical_chart_partial_trace d r Pw hr hP
  refine ⟨C, hC, fun E x => ?_⟩
  simpa only [partialDeriv, iteratedFDeriv_zero_apply] using
    hb E 0 (Nat.zero_le _) (Fin.elim0 : Fin 0 → Fin d) x

#print axioms frozen_chart_functional_trace
#print axioms physical_chart_partial_trace
#print axioms physical_chart_value_trace

end HRS.MS.ProClosureS111
