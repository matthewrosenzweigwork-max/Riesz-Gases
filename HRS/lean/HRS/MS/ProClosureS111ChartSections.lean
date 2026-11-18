import HRS.MS.ProClosureS111WeightedOperators
import HRS.MS.ProClosureS111PhysicalWick

/-!
Finite compact smooth sections of an arbitrary frozen weighted chart.
Their encodings are the canonical l2 truncations, so they approximate
every finite weighted C^r test, including the constant function. The
constant is never asserted to belong to the oscillator test space.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.ProClosureS111
open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.S111X1

variable {d r : ℕ} {Pw : ℝ}

def frozenWeightedEncode (E : r26t6_WeightedChart d r Pw) :
    weightedTestSubmodule d r Pw →ₗ[ℝ] r26t6_Coeff where
  toFun f := E.encode f
  map_add' f g := E.add _ _ (weightedTestSubmodule_iff.1 f.property)
    (weightedTestSubmodule_iff.1 g.property)
  map_smul' c f := E.smul c f (weightedTestSubmodule_iff.1 f.property)

def coeffSection (c : r26t6_Coeff) (n : ℕ) : r26t6_Coeff :=
  ∑ j ∈ Finset.range n, lp.single 2 j (c j)

theorem coeffSection_tendsto (c : r26t6_Coeff) :
    Tendsto (coeffSection c) atTop (𝓝 c) :=
  (lp.hasSum_single (by norm_num) c).tendsto_sum_nat

theorem inner_coeffSection (q c : r26t6_Coeff) (n : ℕ) :
    inner ℝ q (coeffSection c n) = ∑ j ∈ Finset.range n, c j * q j := by
  simp [coeffSection, inner_sum, lp.inner_single_right, mul_comm]

def chartSection (E : r26t6_WeightedChart d r Pw) (c : r26t6_Coeff) (n : ℕ) :
    compactSmoothSubmodule d :=
  ∑ j ∈ Finset.range n, c j • frozenChartTest E j

theorem chartSection_apply (E : r26t6_WeightedChart d r Pw) (c : r26t6_Coeff)
    (n : ℕ) (x : Euc d) :
    (chartSection E c n : Euc d → ℝ) x = ∑ j ∈ Finset.range n, c j * E.test j x := by
  simp [chartSection, frozenChartTest]

theorem encode_chartSection (E : r26t6_WeightedChart d r Pw)
    (hP : (d : ℝ) < 2 * Pw) (c : r26t6_Coeff) (n : ℕ) :
    E.encode (chartSection E c n) = coeffSection c n := by
  change compactFrozenEncode E hP (chartSection E c n) = _
  simp only [chartSection, map_sum, map_smul, coeffSection]
  refine Finset.sum_congr rfl fun j _ => ?_
  ext i
  change c j * E.encode (E.test j) i = (lp.single 2 j (c j) : r26t6_Coeff) i
  rw [E.test_coord]
  by_cases hij : j = i
  · subst i
    simp
  · simp [hij, Ne.symm hij, lp.single_apply, Pi.single_eq_of_ne]

theorem chartSection_error_weighted (E : r26t6_WeightedChart d r Pw)
    (hP : (d : ℝ) < 2 * Pw) (f : Euc d → ℝ) (hf : IsR2WeightedTest r Pw f)
    (n : ℕ) : IsR2WeightedTest r Pw
      ((chartSection E (E.encode f) n : Euc d → ℝ) - f) :=
  weightedTestSubmodule_iff.1 ((weightedTestSubmodule d r Pw).sub_mem
    (weighted_test_of_compact_smooth hP (chartSection E (E.encode f) n).property)
    (weightedTestSubmodule_iff.2 hf))

theorem chartSection_error_tendsto (E : r26t6_WeightedChart d r Pw)
    (hP : (d : ℝ) < 2 * Pw) (f : Euc d → ℝ) (hf : IsR2WeightedTest r Pw f) :
    Tendsto (fun n => (weightedSobolevE r Pw
      ((chartSection E (E.encode f) n : Euc d → ℝ) - f)).toReal) atTop (𝓝 0) := by
  have he : ∀ n, (weightedSobolevE r Pw
      ((chartSection E (E.encode f) n : Euc d → ℝ) - f)).toReal =
        ‖coeffSection (E.encode f) n - E.encode f‖ := by
    intro n
    rw [← E.norm _ (chartSection_error_weighted E hP f hf n)]
    let fn : weightedTestSubmodule d r Pw :=
      ⟨chartSection E (E.encode f) n,
        weighted_test_of_compact_smooth hP (chartSection E (E.encode f) n).property⟩
    let fw : weightedTestSubmodule d r Pw := ⟨f, weightedTestSubmodule_iff.2 hf⟩
    have hsub : E.encode ((chartSection E (E.encode f) n : Euc d → ℝ) - f) =
        E.encode (chartSection E (E.encode f) n) - E.encode f :=
      (frozenWeightedEncode E).map_sub fn fw
    rw [hsub, encode_chartSection E hP]
  simp_rw [he]
  exact tendsto_iff_norm_sub_tendsto_zero.1 (coeffSection_tendsto (E.encode f))

theorem constant_isWeightedTest (hP : (d : ℝ) < 2 * Pw) (c : ℝ) :
    IsR2WeightedTest r Pw (fun _ : Euc d => c) := by
  apply chart_weighted_of_memCb hP
  refine ⟨contDiff_const, fun j _ => ?_⟩
  refine ⟨|c|, ?_⟩
  rintro _ ⟨x, rfl⟩
  by_cases hj : j = 0
  · subst j
    simp
  · simp [iteratedFDeriv_const_of_ne hj]

/-- Oscillator evaluation is linear on the compact smooth chart sections. -/
theorem chartSection_eval (E : r26t6_WeightedChart d r Pw) (c : r26t6_Coeff)
    (n : ℕ) {m : ℝ} (z : OscDual d m) :
    OscDual.eval z (chartSection E c n) =
      ∑ j ∈ Finset.range n, c j * OscDual.eval z (E.test j) := by
  let embed : compactSmoothSubmodule d →ₗ[ℝ] oscSub d m :=
    { toFun := fun f => ⟨f, r2Test_isOscTest m f.property⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  show OscDual.eval z ((embed (chartSection E c n) : oscSub d m) : Euc d → ℝ) = _
  rw [← gaussianTestEvaluation_apply z (embed (chartSection E c n))]
  simp only [chartSection, map_sum, map_smul, smul_eq_mul, gaussianTestEvaluation_apply]
  rfl

/-- The actual commutator kernel is linear on compact chart sections. -/
theorem chartSection_commutator (E : r26t6_WeightedChart d r Pw) (c : r26t6_Coeff)
    (n : ℕ) (s : ℝ) (x y : Euc d) :
    HRS.Whole.commutatorKernel d s (gradient (chartSection E c n : Euc d → ℝ)) x y =
      ∑ j ∈ Finset.range n, c j *
        HRS.Whole.commutatorKernel d s (gradient (E.test j)) x y := by
  rw [← compactCommutatorEvaluation_apply]
  simp only [chartSection, map_sum, map_smul, smul_eq_mul,
    compactCommutatorEvaluation_apply, frozenChartTest]

theorem commutator_gradient_sub_const (s : ℝ) (c : ℝ) (f : Euc d → ℝ) :
    HRS.Whole.commutatorKernel d s (gradient (fun x => f x - c)) =
      HRS.Whole.commutatorKernel d s (gradient f) := by
  have hg : gradient (fun x => f x - c) = gradient f := by
    funext x
    simp only [gradient, fderiv_sub_const]
  rw [hg]

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.chartSection_error_tendsto
#print axioms HRS.MS.ProClosureS111.chartSection_eval
#print axioms HRS.MS.ProClosureS111.chartSection_commutator
