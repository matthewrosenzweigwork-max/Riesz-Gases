import HRS.MS.R26T8AO02
import HRS.MS.R26T8AO03a

/-!
# S8.2 T8A O03b (part 1): closure of `TestBound` under sums and scalar multiples
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

theorem r26t8a_o03b_tb_add {k : ℕ} {A B : ℝ} {f g : Euc d → ℝ} (hf : TestBound k A f) (hg : TestBound k B g) :
    TestBound k (A + B) (f + g) := by
  refine ⟨hf.1.add hg.1, fun j hj1 hjk x => ?_⟩
  have hfj : ContDiff ℝ (j : WithTop ℕ∞) f := hf.1.of_le (by exact_mod_cast le_top)
  have hgj : ContDiff ℝ (j : WithTop ℕ∞) g := hg.1.of_le (by exact_mod_cast le_top)
  rw [iteratedFDeriv_add_apply hfj.contDiffAt hgj.contDiffAt]
  exact (norm_add_le _ _).trans (add_le_add (hf.2 j hj1 hjk x) (hg.2 j hj1 hjk x))

theorem r26t8a_o03b_tb_smul {k : ℕ} {A : ℝ} {f : Euc d → ℝ} (c : ℝ) (hf : TestBound k A f) :
    TestBound k (|c| * A) (c • f) := by
  refine ⟨hf.1.const_smul c, fun j hj1 hjk x => ?_⟩
  have hfj : ContDiff ℝ (j : WithTop ℕ∞) f := hf.1.of_le (by exact_mod_cast le_top)
  rw [iteratedFDeriv_const_smul_apply hfj.contDiffAt, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hf.2 j hj1 hjk x) (abs_nonneg c)

theorem r26t8a_o03b_tb_mono {k : ℕ} {A B : ℝ} {f : Euc d → ℝ} (hf : TestBound k A f) (hAB : A ≤ B) :
    TestBound k B f := ⟨hf.1, fun j hj1 hjk x => (hf.2 j hj1 hjk x).trans hAB⟩

theorem r26t8a_o03b_tb_nonneg {k : ℕ} {A : ℝ} {f : Euc d → ℝ} (hk : 1 ≤ k) (hf : TestBound k A f) : 0 ≤ A :=
  (norm_nonneg _).trans (hf.2 1 le_rfl hk 0)

theorem r26t8a_o03b_tb_of_testSize {k : ℕ} {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (ε : ℝ) (hε : 0 ≤ ε)
    (hb : testSizeE k f ≤ ENNReal.ofReal ε) : TestBound k ε f :=
  ⟨hf, fun j hj1 hjk x => r26t8a_o03a_le_testSize f ε hε hb j hj1 hjk x⟩

end HRS.MS.R26T8A
