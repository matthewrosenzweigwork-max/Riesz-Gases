import HRS.MS.S21F_D00

/-!
# S21F, packet R26-T3.I00: enumerated cosine-Hermite initial feature family

Definitions plus the existence of the enumeration (`ℕ × MultiIndex d` is countably infinite).  The `3/4` Hilbert time-regularity
weight is `(1+n²)^(3/8)` on the cosine analysis coefficients; the normalized constant cosine is kept separately at `n = 0`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R26T3
open HRS HRS.Whole

abbrev FeatureIndex (d : ℕ) := ℕ × MultiIndex d

theorem r26t3_feature_enum_exists (d : ℕ) : Nonempty (ℕ ≃ FeatureIndex d) := by
  have : Countable (FeatureIndex d) := inferInstance
  have : Infinite (FeatureIndex d) := inferInstance
  exact ⟨(nonempty_equiv_of_countable (α := ℕ) (β := FeatureIndex d)).some⟩

open Classical in
def r26t3_feature_enum (d : ℕ) : ℕ ≃ FeatureIndex d := Classical.choice (r26t3_feature_enum_exists d)
def r26t3_cosine (T : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  if n=0 then (Real.sqrt T)⁻¹ else Real.sqrt (2/T)*Real.cos ((n : ℝ)*Real.pi*u/T)
def r26t3_qwin {p : Parameters} {δ : ℝ} (R : Trajectory p δ) (b : ℝ) (j : ℕ) (x : Euc p.d) : ℝ :=
  let i := r26t3_feature_enum p.d j
  (1+(i.1 : ℝ)^2)^(3/8 : ℝ)*∫ u in Set.Icc 0 p.T,
    r26t3_cosine p.T i.1 u*r26t3_U R 0 (b+u) (oscTestFun (wholeSpaceIndex p.d) i.2) x
def r26t3_feature_weight (d : ℕ) (j : ℕ) : ℝ :=
  let i := r26t3_feature_enum d j
  (1+(i.1 : ℝ))^(-(5/4 : ℝ))*oscEigenvalue d i.2^(-(3*(d : ℝ)+30))

end HRS.MS.R26T3
