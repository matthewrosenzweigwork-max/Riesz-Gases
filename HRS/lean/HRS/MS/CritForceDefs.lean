import HRS.Whole.Critical

/-!
# S8.2 shared definitions: weighted critical forcing

Definitions shared by the S8.2 producer packets (centered integrand, recent/old block suprema,
Hermite feature order and weights, history constant).  Statements copied from the Pro skeleton
(`S8.2.lean`); nothing here is an assumption.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S82BD

open HRS HRS.Whole

/-- Exactly the frozen centered integrand, with its original normalization. -/
def s82Centered (d N : ℕ) (a β m : ℝ) (ρ : Euc d → ℝ)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → EucConfig d N)
    (α : MultiIndex d) (t r : ℝ) (ζ : Ω) : ℝ :=
  (Real.sqrt N / 2) *
    (commForcing (critCoeff d a β ρ) ((d : ℝ) / 2) m
        (HRS.Whole.withDensityReal ρ) X α t r ζ -
      ∫ ζ', commForcing (critCoeff d a β ρ) ((d : ℝ) / 2) m
        (HRS.Whole.withDensityReal ρ) X α t r ζ' ∂P)

/-- The recent interval has length at most T when t is in [0,T]. -/
def s82Recent {ι Ω : Type} (F : ι → ℝ → ℝ → Ω → ℝ)
    (a₀ t : ℝ) (i : ι) (ζ : Ω) : ℝ :=
  ∫ r in Set.Icc a₀ (a₀ + t), F i (a₀ + t) r ζ

/-- Old history is partitioned into unit intervals, truncated at zero. -/
def s82Past {ι Ω : Type} (F : ι → ℝ → ℝ → Ω → ℝ)
    (a₀ : ℝ) (j : ℕ) (t : ℝ) (i : ι) (ζ : Ω) : ℝ :=
  ∫ r in Set.Icc (max 0 (a₀ - ((j : ℝ) + 1))) (max 0 (a₀ - (j : ℝ))),
    F i (a₀ + t) r ζ

def s82RecentSup {ι Ω : Type} (F : ι → ℝ → ℝ → Ω → ℝ)
    (T a₀ : ℝ) (i : ι) (ζ : Ω) : ℝ≥0∞ :=
  ⨆ t : Set.Icc (0 : ℝ) T, ENNReal.ofReal |s82Recent F a₀ t i ζ|

def s82PastSup {ι Ω : Type} (F : ι → ℝ → ℝ → Ω → ℝ)
    (T a₀ : ℝ) (j : ℕ) (i : ι) (ζ : Ω) : ℝ≥0∞ :=
  ⨆ t : Set.Icc (0 : ℝ) T, ENNReal.ofReal |s82Past F a₀ j t i ζ|

/-- M_* = K + ceil(d/2) + 6; K = 8d + 80. -/
def s82FeatureOrder (d : ℕ) : ℕ := 8 * d + 80 + (d + 1) / 2 + 6

def s82Weight (d : ℕ) (m : ℝ) (α : MultiIndex d) : ℝ :=
  oscEigenvalue d α ^ (((s82FeatureOrder d : ℝ) + 4 - m) / 2)

def s82HistoryConstant {ι : Type} (C q : ℝ) (w : ι → ℝ) : ℝ :=
  C * (1 + (1 - q)⁻¹) * Real.sqrt (∑' i, (w i) ^ 2)

end HRS.MS.S82BD
