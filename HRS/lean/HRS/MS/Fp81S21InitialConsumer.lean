import HRS.MS.Fp81S21InitialWindow

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section
namespace HRS.Fp81.S21

open HRS.Whole HRS.MS.R26T3

/-- The full-history future family used by the initial-window consumer. -/
abbrev Future (p : Parameters) :=
  (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d) H)

/-- Probability and Gaussian-future certificate, with the absolute cutoff at
zero retained. -/
def ValidFuture {p : Parameters} {δ : ℝ}
    (R : Trajectory p δ) (future : Future p) : Prop :=
  (∀ H v, IsProbabilityMeasure (future H v)) ∧
  ∀ H : ℝ, 0 < H → ∀ v ∈ Set.Icc (0 : ℝ) H,
    IsR2FutureGaussian (r26t3_coeff R)
      (wholeSpaceIndex p.d) H v (future H v)

/-- Exact packet-28 consumer contract. This remains a proposition header
until the all-parameter uniform static estimate is available. -/
def fp81s21_initial_uniform_in_shift_contract (p : Parameters) : Prop :=
  ∃ δ28 : ℝ, 0 < δ28 ∧ δ28 ≤ 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ28 → ∀ R : Trajectory p δ,
      ∀ [IsProbabilityMeasure (r26t3_mu R 0)],
      ∀ future : Future p, ValidFuture R future →
        ∃ α : ℕ → ℝ,
          (∀ N, 0 ≤ α N) ∧
          Tendsto α atTop (𝓝 0) ∧
          ∀ N : ℕ, 2 ≤ N → ∀ a : ℝ, ∀ ha : 0 ≤ a,
            ∀ Φ : Window p → ℝ, Φ ∈ HRS.CbUnitBall (Window p) 5 →
              ∀ G0 : GaussianRealization R,
                |initialRemainder R future N G0 a ha Φ| ≤ α N

#print axioms fp81s21_initial_uniform_in_shift_contract

end HRS.Fp81.S21
end
