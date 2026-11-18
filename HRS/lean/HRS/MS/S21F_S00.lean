import HRS.MS.S21F_D00

/-!
# S21F, packet R26-T3.S00: static feature data and exactly centered observables

Definitions only: the concrete separable Hilbert feature space `SeqL2`, the exact first marginal in `W`, the actual `Q`-expectation
in each `B` coordinate; `StaticTransport` carries only the physical velocity bounds and the weighted divergence equation.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R26T3
open HRS HRS.Whole

def r26t3_J (d : ℕ) : ℕ := 4*d+40
def r26t3_k (d : ℕ) : ℕ := 2*d+10
def r26t3_marg {p : Parameters} {δ : ℝ} (R : Trajectory p δ) (N : ℕ) :=
  HRS.Whole.firstMarginal (r26t3_Q R N)
def r26t3_W {p : Parameters} {δ : ℝ} (R : Trajectory p δ) (q : ℕ → Euc p.d → ℝ)
    (N : ℕ) : EucConfig p.d N → SeqL2 := featureVec q (r26t3_marg R N)
def r26t3_ell {p : Parameters} {δ : ℝ} (R : Trajectory p δ) (q : ℕ → Euc p.d → ℝ)
    (x : Euc p.d) : SeqL2 := SeqL2.ofSeq (fun j => r26t3_a R (q j) x)
structure StaticTransport {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    (q : ℕ → Euc p.d → ℝ) where
  summable : IsSummableFeatureFamily (r26t3_J p.d) q
  v : ℕ → Euc p.d → Euc p.d
  C : ℝ
  Cpos : 0 ≤ C
  bounds : ∀ j, HasCbBound (r26t3_k p.d) (C * cbNorm (r26t3_J p.d) (q j)) (v j)
  divergence : ∀ j x, -(movDiv (fun y => R.ρ 0 y • v j y) x) = R.ρ 0 x * r26t3_a R (q j) x
def r26t3_h {p : Parameters} {δ : ℝ} {R : Trajectory p δ} {q : ℕ → Euc p.d → ℝ}
    (V : StaticTransport R q) (j : ℕ) := commutatorKernel p.d p.s (V.v j)
def r26t3_Aentry {p : Parameters} {δ : ℝ} {R : Trajectory p δ} {q : ℕ → Euc p.d → ℝ}
    (V : StaticTransport R q) (j k : ℕ) (x : Euc p.d) := inner ℝ (V.v j x) (gradient (q k) x)
def r26t3_Bcoord {p : Parameters} {δ : ℝ} {R : Trajectory p δ} {q : ℕ → Euc p.d → ℝ}
    (V : StaticTransport R q) (N j : ℕ) (X : EucConfig p.d N) : ℝ :=
  N * (pairEnergy (r26t3_h V j) X (r26t3_mu R 0) -
    ∫ Y, pairEnergy (r26t3_h V j) Y (r26t3_mu R 0) ∂(r26t3_Q R N))

end HRS.MS.R26T3
