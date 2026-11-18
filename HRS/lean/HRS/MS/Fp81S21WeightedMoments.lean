import HRS.MS.Fp81S21WeightedNorm2
import HRS.MS.Fp81S21Uniform
import HRS.MS.R2WfmTie
import HRS.MS.S21F_D01

/-!
# Moving particle weighted field moments

`R2Wfm.round2_weighted_field_moments_proof` takes the physical parameters
`(d,s,M,L,C₀,c₀,b,p,K,Pw,k,m,r)` and returns two clauses.  The first clause
chooses `C` before the reference density and an indexed family
`P : ι → ℕ → Measure (EucConfig d N)`; its family premise is
`∀ i N, 2 ≤ N → HasR2ActualDensity s b p K (withDensityReal ρ) (P i N)`.
The resulting `R2WeightedFieldBound` contains both the raw empirical
fluctuation and the exactly centered commutator field.  For a moving
particle field at a fixed `u`, the intended family uses its actual law at
the selected particle count and the canonical Gibbs law at the other
counts.  The selected law is supplied by `fp81s21_uniform_density_moments`.

The definitions below preserve the two fields in that theorem verbatim.
They do not identify `r2NegSobNorm` with `dualNormE`: the only norm bridge
used later is `fp81s21_dualNormE_le_r2NegSobNorm`, while
`fp81s21_chartAction_dualNorm` identifies the chart action's norm exactly.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

/-- The chart coefficient representation and uniform second moment
contract for a time-indexed random functional.  The almost-everywhere
identity is required on every compact smooth `R2` test, and the norm
identity records the exact Hilbert chart normalization. -/
def fp81s21_MomentRep {d r : ℕ} {Pw : ℝ}
    {Ω : Type*} [MeasurableSpace Ω] (E : r26t6_WeightedChart d r Pw)
    (P : Measure Ω)
    (Q : ℝ → Ω → (Euc d → ℝ) → ℝ)
    (q : ℝ → Ω → r26t6_Coeff) (M : ℝ) : Prop :=
  Measurable (Function.uncurry q) ∧
    ∀ u, 0 ≤ u →
      MemLp (q u) 2 P ∧
      (∫ ω, ‖q u ω‖ ^ 2 ∂P) ≤ M ∧
      ∀ᵐ ω ∂P,
        (∀ f, IsR2Test f → fp81s21_chartAction E (q u ω) f = Q u ω f) ∧
        dualNormE r Pw (Q u ω) = ENNReal.ofReal ‖q u ω‖

/-- The raw moving empirical fluctuation field used by W1N. -/
def fp81s21_particleEmpField {p : Parameters} {δ : ℝ}
    (R : Trajectory p δ) (N : ℕ) (A : Particle R N) (u : ℝ)
    (ω : A.Ω) (f : Euc p.d → ℝ) : ℝ :=
  r2EmpDistr (r26t3_mu R u) (A.X u.toNNReal ω) f

/-- The moving particle quadratic field, with the actual law `A.P` used
for its exact centering. -/
def fp81s21_particleQuadField {p : Parameters} {δ : ℝ}
    (R : Trajectory p δ) (N : ℕ) (A : Particle R N) (u : ℝ)
    (ω : A.Ω) (f : Euc p.d → ℝ) : ℝ :=
  r2QuadField p.s (r26t3_mu R u) A.P A.X u ω f

#print axioms HRS.Fp81.S21.fp81s21_MomentRep
#print axioms HRS.Fp81.S21.fp81s21_particleEmpField
#print axioms HRS.Fp81.S21.fp81s21_particleQuadField

end HRS.Fp81.S21
