import HRS.MS.Fp81S21InitialWindow2
import HRS.MS.S21F_S02a
import HRS.MS.S21H2_S02

/-!
# S2.1(iii): response-window certificates

The intended packet-level claims are: after the common preparation radius is
chosen, with `0 < p.γ`, for every `b ≥ 0` and every `x`, the defined
`responseWindow R b x` is a genuine continuous path with coordinates
`r26t3_a R (propagatorW (r26t3_coeff R) 0 (b+t)
  (oscTestFun (wholeSpaceIndex p.d) α)) x`; the corresponding coordinate
sequence is in `ℓ²`; `x ↦ responseWindow R b x` is strongly measurable and its
cubic norm is integrable under `r26t3_mu R 0`; and it agrees with the shifted
`r2EllFun`/`r2EllPath` construction and physical restriction.

The response-inverse comparison available for these claims is only almost
everywhere.  Its actual hypotheses are `0 < δ`, `δ ≤ 1/2`, and
`MemLp f 2 (r26t3_mu R 0)`.  The smooth representative is separately
controlled under `0 < p.γ` and `MemCb (r26t3_J p.d) f`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3

variable {p : Parameters} {δ : ℝ}

/-- The canonical response representative agrees with `responseInverse`
almost everywhere under the actual time-zero preparation. The equality is
not asserted pointwise: `responseInverse` is totalized by zero when its
response witness is unavailable. -/
theorem fp81s21_response_inverse_ae
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (R : Trajectory p δ)
    (f : Euc p.d → ℝ) (hf : MemLp f 2 (r26t3_mu R 0)) :
    r26t3_a R f =ᵐ[r26t3_mu R 0]
      HRS.Whole.responseInverse (HRS.Whole.rieszKernel p.d p.s)
        (r26t3_mu R 0) p.γ f := by
  exact r26t3_response_ae hδ hδh R f hf

#print axioms fp81s21_response_inverse_ae

/-- At positive preparation strength, `r26t3_a` is the everywhere-defined
smooth representative. The constant is selected before the test function,
which is the order needed for orbit-family estimates. -/
theorem fp81s21_response_smooth
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (R : Trajectory p δ)
    (hγ : 0 < p.γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Euc p.d → ℝ,
      MemCb (r26t3_J p.d) f →
        MemCb (r26t3_k p.d + 2) (r26t3_a R f) ∧
        cbNorm (r26t3_k p.d + 2) (r26t3_a R f) ≤
          C * cbNorm (r26t3_J p.d) f ∧
        HRS.Whole.MemL2Zero (r26t3_mu R 0) (r26t3_a R f) ∧
        (∀ x, r26t3_a R f x + p.γ *
          HRS.Whole.Kop (HRS.Whole.rieszKernel p.d p.s)
            (r26t3_mu R 0) (r26t3_a R f) x =
          HRS.Whole.projMean (r26t3_mu R 0) f x) := by
  exact r26t3_response_smooth hδ hδh R hγ

#print axioms fp81s21_response_smooth

end HRS.Fp81.S21

end
