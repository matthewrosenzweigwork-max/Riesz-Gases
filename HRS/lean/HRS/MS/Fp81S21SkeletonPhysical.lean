import HRS.MS.Fp81S21ErrorEnvelope2

/-!
# Parametric physical-error constructor for O5

The supplied O1 fixes the cubic tensor. The error field is the actual envelope
of all realization/start/test errors, with zero adjoined, as defined in
`Fp81S21ErrorEnvelope`. Its quantitative bound comes from `ErrorEnvelope2`.

The initial profile and the fixed-window decomposition remain explicit inputs.
In particular, this constructor does not select physical data, prove the
physical decomposition, or extract a common radius. The constants `C` and `c`
precede the window length and its vanishing recent-error profile.

Header elaboration: make `p`, `δ`, and `R` explicit in the telescope (with `δ`
implicit), and type `L`, `eL`, and `N`. No mathematical hypothesis is changed.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open Filter Topology

namespace HRS.Fp81.S21

open HRS.MS.R26T3

/-- Assemble O5 from the physical decomposition of the actual error envelope.
The `E` projection is definitionally `fp81s21_errorEnvelope p R
(fp81s21_O1_kappa O1)`. The supplied initial profile and tail constants are
retained verbatim; no positivity of `C` or of the profiles is required by O5. -/
def fp81s21_O5_of_physical
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (O1 : fp81s21_O1_gaussian_wick p.d p.s p.a p.β p.γ p.T R.ρ)
    (α : ℕ → ℝ) (hα : Tendsto α atTop (𝓝 0))
    (C c : ℝ) (hc : 0 < c)
    (hdec : ∀ L : ℝ, 0 < L → ∃ eL : ℕ → ℝ,
      Tendsto eL atTop (𝓝 0) ∧ ∀ N : ℕ, 2 ≤ N →
        fp81s21_errorEnvelope p R (fp81s21_O1_kappa O1) N ≤
          α N + eL N + C * Real.exp (-c * L)) :
    fp81s21_O5_recent_decomposition p.d p.s p.a p.β p.γ p.T R.ρ
      (fp81s21_O1_kappa O1) ⟨α, hα⟩ where
  E := fp81s21_errorEnvelope p R (fp81s21_O1_kappa O1)
  C := C
  c := c
  c_pos := hc
  E_nonneg := fp81s21_errorEnvelope_nonneg p R O1
  E_finite := fp81s21_errorEnvelope_E_finite p R (fp81s21_O1_kappa O1)
  quantitative := fp81s21_errorEnvelope_quantitative p R O1
  decomposition := hdec

end HRS.Fp81.S21

end

#print axioms HRS.Fp81.S21.fp81s21_O5_of_physical
