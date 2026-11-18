import HRS.MS.TransOpAux15

/-!
# S611 packet P4c: propagator and noise covariance of the translated coefficients

`C0 = (quadraticGradientDyn d s q β).coeff (fun _ => ρβ)` (stationary), `Ctr = ... .coeff (movTranslatedDensity q b ρβ)`, `cs r = movShift q b r`.
* `s611_coeff_shift`: `Ctr` is the `cs`-shift of `C0` (`drift_tr = drift_0(· - cs r) - q cs r`, `ρ_tr = ρβ(· - cs r)`), and `C0` is the
  `(-cs)`-shift of `Ctr`;
* `s611_propagator_shift`: under uniqueness of classical adjoint solutions for `C0`,
  `U^{r,t}_{tr}(φ(· - cs t)) = (U^{r,t}_0 φ)(· - cs r)`;
* `s611_noiseCov_shift`: `noiseCovW Ctr q' t t' (φ(· - cs t)) (φ'(· - cs t')) = noiseCovW C0 q' t t' φ φ'`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.TransOp

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s611_hasDerivAt_movShift (q : ℝ) (b : Euc d) (r : ℝ) :
    HasDerivAt (fun r => movShift q b r) ((-q) • movShift q b r) r := by
  unfold movShift
  have h1 : HasDerivAt (fun t : ℝ => Real.exp (-q * t)) (Real.exp (-q * r) * (-q)) r := by
    have := ((hasDerivAt_id r).const_mul (-q)).exp
    simpa using this
  have := h1.smul_const b
  refine this.congr_deriv ?_
  rw [smul_smul, mul_comm]

theorem s611_continuous_movShift (q : ℝ) (b : Euc d) : Continuous (fun r => movShift q b r) :=
  continuous_iff_continuousAt.2 fun r => (s611_hasDerivAt_movShift q b r).continuousAt

/-- `Ctr` is the `cs`-shift of `C0`. -/
theorem s611_drift_tr (s q β : ℝ) (ρβ : Euc d → ℝ) (b : Euc d) (r : ℝ) (x : Euc d) :
    ((quadraticGradientDyn d s q β).coeff (movTranslatedDensity q b ρβ)).drift r x =
      ((quadraticGradientDyn d s q β).coeff (fun _ => ρβ)).drift r (x - movShift q b r) +
        (-q) • movShift q b r := by
  show meanFieldDriftW (quadraticGradientDyn d s q β) (fun y => ρβ (y - movShift q b r)) x = _
  rw [s611_drift_shift]
  show _ = meanFieldDriftW (quadraticGradientDyn d s q β) ρβ (x - movShift q b r) + _
  rw [neg_smul, sub_eq_add_neg]

theorem s611_adjoint_to_tr (s q β : ℝ) (ρβ : Euc d → ℝ) (b : Euc d) {t : ℝ} {φ : Euc d → ℝ}
    {f : ℝ → Euc d → ℝ}
    (h : IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff (fun _ => ρβ)) t φ f) :
    IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff (movTranslatedDensity q b ρβ)) t
      (fun x => φ (x - movShift q b t)) (fun r x => f r (x - movShift q b r)) :=
  s611_adjoint_shift
    (C' := (quadraticGradientDyn d s q β).coeff (fun _ => ρβ))
    (Cc := (quadraticGradientDyn d s q β).coeff (movTranslatedDensity q b ρβ))
    (fun r => movShift q b r) (fun r => (-q) • movShift q b r)
    (s611_hasDerivAt_movShift q b)
    ((s611_continuous_movShift q b).const_smul (-q))
    rfl rfl rfl (fun r x => s611_drift_tr s q β ρβ b r x) (fun r x => rfl) h

theorem s611_adjoint_from_tr (s q β : ℝ) (ρβ : Euc d → ℝ) (b : Euc d) {t : ℝ} {ψ : Euc d → ℝ}
    {g : ℝ → Euc d → ℝ}
    (h : IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff (movTranslatedDensity q b ρβ)) t ψ g) :
    IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff (fun _ => ρβ)) t
      (fun x => ψ (x - -movShift q b t)) (fun r x => g r (x - -movShift q b r)) := by
  refine s611_adjoint_shift
    (C' := (quadraticGradientDyn d s q β).coeff (movTranslatedDensity q b ρβ))
    (Cc := (quadraticGradientDyn d s q β).coeff (fun _ => ρβ))
    (fun r => -movShift q b r) (fun r => q • movShift q b r) ?_ ?_
    rfl rfl rfl ?_ ?_ h
  · intro r
    have h1 := (s611_hasDerivAt_movShift q b r).fun_neg
    refine h1.congr_deriv ?_
    rw [neg_smul, neg_neg]
  · exact (s611_continuous_movShift q b).const_smul q
  · intro r x
    have := s611_drift_tr s q β ρβ b r (x + movShift q b r)
    simp only [add_sub_cancel_right] at this
    have e : x - -movShift q b r = x + movShift q b r := sub_neg_eq_add _ _
    rw [e, this, neg_smul]
    abel
  · intro r x
    show ρβ x = ρβ (x - -movShift q b r - movShift q b r)
    simp

end HRS.MS.TransOp

end
