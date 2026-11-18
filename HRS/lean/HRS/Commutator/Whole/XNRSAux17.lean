import HRS.Commutator.Whole.XNRSAux16

/-!
# Packet X-NRS, part 17: `𝒞_g(v,a) = 2 c' J(d-s, Λ^{-(d-s)} φ)`
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv

noncomputable section

namespace HRS.Commutator.Whole.XNRS

variable {d : ℕ}

theorem xB_J (hd : 3 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) :
    ∃ c' : ℂ, ∀ (ρ : Euc d → ℝ) (_hρ : XGoodCut ρ) (v : Euc d → Euc d) (_hv : XTVF v) (L : ℝ)
      (_hL0 : 0 ≤ L) (_hL : XLip v L) (a : Euc d → ℝ) (φ : 𝓢(Euc d, ℂ))
      (_ha : ∀ x, φ x = (a x : ℂ)) (_hφ : XInD ρ φ),
      ((CcommFun (kernGrad s) v a : ℝ) : ℂ) =
        2 * c' * xJ v ρ ((d : ℝ) - s) (xlam (-((d : ℝ) - s)) ρ φ) := by
  obtain ⟨c', hc'⟩ := xK0_conv hd hs0 hsd
  refine ⟨c', fun ρ hρ v hv L hL0 hL a φ ha hφ => ?_⟩
  have h1 := xB_real hd hs0 hsd hv hL0 hL a φ ha
  rw [h1]
  set h := xlam (-((d : ℝ) - s)) ρ φ with hh
  have hφeq : xlam ((d : ℝ) - s) ρ h = φ := by
    rw [hh, xlam_comp hρ hφ, add_neg_cancel, xlam_zero hρ hφ]
  unfold xJ
  rw [hφeq]
  have hint : ((∫ x, a x * ∑ i, v x i * ∫ y, kernGrad s (x - y) i * a y : ℝ) : ℂ) =
      ∫ x, ((a x * ∑ i, v x i * ∫ y, kernGrad s (x - y) i * a y : ℝ) : ℂ) :=
    (integral_complex_ofReal).symm
  rw [Complex.ofReal_mul, hint, mul_assoc, ← integral_const_mul]
  rw [← integral_const_mul, ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  have hx : ((a x * ∑ i, v x i * ∫ y, kernGrad s (x - y) i * a y : ℝ) : ℂ) =
      φ x * ∑ i, ((v x i : ℝ) : ℂ) * (c' * xdr i h x) := by
    rw [ha x]
    push_cast
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    rw [← hc' ρ hρ φ hφ i x, ← integral_complex_ofReal]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [ha y]
    push_cast; rfl
  rw [hx, xadv_apply hv, Complex.ofReal_ofNat]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

end HRS.Commutator.Whole.XNRS
