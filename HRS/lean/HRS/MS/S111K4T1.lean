import Mathlib
import HRS.MS.S111X2Aux14

/-!
# S11.1 / T03 (S11K4), small analytic tools (Pro `R26-T6` `E02`, `E05`, `E06`)
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set

namespace HRS.MS.S111K4

/-- Pro `R26-T6.E02`: a bounded linear operator commutes with the derivative. -/
theorem k4_response_derivative {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (R : E →L[ℝ] E)
    (f : ℝ → E) (f' : E) (v : ℝ) (hf : HasDerivAt f f' v) : HasDerivAt (fun q => R (f q)) (R f') v :=
  R.hasFDerivAt.comp_hasDerivAt v hf

/-- Pro `R26-T6.E05`: an integrable odd kernel pairing is antisymmetric under exchanging the two test functions. -/
theorem k4_odd_symmetrize {X : Type*} [MeasurableSpace X] (μ : Measure X) [SFinite μ]
    (k : X → X → ℝ) (g h : X → ℝ) (hk : ∀ x y, k y x = -k x y)
    (hi : Integrable (fun p : X × X => k p.1 p.2 * g p.1 * h p.2) (μ.prod μ)) :
    Integrable (fun p : X × X => k p.1 p.2 * h p.1 * g p.2) (μ.prod μ) ∧
      (∫ p, k p.1 p.2 * h p.1 * g p.2 ∂(μ.prod μ)) = -(∫ p, k p.1 p.2 * g p.1 * h p.2 ∂(μ.prod μ)) := by
  have hsw : Integrable (fun p : X × X => k p.2 p.1 * g p.2 * h p.1) (μ.prod μ) := hi.swap
  have e : ∀ p : X × X, k p.1 p.2 * h p.1 * g p.2 = -(k p.2 p.1 * g p.2 * h p.1) := fun p => by
    rw [hk p.1 p.2]; ring
  refine ⟨?_, ?_⟩
  · have := hsw.neg
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Pi.neg_apply]
    exact (e p).symm
  · simp_rw [e]
    rw [integral_neg]
    congr 1
    exact integral_prod_swap (fun p : X × X => k p.1 p.2 * g p.1 * h p.2)

/-- Pro `R26-T6.E06`: absolute continuity and the fundamental theorem of calculus for a function with bounded a.e.
derivative. -/
theorem k4_triple_ftc (H : ℝ) (hH : 0 < H) (K F : ℝ → ℝ) (hK : ContinuousOn K (Icc 0 H))
    (hF : IntegrableOn F (Icc 0 H)) (hder : ∀ v ∈ Ioo 0 H, HasDerivAt K (F v) v) (B : ℝ)
    (hbound : ∀ v ∈ Ioo 0 H, |F v| ≤ B) :
    AbsolutelyContinuousOnInterval K 0 H ∧
      ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ H → K b - K a = ∫ v in Icc a b, F v := by
  refine ⟨HRS.MS.S111X2.s111x2_ac_of_deriv_bdd hH hK hder hbound, fun a b ha hab hb => ?_⟩
  have hsub : Icc a b ⊆ Icc 0 H := Icc_subset_Icc ha hb
  have hFab : IntervalIntegrable F volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact hF.mono_set hsub
  have hKab : ContinuousOn K (Icc a b) := hK.mono hsub
  have hd' : ∀ x ∈ Ioo a b, HasDerivAt K (F x) x := fun x hx =>
    hder x ⟨lt_of_le_of_lt ha hx.1, lt_of_lt_of_le hx.2 hb⟩
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hKab hd' hFab
  rw [← this, intervalIntegral.integral_of_le hab, integral_Icc_eq_integral_Ioc]

end HRS.MS.S111K4
