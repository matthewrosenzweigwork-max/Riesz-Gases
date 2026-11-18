import HRS.MS.S111X2Aux1

/-!
# S11.1 X2, packet E03 (part 2): a continuous function with bounded interior derivative is absolutely continuous
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped NNReal

namespace HRS.MS.S111X2

/-- `HasDerivAt` on the open interval transfers to a.e. on `Icc`. -/
theorem s111x2_ae_icc_of_ioo {P : ℝ → Prop} {H : ℝ} (h : ∀ r ∈ Ioo 0 H, P r) :
    ∀ᵐ t ∂(volume.restrict (Icc 0 H)), P t := by
  rw [ae_restrict_iff' measurableSet_Icc]
  have : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Icc 0 H → t ∈ Ioo 0 H := by
    have h1 := Ioo_ae_eq_Icc (α := ℝ) (a := 0) (b := H) (μ := volume)
    filter_upwards [h1] with t ht hmem
    rw [ht]; exact hmem
  filter_upwards [this] with t ht hm using h t (ht hm)

theorem s111x2_ac_of_deriv_bdd {E E' : ℝ → ℝ} {H K : ℝ} (hH : 0 < H)
    (hcont : ContinuousOn E (Icc 0 H)) (hder : ∀ r ∈ Ioo 0 H, HasDerivAt E (E' r) r)
    (hbd : ∀ r ∈ Ioo 0 H, |E' r| ≤ K) :
    AbsolutelyContinuousOnInterval E 0 H := by
  have hK : 0 ≤ K := (abs_nonneg _).trans (hbd (H / 2) ⟨by linarith, by linarith⟩)
  have hL : LipschitzOnWith K.toNNReal E (Ioo 0 H) := by
    refine (convex_Ioo 0 H).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
      (fun x hx => (hder x hx).hasDerivWithinAt) (fun x hx => ?_)
    rw [Real.le_toNNReal_iff_coe_le hK]
    simpa using hbd x hx
  have hcl : closure (Ioo (0 : ℝ) H) = Icc 0 H := closure_Ioo hH.ne
  have hL' : LipschitzOnWith K.toNNReal E (Icc 0 H) := by
    rw [← hcl]
    exact LipschitzOnWith.closure (by rwa [hcl]) hL
  have hL'' : LipschitzOnWith K.toNNReal E (uIcc 0 H) := by
    rw [uIcc_of_le hH.le]; exact hL'
  exact hL''.absolutelyContinuousOnInterval

end HRS.MS.S111X2
