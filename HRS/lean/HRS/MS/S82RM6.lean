import HRS.MS.S82RM5

/-!
# S8.2 R02 (S82R), M6: one-site step of the transfer (uses M1)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Function
open scoped ENNReal BigOperators Classical

namespace HRS.MS.S82R
open HRS.External

variable {E : Type*} [MeasurableSpace E] {n : ℕ}

lemma s82r_site_step {μ : Measure E} [IsProbabilityMeasure μ] {S S' : Spec E n}
    {κ κ' : Fin n → (Fin n → E) → E → ℝ} {Γ : E → E → ℝ} {b : E → ℝ}
    (hS : s82r_Dens μ S κ) (hS' : s82r_Dens μ S' κ') (hH : s82r_Hyp μ Γ b κ κ')
    {W : Fin n → E → ℝ} (hW : s82r_WOK W) {F F' : (Fin n → E) → ℝ}
    (hFm : Measurable F) (hF'm : Measurable F') {BF BF' : ℝ} (hFb : ∀ x, |F x| ≤ BF)
    (hF'b : ∀ x, |F' x| ≤ BF') {k0 : ℝ}
    (hFF : ∀ x y, F x - F' y ≤ s82r_cost W x y + k0) (i : Fin n) (x y : Fin n → E) :
    S.site i F x - S'.site i F' y ≤ k0 + ∫ z, W i z * b z ∂μ +
      ∑ ℓ ∈ Finset.univ.erase i, if x ℓ = y ℓ then 0 else
        (W ℓ (x ℓ) + s82r_Gam μ Γ (W i) (x ℓ)) + (W ℓ (y ℓ) + s82r_Gam μ Γ (W i) (y ℓ)) := by
  obtain ⟨hki, hk1⟩ := hS.one i x
  obtain ⟨hki', hk1'⟩ := hS'.one i y
  obtain ⟨Bw, hBw⟩ := hW.bdd i
  rw [hS.site i x F, hS'.site i y F']
  set s : ℝ := k0 + ∑ ℓ ∈ Finset.univ.erase i, if x ℓ = y ℓ then 0 else W ℓ (x ℓ) + W ℓ (y ℓ) with hs
  have hmc := s82r_mc μ (κ i x) (κ' i y) (hS.nonneg i x) (hS'.nonneg i y) hki hki' hk1 hk1'
    (fun a => F (update x i a)) (fun b => F' (update y i b)) (W i)
    (hFm.comp (measurable_update x)) (hF'm.comp (measurable_update y)) (hW.meas i)
    (fun z => hFb _) (fun z => hF'b _)
    (fun z => by rw [abs_of_nonneg (hW.nonneg i z)]; exact hBw z) (hW.nonneg i) (s := s)
    (fun a => by
      have := hFF (update x i a) (update y i a)
      rw [s82r_cost_update] at this
      simp only [if_true, zero_add] at this
      rw [hs]; linarith)
    (fun a b => by
      have := hFF (update x i a) (update y i b)
      rw [s82r_cost_update] at this
      have h2 : (if a = b then 0 else W i a + W i b) ≤ W i a + W i b := by
        split_ifs
        · exact add_nonneg (hW.nonneg i a) (hW.nonneg i b)
        · exact le_rfl
      rw [hs]; linarith)
  have hd := s82r_wdiff_bound hH (hW.meas i) (hW.nonneg i) hBw i x y (hki.sub hki').abs
  have hsum : ∑ ℓ ∈ Finset.univ.erase i, (if x ℓ = y ℓ then (0 : ℝ) else W ℓ (x ℓ) + W ℓ (y ℓ)) +
      ∑ ℓ ∈ Finset.univ.erase i, (if x ℓ = y ℓ then (0 : ℝ) else
        s82r_Gam μ Γ (W i) (x ℓ) + s82r_Gam μ Γ (W i) (y ℓ)) =
      ∑ ℓ ∈ Finset.univ.erase i, if x ℓ = y ℓ then (0 : ℝ) else
        (W ℓ (x ℓ) + s82r_Gam μ Γ (W i) (x ℓ)) + (W ℓ (y ℓ) + s82r_Gam μ Γ (W i) (y ℓ)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    by_cases hℓ : x ℓ = y ℓ
    · simp [hℓ]
    · simp only [hℓ, if_false]; ring
  rw [← hsum]
  have : ∫ z, F (update x i z) * κ i x z ∂μ - ∫ z, F' (update y i z) * κ' i y z ∂μ ≤ s + ∫ z, W i z * |κ i x z - κ' i y z| ∂μ := hmc
  rw [hs] at this
  linarith

end HRS.MS.S82R

end
