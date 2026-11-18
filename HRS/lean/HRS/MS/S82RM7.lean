import HRS.MS.S82RM6

/-!
# S8.2 R02 (S82R), M7: one scan step of the transfer
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Function
open scoped ENNReal BigOperators Classical

namespace HRS.MS.S82R
open HRS.External

variable {E : Type*} [MeasurableSpace E] {n : ℕ}

lemma s82r_inner_sum [NeZero n] (ℓ : Fin n) (a c : ℝ) (g h : Fin n → ℝ) :
    (1 / (n : ℝ)) * ∑ i ∈ Finset.univ.erase ℓ, ((a + g i) + (c + h i)) =
      (1 - 1 / (n : ℝ)) * (a + c) + (1 / (n : ℝ)) *
        ((∑ i ∈ Finset.univ.erase ℓ, g i) + ∑ i ∈ Finset.univ.erase ℓ, h i) := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hcard : ((Finset.univ.erase ℓ).card : ℝ) = (n : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ ℓ), Finset.card_univ, Fintype.card_fin]
    have : 1 ≤ n := Nat.pos_of_ne_zero (NeZero.ne n)
    rw [Nat.cast_sub this]; simp
  have e : ∑ i ∈ Finset.univ.erase ℓ, ((a + g i) + (c + h i)) =
      ((Finset.univ.erase ℓ).card : ℝ) * (a + c) + ((∑ i ∈ Finset.univ.erase ℓ, g i) +
        ∑ i ∈ Finset.univ.erase ℓ, h i) := by
    have : ∀ i, (a + g i) + (c + h i) = (a + c) + (g i + h i) := fun i => by ring
    simp_rw [this]
    rw [Finset.sum_add_distrib (f := fun _ => a + c) (g := fun i => g i + h i), Finset.sum_const,
      nsmul_eq_mul, Finset.sum_add_distrib]
  rw [e, hcard]
  field_simp

lemma s82r_scan_step [NeZero n] {μ : Measure E} [IsProbabilityMeasure μ] {S S' : Spec E n}
    {κ κ' : Fin n → (Fin n → E) → E → ℝ} {Γ : E → E → ℝ} {b : E → ℝ}
    (hS : s82r_Dens μ S κ) (hS' : s82r_Dens μ S' κ') (hH : s82r_Hyp μ Γ b κ κ')
    {W : Fin n → E → ℝ} (hW : s82r_WOK W) {F F' : (Fin n → E) → ℝ}
    (hFm : Measurable F) (hF'm : Measurable F') {BF BF' : ℝ} (hFb : ∀ x, |F x| ≤ BF)
    (hF'b : ∀ x, |F' x| ≤ BF') {k0 : ℝ}
    (hFF : ∀ x y, F x - F' y ≤ s82r_cost W x y + k0) (x y : Fin n → E) :
    S.scan F x - S'.scan F' y ≤
      k0 + (1 / (n : ℝ)) * ∑ i, ∫ z, W i z * b z ∂μ + s82r_cost (s82r_Sw μ Γ n W) x y := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  unfold Spec.scan
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  have hstep : ∀ i : Fin n, S.site i F x - S'.site i F' y ≤ k0 + ∫ z, W i z * b z ∂μ +
      ∑ ℓ ∈ Finset.univ.erase i, if x ℓ = y ℓ then 0 else
        (W ℓ (x ℓ) + s82r_Gam μ Γ (W i) (x ℓ)) + (W ℓ (y ℓ) + s82r_Gam μ Γ (W i) (y ℓ)) :=
    fun i => s82r_site_step hS hS' hH hW hFm hF'm hFb hF'b hFF i x y
  have h1 : ∑ i, (S.site i F x - S'.site i F' y) ≤ ∑ i, (k0 + ∫ z, W i z * b z ∂μ +
      ∑ ℓ ∈ Finset.univ.erase i, if x ℓ = y ℓ then 0 else
        (W ℓ (x ℓ) + s82r_Gam μ Γ (W i) (x ℓ)) + (W ℓ (y ℓ) + s82r_Gam μ Γ (W i) (y ℓ))) :=
    Finset.sum_le_sum fun i _ => hstep i
  have hswap : ∑ i : Fin n, ∑ ℓ ∈ Finset.univ.erase i, (if x ℓ = y ℓ then (0 : ℝ) else
        (W ℓ (x ℓ) + s82r_Gam μ Γ (W i) (x ℓ)) + (W ℓ (y ℓ) + s82r_Gam μ Γ (W i) (y ℓ))) =
      ∑ ℓ : Fin n, ∑ i ∈ Finset.univ.erase ℓ, (if x ℓ = y ℓ then (0 : ℝ) else
        (W ℓ (x ℓ) + s82r_Gam μ Γ (W i) (x ℓ)) + (W ℓ (y ℓ) + s82r_Gam μ Γ (W i) (y ℓ))) := by
    refine Finset.sum_comm' fun i ℓ => ?_
    simp [Finset.mem_erase, eq_comm, and_comm]
  have hcost : (1 / (n : ℝ)) * ∑ ℓ : Fin n, ∑ i ∈ Finset.univ.erase ℓ, (if x ℓ = y ℓ then (0 : ℝ) else
        (W ℓ (x ℓ) + s82r_Gam μ Γ (W i) (x ℓ)) + (W ℓ (y ℓ) + s82r_Gam μ Γ (W i) (y ℓ))) =
      s82r_cost (s82r_Sw μ Γ n W) x y := by
    unfold s82r_cost
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    by_cases hℓ : x ℓ = y ℓ
    · simp [hℓ]
    · simp only [hℓ, if_false]
      rw [s82r_inner_sum ℓ (W ℓ (x ℓ)) (W ℓ (y ℓ)) (fun i => s82r_Gam μ Γ (W i) (x ℓ))
        (fun i => s82r_Gam μ Γ (W i) (y ℓ))]
      unfold s82r_Sw
      ring
  have h2 : ∑ i : Fin n, (k0 + ∫ z, W i z * b z ∂μ +
      ∑ ℓ ∈ Finset.univ.erase i, if x ℓ = y ℓ then 0 else
        (W ℓ (x ℓ) + s82r_Gam μ Γ (W i) (x ℓ)) + (W ℓ (y ℓ) + s82r_Gam μ Γ (W i) (y ℓ))) =
      (n : ℝ) * k0 + ∑ i, ∫ z, W i z * b z ∂μ + ∑ ℓ : Fin n, ∑ i ∈ Finset.univ.erase ℓ,
        (if x ℓ = y ℓ then (0 : ℝ) else
        (W ℓ (x ℓ) + s82r_Gam μ Γ (W i) (x ℓ)) + (W ℓ (y ℓ) + s82r_Gam μ Γ (W i) (y ℓ))) := by
    rw [← hswap, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hmul := mul_le_mul_of_nonneg_left h1 (one_div_pos.mpr hn).le
  rw [h2] at hmul
  refine hmul.trans (le_of_eq ?_)
  rw [mul_add, mul_add, hcost]
  field_simp

end HRS.MS.S82R

end
