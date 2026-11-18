import HRS.MC.S7S7fAux4

/-!
# Packet S7f, helper 5: the cubic cancellation for the triple series

Abstract algebra on families `T, Q, κ, D : ι → ι → ι → ℝ` with product weights: if
`T k l j + T k j l - γ Q k l j = κ k l j` (`sed_B9cancel`) and `D` is invariant under the swap of the last two
indices and under the cyclic shift, then
`-∑ T D + γ (1/2) ∑ Q (l j k)-shifted D = -(1/2) ∑ κ D`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7f

open HRS HRS.Sec7 HRS.MC.SEdge HRS.StaticLimitAux HRS.MC.Sec7.S7d HRS.MC.Sec7.S7c HRS.MC.Sec7.S7e

variable {ι : Type*}

theorem s7f_cancel_alg {b : ι → ℝ} (hb : Summable b) (hb0 : ∀ k, 0 ≤ b k) (γ : ℝ)
    {T Q κ D : ι → ι → ι → ℝ} {MT MQ Mκ : ℝ}
    (hT : ∀ k l j, |T k l j| ≤ MT * b k * b l * b j)
    (hQ : ∀ k l j, |Q k l j| ≤ MQ * b k * b l * b j)
    (hκ : ∀ k l j, |κ k l j| ≤ Mκ * b k * b l * b j)
    (hD : ∀ k l j, |D k l j| ≤ 1)
    (hB9 : ∀ k l j, T k l j + T k j l - γ * Q k l j = κ k l j)
    (hsw : ∀ k l j, D k j l = D k l j) (hcyc : ∀ k l j, D l j k = D k l j) :
    -(∑' k, ∑' l, ∑' j, T k l j * D k l j) +
        γ * ((1 / 2) * ∑' k, ∑' l, ∑' j, Q k l j * D l j k) =
      -(1 / 2) * ∑' k, ∑' l, ∑' j, κ k l j * D k l j := by
  have hsum : ∀ {M : ℝ} {u : ι → ι → ι → ℝ}, (∀ k l j, |u k l j| ≤ M * b k * b l * b j) →
      Summable (fun p : ι × (ι × ι) => u p.1 p.2.1 p.2.2 * D p.1 p.2.1 p.2.2) := by
    intro M u hu
    refine Summable.of_norm_bounded (s7e_summable_triple hb hb0 |M|) (fun p => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    calc |u p.1 p.2.1 p.2.2| * |D p.1 p.2.1 p.2.2| ≤ (M * b p.1 * b p.2.1 * b p.2.2) * 1 :=
          mul_le_mul (hu _ _ _) (hD _ _ _) (abs_nonneg _) ((abs_nonneg _).trans (hu _ _ _))
      _ ≤ |M| * b p.1 * b p.2.1 * b p.2.2 := by
          rw [mul_one]
          gcongr
          · exact hb0 _
          · exact hb0 _
          · exact hb0 _
          · exact le_abs_self M
  have hsT := hsum hT
  have hsQ := hsum hQ
  have hsκ := hsum hκ
  have eT := s7e_tsum_triple _ hsT
  have eQ := s7e_tsum_triple _ hsQ
  have eκ := s7e_tsum_triple _ hsκ
  have hQ' : ∀ k l j, Q k l j * D l j k = Q k l j * D k l j := fun k l j => by rw [hcyc]
  simp_rw [hQ']
  rw [← eT, ← eQ, ← eκ]
  -- the swap equivalence
  let e : ι × (ι × ι) ≃ ι × (ι × ι) := Equiv.prodCongr (Equiv.refl ι) (Equiv.prodComm ι ι)
  have hswap : ∑' p : ι × (ι × ι), T p.1 p.2.2 p.2.1 * D p.1 p.2.1 p.2.2 =
      ∑' p : ι × (ι × ι), T p.1 p.2.1 p.2.2 * D p.1 p.2.1 p.2.2 := by
    rw [← Equiv.tsum_eq e (fun p : ι × (ι × ι) => T p.1 p.2.1 p.2.2 * D p.1 p.2.1 p.2.2)]
    refine tsum_congr fun p => ?_
    obtain ⟨k, l, j⟩ := p
    simp [e, hsw]
  have hsT' : Summable (fun p : ι × (ι × ι) => T p.1 p.2.2 p.2.1 * D p.1 p.2.1 p.2.2) := by
    have := (e.summable_iff (f := fun p : ι × (ι × ι) => T p.1 p.2.1 p.2.2 * D p.1 p.2.1 p.2.2)).2 hsT
    refine this.congr fun p => ?_
    obtain ⟨k, l, j⟩ := p
    simp [e, hsw]
  have hcomb : ∑' p : ι × (ι × ι), (T p.1 p.2.1 p.2.2 + T p.1 p.2.2 p.2.1) * D p.1 p.2.1 p.2.2 =
      (∑' p : ι × (ι × ι), T p.1 p.2.1 p.2.2 * D p.1 p.2.1 p.2.2) +
      ∑' p : ι × (ι × ι), T p.1 p.2.1 p.2.2 * D p.1 p.2.1 p.2.2 := by
    simp_rw [add_mul]
    rw [hsT.tsum_add hsT', hswap]
  have hcomb2 : ∑' p : ι × (ι × ι), (T p.1 p.2.1 p.2.2 + T p.1 p.2.2 p.2.1) * D p.1 p.2.1 p.2.2 =
      (∑' p : ι × (ι × ι), κ p.1 p.2.1 p.2.2 * D p.1 p.2.1 p.2.2) +
      γ * ∑' p : ι × (ι × ι), Q p.1 p.2.1 p.2.2 * D p.1 p.2.1 p.2.2 := by
    have : ∀ p : ι × (ι × ι), (T p.1 p.2.1 p.2.2 + T p.1 p.2.2 p.2.1) * D p.1 p.2.1 p.2.2 =
        κ p.1 p.2.1 p.2.2 * D p.1 p.2.1 p.2.2 + γ * (Q p.1 p.2.1 p.2.2 * D p.1 p.2.1 p.2.2) := by
      intro p
      have := hB9 p.1 p.2.1 p.2.2
      rw [← this]; ring
    simp_rw [this]
    rw [hsκ.tsum_add (hsQ.mul_left γ), tsum_mul_left]
  linarith

end HRS.MC.Sec7.S7f

end
