import HRS.MC.QRPHdAux9

/-!
# Packet HD, part 10: the band bound `A_{ab}² ≤ 8 ∑_{σ,ε,τ} 1[b = φ(a)] w(a)`
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped BigOperators ComplexConjugate

namespace HRS.MC.QRSpec.Hd

open HRS

variable {d : ℕ} {s : ℝ}

theorem hd_bool_sq (f : Bool → ℝ) : (∑ b, f b) ^ 2 ≤ 2 * ∑ b, f b ^ 2 := by
  rw [Fintype.sum_bool, Fintype.sum_bool]
  nlinarith [sq_nonneg (f true - f false)]

theorem hd_triple_sq (x : Bool → Bool → Bool → ℝ) :
    (∑ σ, ∑ ε, ∑ τ, x σ ε τ) ^ 2 ≤ 8 * ∑ σ, ∑ ε, ∑ τ, x σ ε τ ^ 2 := by
  have h1 : ∀ σ ε, (∑ τ, x σ ε τ) ^ 2 ≤ 2 * ∑ τ, x σ ε τ ^ 2 := fun σ ε => hd_bool_sq _
  have h2 : ∀ σ, (∑ ε, ∑ τ, x σ ε τ) ^ 2 ≤ 2 * ∑ ε, (∑ τ, x σ ε τ) ^ 2 := fun σ =>
    hd_bool_sq (fun ε => ∑ τ, x σ ε τ)
  have h3 := hd_bool_sq (fun σ => ∑ ε, ∑ τ, x σ ε τ)
  calc (∑ σ, ∑ ε, ∑ τ, x σ ε τ) ^ 2 ≤ 2 * ∑ σ, (∑ ε, ∑ τ, x σ ε τ) ^ 2 := h3
    _ ≤ 2 * ∑ σ, 2 * ∑ ε, (∑ τ, x σ ε τ) ^ 2 := by
        gcongr with σ _
        exact h2 σ
    _ ≤ 2 * ∑ σ, 2 * ∑ ε, 2 * ∑ τ, x σ ε τ ^ 2 := by
        gcongr with σ _ ε _
        exact h1 σ ε
    _ = 8 * ∑ σ, ∑ ε, ∑ τ, x σ ε τ ^ 2 := by
        simp only [← Finset.mul_sum]; ring

theorem hd_A_sq_le (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs1 : s + 1 < d) {ρ : Torus d → ℝ} {Λ : ℝ}
    (hΛ : ∀ x, ρ x ≤ Λ) (κ a b : NonzeroLattice d) :
    (Sec7.wickCoeff (withDensityReal ρ) (hTransport d s (Torus.realMode κ)) a b) ^ 2 ≤
      8 * ∑ σ : Bool, ∑ ε : Bool, ∑ τ : Bool,
        (if b.1 = hdφ κ.1 σ ε τ a.1 then hdw d s κ.1 σ ε a.1 else 0) := by
  set A := Sec7.wickCoeff (withDensityReal ρ) (hTransport d s (Torus.realMode κ)) a b with hA
  set x : Bool → Bool → Bool → ℝ := fun σ ε τ =>
    if b.1 = hdφ κ.1 σ ε τ a.1 then 4 * Real.pi ^ 2 * Lattice.enorm κ.1 * hdD d s (hdsg ε • κ.1) (hdsg σ • a.1) else 0
    with hx
  have hnorm : |A| ≤ ∑ σ, ∑ ε, ∑ τ, x σ ε τ := by
    have h1 : ‖(A : ℂ)‖ = |A| := by rw [Complex.norm_real, Real.norm_eq_abs]
    rw [← h1, hA, hd_wick_formula hd hs0 hs1 hΛ]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun σ _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ε _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
    by_cases hc : hdsg σ • a.1 + hdsg ε • κ.1 + hdsg τ • b.1 = 0
    · rw [if_pos hc, norm_mul]
      have hb := (hd_cond_iff σ ε τ a.1 κ.1 b.1).mp hc
      simp only [hx, if_pos hb]
      have hK := hdK_norm_le' (s := s) (hdsg σ • a.1) (hdsg ε • κ.1) (hdsg τ • b.1) hc
      rw [hd_enorm_smul_sg] at hK
      have hcf : ‖hdcf a.1 σ * hdcf κ.1 ε * hdcf b.1 τ‖ ≤ 1 := by
        rw [norm_mul, norm_mul]
        have h1 := hd_cf_norm_le a.1 σ
        have h2 := hd_cf_norm_le κ.1 ε
        have h3 := hd_cf_norm_le b.1 τ
        exact mul_le_one₀ (mul_le_one₀ h1 (norm_nonneg _) h2) (norm_nonneg _) h3
      calc ‖hdcf a.1 σ * hdcf κ.1 ε * hdcf b.1 τ‖ * ‖hdK d s (hdsg ε • κ.1) (hdsg τ • b.1)‖
          ≤ 1 * (4 * Real.pi ^ 2 * Lattice.enorm κ.1 * hdD d s (hdsg ε • κ.1) (hdsg σ • a.1)) :=
            mul_le_mul hcf hK (norm_nonneg _) zero_le_one
        _ = _ := one_mul _
    · have hb : ¬ b.1 = hdφ κ.1 σ ε τ a.1 := fun h => hc ((hd_cond_iff σ ε τ a.1 κ.1 b.1).mpr h)
      rw [if_neg hc]
      simp only [hx, if_neg hb]
      simp
  have hsq : A ^ 2 ≤ (∑ σ, ∑ ε, ∑ τ, x σ ε τ) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hnorm 2
  refine hsq.trans ((hd_triple_sq x).trans ?_)
  refine mul_le_mul_of_nonneg_left (le_of_eq ?_) (by norm_num)
  refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun ε _ => Finset.sum_congr rfl fun τ _ => ?_
  simp only [hx, hdw]
  split_ifs
  · ring
  · simp

end HRS.MC.QRSpec.Hd

end
