import HRS.MC.D3T3Aux8

/-!
# Packet D3T3, auxiliary facts: rapid decay of `ĝ_λ` and smoothness of `g_λ`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal FourierTransform

namespace HRS.MC.D3T3

open HRS HRS.MC.FDLE HRS.MC.Per HRS.MC.D3T1

variable {d : ℕ}

lemma d3f_ghat_nonneg {ψ : Euc d → ℝ} {s b lam : ℝ} (hb0 : 0 ≤ b) (hlam : 0 < lam)
    (k : Lattice d) : 0 ≤ fdlGhat ψ s b lam k := by
  unfold fdlGhat
  exact mul_nonneg hb0 (setIntegral_nonneg measurableSet_Ioi (fun t ht =>
    div_nonneg (mul_nonneg (Real.rpow_nonneg (lt_trans hlam ht).le _) (sq_nonneg _))
      (lt_trans hlam ht).le))

/-- Polynomial decay of `ĝ_λ(k)` of any order. -/
lemma d3f_ghat_decay {s : ℝ} (hs0 : 0 ≤ s) {ψ : Euc d → ℝ} (hψ : IsFDLProfile ψ) {b lam : ℝ}
    (hb0 : 0 < b) (hlam : 0 < lam) (q : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : Lattice d, k ≠ 0 →
      fdlGhat ψ s b lam k ≤ B * Lattice.enorm k ^ (-(2 * (q : ℝ))) := by
  obtain ⟨C, hC0, hC⟩ := d3f_psi_sq hψ (q + d + 1)
  set a : ℝ := (d : ℝ) - s - 1 + (-(2 * ((q + d + 1 : ℕ) : ℝ))) with ha
  have ha1 : a < -1 := by
    rw [ha]; push_cast
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    linarith
  have hgint : IntegrableOn (fun t : ℝ => t ^ a) (Ioi lam) := integrableOn_Ioi_rpow_of_lt ha1 hlam
  set I : ℝ := ∫ t in Ioi lam, t ^ a with hI
  have hI0 : 0 ≤ I := setIntegral_nonneg measurableSet_Ioi (fun t ht =>
    Real.rpow_nonneg (lt_trans hlam ht).le _)
  refine ⟨b * C * I, by positivity, fun k hk => ?_⟩
  have hen : 1 ≤ Lattice.enorm k := d3f_enorm_ge_one hk
  have hen0 : 0 < Lattice.enorm k := lt_of_lt_of_le one_pos hen
  have hint := d3f_int_psi hψ hs0 hlam hk
  have hmono : ∫ t in Ioi lam, t ^ ((d : ℝ) - s) * fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2 / t
      ≤ ∫ t in Ioi lam, (C * Lattice.enorm k ^ (-(2 * ((q + d + 1 : ℕ) : ℝ)))) * t ^ a := by
    refine setIntegral_mono_on hint (hgint.const_mul _) measurableSet_Ioi (fun t ht => ?_)
    have ht0 : 0 < t := lt_trans hlam ht
    have h1 := hC t ht0 k hk
    calc t ^ ((d : ℝ) - s) * fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2 / t
        = (t ^ ((d : ℝ) - s) / t) * fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2 := by ring
      _ ≤ (t ^ ((d : ℝ) - s) / t) * (C * t ^ (-(2 * ((q + d + 1 : ℕ) : ℝ))) *
            Lattice.enorm k ^ (-(2 * ((q + d + 1 : ℕ) : ℝ)))) :=
          mul_le_mul_of_nonneg_left h1 (div_nonneg (Real.rpow_nonneg ht0.le _) ht0.le)
      _ = (C * Lattice.enorm k ^ (-(2 * ((q + d + 1 : ℕ) : ℝ)))) *
            (t ^ ((d : ℝ) - s) / t * t ^ (-(2 * ((q + d + 1 : ℕ) : ℝ)))) := by ring
      _ = _ := by rw [d3f_rpow_comb ht0]
  have hexp : Lattice.enorm k ^ (-(2 * ((q + d + 1 : ℕ) : ℝ))) ≤
      Lattice.enorm k ^ (-(2 * (q : ℝ))) := by
    refine Real.rpow_le_rpow_of_exponent_le hen ?_
    push_cast
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  unfold fdlGhat
  rw [integral_const_mul] at hmono
  calc b * ∫ t in Ioi lam, t ^ ((d : ℝ) - s) * fdlPsiHat ψ (t • Lattice.toEuc k) ^ 2 / t
      ≤ b * ((C * Lattice.enorm k ^ (-(2 * ((q + d + 1 : ℕ) : ℝ)))) * I) :=
        mul_le_mul_of_nonneg_left hmono hb0.le
    _ = (b * C * I) * Lattice.enorm k ^ (-(2 * ((q + d + 1 : ℕ) : ℝ))) := by ring
    _ ≤ (b * C * I) * Lattice.enorm k ^ (-(2 * (q : ℝ))) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)

end HRS.MC.D3T3
