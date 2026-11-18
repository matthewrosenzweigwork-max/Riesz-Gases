import HRS.Uniform.Q12Aux6

/-!
# Q12, part 7: Lemma 3.22 (`filtered_coercivity`), statement of `HRS/Uniform/Comparison.lean` verbatim
-/

noncomputable section

open MeasureTheory Filter Topology Set
open HRS HRS.CoercAux

namespace HRS.Uniform.Q12

variable {d : ℕ}

lemma q12_oN_mono {s C₀ C₀' : ℝ} (h : C₀ ≤ C₀') (N : ℕ) : oN d s C₀ N ≤ oN d s C₀' N := by
  unfold oN
  have : 0 ≤ (N : ℝ) ^ (s / d - 1) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  nlinarith

lemma q12_smear_pow_le (hd : 1 ≤ d) {N : ℕ} (hN : 1 ≤ N) {Λ : ℝ} (hΛ : 1 ≤ Λ) (L : ℕ) :
    (smearScale d N Λ ^ 2) ^ L ≤ (N : ℝ) ^ (-(2 * (L : ℝ)) / d) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hNΛ : (N : ℝ) ≤ N * Λ := by nlinarith
  unfold smearScale
  rw [← pow_mul, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  have e : (-(1 : ℝ) / d) * ((2 * L : ℕ) : ℝ) = -(2 * (L : ℝ)) / d := by
    push_cast; ring
  rw [e]
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine Real.rpow_le_rpow_of_nonpos hN0 hNΛ ?_
  have : 0 ≤ 2 * (L : ℝ) / d := by positivity
  rw [neg_div]; linarith

theorem filtered_coercivity_proof (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (Λ : ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∀ L : ℕ, 1 ≤ L → ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, 2 ≤ N → ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ X : Config d N, X ∉ collisionSet d N →
        0 ≤ rieszEnergy d s X (withDensityReal ρ) + oN d s C₀ N ∧
        ∀ φ : Torus d → ℝ, Torus.IsCk (2 * L : ℕ) φ → HasFiniteHomSobolev (((d : ℝ) - s) / 2) φ →
          ∀ A : ℝ, 0 ≤ A → (∀ x, |((Torus.laplacian : (Torus d → ℝ) → Torus d → ℝ)^[L] φ) x| ≤ A) →
            |∫ x, φ x ∂(empirical X) - ∫ x, φ x ∂(withDensityReal ρ)| ≤
              C * homSobolev (((d : ℝ) - s) / 2) φ *
                  Real.sqrt (rieszEnergy d s X (withDensityReal ρ) + oN d s C₀ N) +
                C * (N : ℝ) ^ (-(2 * (L : ℝ)) / d) * A := by
  set Λ' : ℝ := max Λ 1 with hΛ'
  have hΛ'1 : 1 ≤ Λ' := le_max_right _ _
  obtain ⟨C₀k, K, hC₀k, hK, core⟩ := q12_filtered_core hd hs0 hsd
  obtain ⟨-, C₀m, hC₀m, hm⟩ := oNΛ_le_oN hd hs0 hsd C₀k hC₀k Λ' hΛ'1
  refine ⟨C₀m, fun C₀ hC₀ L hL => ⟨2 ^ L * K + 2 + 1, by positivity, ?_⟩⟩
  intro N hN ρ hρ hρΛ X hX
  have hρΛ' : ∀ x, ρ x ≤ Λ' := fun x => (hρΛ x).trans (le_max_left _ _)
  obtain ⟨h0, hmain⟩ := core Λ' hΛ'1 L hL N hN ρ hρ hρΛ' X hX
  have hoN : oNΛ d s C₀k Λ' N ≤ oN d s C₀ N :=
    (hm N hN).trans (q12_oN_mono hC₀ N)
  set F := rieszEnergy d s X (withDensityReal ρ) with hF
  have hT0 : 0 ≤ F + oN d s C₀ N := by linarith
  refine ⟨hT0, fun φ hφ hhom A hA0 hA => ?_⟩
  have h1 := hmain φ hφ hhom A hA0 hA
  have h2 : Real.sqrt (F + oNΛ d s C₀k Λ' N) ≤ Real.sqrt (F + oN d s C₀ N) :=
    Real.sqrt_le_sqrt (by linarith)
  have h3 := q12_smear_pow_le hd (by omega : 1 ≤ N) hΛ'1 L
  have hhom0 : 0 ≤ homSobolev (((d : ℝ) - s) / 2) φ := Real.sqrt_nonneg _
  have hs1 : 0 ≤ Real.sqrt (F + oNΛ d s C₀k Λ' N) := Real.sqrt_nonneg _
  have hK1 : 0 ≤ 2 ^ L * K := by positivity
  have hP : 0 ≤ (N : ℝ) ^ (-(2 * (L : ℝ)) / d) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  refine h1.trans ?_
  have e1 : 2 ^ L * K * homSobolev (((d : ℝ) - s) / 2) φ * Real.sqrt (F + oNΛ d s C₀k Λ' N) ≤
      (2 ^ L * K + 2 + 1) * homSobolev (((d : ℝ) - s) / 2) φ * Real.sqrt (F + oN d s C₀ N) := by
    exact mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hhom0) h2 hs1 (by positivity)
  have e2 : 2 * (smearScale d N Λ' ^ 2) ^ L * A ≤
      (2 ^ L * K + 2 + 1) * (N : ℝ) ^ (-(2 * (L : ℝ)) / d) * A := by
    have hc2 : (2 : ℝ) ≤ 2 ^ L * K + 2 + 1 := by linarith
    calc 2 * (smearScale d N Λ' ^ 2) ^ L * A ≤ 2 * (N : ℝ) ^ (-(2 * (L : ℝ)) / d) * A := by gcongr
      _ ≤ _ := by gcongr
  linarith

end HRS.Uniform.Q12
