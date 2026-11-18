import HRS.Energy.Commutator.SubCore
import HRS.Energy.Commutator.Coerc0

/-!
# Fractional regime `0 ≤ s < d-2`: assembly (packet CM-H7)

`Comm_N = Comm[g_η] + Comm[f_η]` with `η = λ/16` (`commQuantity_split`), the Kato-Ponce bound
`|Comm[g_η]| ≤ C (L+F) E_η` (`gEta_commutator`), the near-field bound `|Comm[f_η]| ≲ L(N⁻²∑ f_{2η}
+ Λ η^{d-s})` (`fEta_commutator`) and the energy control `E_η, N⁻²∑ f_{2η} ≲ F_N + g(0)/2N + Λ η^{d-s}`
(`etaEnergy_le`, `fEta_pairs_le`) evaluated at `η = λ/16, λ/8` (`gEta_zero_le_oN`).
This file is **proved** modulo those statements.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator

variable {d : ℕ} {s : ℝ}

private theorem alg_final (C₁ C₂ L Fr Y : ℝ) (h1 : 0 ≤ C₁) (h2 : 0 ≤ C₂) (hL : 0 ≤ L) (hF : 0 ≤ Fr)
    (hY : 0 ≤ Y) :
    C₁ * (L + Fr) * (2 * Y) + C₂ * L * (2 * Y) ≤ 2 * (C₁ + C₂ + 1) * (L + Fr) * Y := by
  nlinarith [mul_nonneg h2 (mul_nonneg hF hY), mul_nonneg (add_nonneg hL hF) hY,
    mul_nonneg h1 (mul_nonneg (add_nonneg hL hF) hY)]

/-- `E ≤ 2(F + g) + t`, `g ≤ lp + C₅ a`, `t ≤ C₃ a` give `E ≤ 2(F + lp + C₀ a)` for any
`C₀ ≥ C₅ + C₃/2`. -/
private theorem alg_E (E F g t lp a C₃ C₅ C₀ : ℝ) (hE : E ≤ 2 * (F + g) + t) (hg : g ≤ lp + C₅ * a)
    (ht : t ≤ C₃ * a) (ha : 0 ≤ a) (hC : C₅ + C₃ ≤ C₀) (h3 : 0 ≤ C₃) :
    E ≤ 2 * (F + (lp + C₀ * a)) := by
  have : (C₅ + C₃) * a ≤ C₀ * a := mul_le_mul_of_nonneg_right hC ha
  have h4 : 0 ≤ C₃ * a := mul_nonneg h3 ha
  nlinarith

private theorem alg_S (S F g t lp a C₄ C₆ K C₀ : ℝ) (hS : S ≤ 2 * (F + g) + t) (hg : g ≤ lp + C₆ * a)
    (ht : t ≤ C₄ * a) (ha : 0 ≤ a) (hC : C₆ + C₄ + K ≤ C₀) (h4 : 0 ≤ C₄) (h6 : 0 ≤ C₆) (hK : 0 ≤ K)
    (u : ℝ) (hu : u ≤ K * a) :
    S + u ≤ 2 * (F + (lp + C₀ * a)) := by
  have : (C₆ + C₄ + K) * a ≤ C₀ * a := mul_le_mul_of_nonneg_right hC ha
  have h5 : 0 ≤ C₄ * a := mul_nonneg h4 ha
  have h7 : 0 ≤ C₆ * a := mul_nonneg h6 ha
  have h8 : 0 ≤ K * a := mul_nonneg hK ha
  nlinarith

/-- **Regime `0 ≤ s < d-2`**: `|Comm_N(v)| ≤ C (L + F)(F_N + o_N)` where `L` is a Lipschitz constant
and `F` bounds `‖|∇|^{(d+1)/2} v‖_{L^{2d/(d-1)}}`. -/
theorem commutator_estimate_sub (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) - 2) :
    ∃ C₀ C : ℝ, 0 ≤ C₀ ∧ 0 < C ∧ ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 2 ≤ N →
      ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ X : Config d N, X ∉ collisionSet d N →
      ∀ (L F : ℝ) (v : Torus d → Euc d), 0 ≤ L → 0 ≤ F → IsLipschitzVF L v → HasFracBound d v F →
        |commQuantity d s v X (withDensityReal ρ)| ≤
          C * (L + F) * (rieszEnergy d s X (withDensityReal ρ) + oNΛ d s C₀ Λ N) := by
  have hd1 : 1 ≤ d := by omega
  have hsd : s < d := by linarith
  obtain ⟨C₁, hC₁, hG⟩ := gEta_commutator hd hs0 hsd
  obtain ⟨C₂, C₂', hC₂, hC₂', hFc⟩ := fEta_commutator hd1 hs0 hsd
  obtain ⟨C₃, hC₃, hE⟩ := etaEnergy_le hd1 hs0 hsd
  obtain ⟨C₄, hC₄, hP⟩ := fEta_pairs_le hd1 hs0 hsd
  obtain ⟨C₅, hC₅, hz1⟩ := gEta_zero_le_oN hd1 hs0 hsd (c := 1 / 16) (by norm_num) (by norm_num)
  obtain ⟨C₆, hC₆, hz2⟩ := gEta_zero_le_oN hd1 hs0 hsd (c := 1 / 8) (by norm_num) (by norm_num)
  obtain ⟨C₇, hC₇, hnn⟩ := energy_add_oN_nonneg hd1 hs0 hsd
  refine ⟨C₇ + C₅ + C₃ + C₆ + C₄ + C₂' + 2, 2 * (C₁ + C₂ + 1), by positivity, by positivity, ?_⟩
  intro Λ hΛ N hN ρ hρ hρΛ X hX L Fr v hL hFr hv hfrac
  have hΛ0 : (0 : ℝ) ≤ Λ := by linarith
  have hlam1 : smearScale d N Λ < 1 := by
    have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
    exact CoercAux.smearScale_lt_one hd1 (by nlinarith)
  have hlam0 : 0 < smearScale d N Λ := CoercAux.smearScale_pos (by omega) (by linarith)
  have hη0 : 0 < 1 / 16 * smearScale d N Λ := by positivity
  have hη16 : 1 / 16 * smearScale d N Λ ≤ 1 / 16 := by nlinarith
  have h2η : 2 * (1 / 16 * smearScale d N Λ) = 1 / 8 * smearScale d N Λ := by ring
  have h2η0 : 0 < 2 * (1 / 16 * smearScale d N Λ) := by positivity
  have h2η8 : 2 * (1 / 16 * smearScale d N Λ) ≤ 1 / 8 := by rw [h2η]; nlinarith
  have ha := aNΛ_nonneg d s Λ N hΛ0
  have hlp := logPart_nonneg (d := d) (s := s) hΛ hN
  -- the bounds of the packets
  have hsplit := commQuantity_split hd hs0 hsd hη0 X hX hρ hρΛ hL hv
  have hB := hG _ hη0 (by linarith) L Fr v hL hFr hv hfrac ρ Λ hρ hρΛ N hN X
  have hD := hFc _ hη0 hη16 L v hL hv ρ Λ hρ hρΛ N hN X hX
  have hEη := hE _ hη0 (by linarith) ρ Λ hρ hρΛ N hN X hX
  have hP2 := hP _ h2η0 h2η8 ρ Λ hρ hρΛ N hN X hX
  obtain ⟨hg1, hΛ1⟩ := hz1 Λ hΛ N hN
  obtain ⟨hg2, hΛ2⟩ := hz2 Λ hΛ N hN
  rw [← h2η] at hg2 hΛ2
  have hΛη : (1 / 16 * smearScale d N Λ) ^ ((d : ℝ) - s) ≤
      Λ * (1 / 16 * smearScale d N Λ) ^ ((d : ℝ) - s) := by
    have : 0 ≤ (1 / 16 * smearScale d N Λ) ^ ((d : ℝ) - s) := by positivity
    nlinarith
  -- nonnegativity of Y := F + o_N
  have hY0 : 0 ≤ rieszEnergy d s X (withDensityReal ρ) +
      oNΛ d s (C₇ + C₅ + C₃ + C₆ + C₄ + C₂' + 2) Λ N := by
    have h1 := hnn Λ hΛ N hN ρ hρ hρΛ X hX
    have h2 := oNΛ_mono (d := d) (s := s) (N := N) hΛ0
      (show C₇ ≤ C₇ + C₅ + C₃ + C₆ + C₄ + C₂' + 2 by linarith)
    linarith
  rw [oNΛ_eq] at hY0 ⊢
  -- E_η ≤ 2 Y
  have hEY := alg_E _ _ _ _ _ _ C₃ C₅ (C₇ + C₅ + C₃ + C₆ + C₄ + C₂' + 2) hEη hg1
    (by calc C₃ * Λ * (1 / 16 * smearScale d N Λ) ^ ((d : ℝ) - s)
            = C₃ * (Λ * (1 / 16 * smearScale d N Λ) ^ ((d : ℝ) - s)) := by ring
          _ ≤ C₃ * aNΛ d s Λ N := mul_le_mul_of_nonneg_left hΛ1 hC₃)
    ha (by linarith) hC₃
  -- N⁻² ∑ f_{2η} + C₂' Λ η^{d-s} ≤ 2 Y
  have hSY' := alg_S _ _ _ _ _ _ C₄ C₆ C₂' (C₇ + C₅ + C₃ + C₆ + C₄ + C₂' + 2) hP2 hg2
    (by calc C₄ * Λ * (2 * (1 / 16 * smearScale d N Λ)) ^ ((d : ℝ) - s)
            = C₄ * (Λ * (2 * (1 / 16 * smearScale d N Λ)) ^ ((d : ℝ) - s)) := by ring
          _ ≤ C₄ * aNΛ d s Λ N := mul_le_mul_of_nonneg_left hΛ2 hC₄)
    ha (by linarith) hC₄ hC₆ hC₂'
    (C₂' * Λ * (1 / 16 * smearScale d N Λ) ^ ((d : ℝ) - s))
    (by calc C₂' * Λ * (1 / 16 * smearScale d N Λ) ^ ((d : ℝ) - s)
            = C₂' * (Λ * (1 / 16 * smearScale d N Λ) ^ ((d : ℝ) - s)) := by ring
          _ ≤ C₂' * aNΛ d s Λ N := mul_le_mul_of_nonneg_left hΛ1 hC₂')
  -- conclude
  calc |commQuantity d s v X (withDensityReal ρ)|
      = |commQuantityWith (fun z => Torus.grad (gEta d s (1 / 16 * smearScale d N Λ)) z) v X
            (withDensityReal ρ) +
          commQuantityWith (fun z => Torus.grad (fEta d s (1 / 16 * smearScale d N Λ)) z) v X
            (withDensityReal ρ)| := by rw [hsplit]
    _ ≤ |commQuantityWith (fun z => Torus.grad (gEta d s (1 / 16 * smearScale d N Λ)) z) v X
            (withDensityReal ρ)| +
          |commQuantityWith (fun z => Torus.grad (fEta d s (1 / 16 * smearScale d N Λ)) z) v X
            (withDensityReal ρ)| := abs_add_le _ _
    _ ≤ C₁ * (L + Fr) * etaEnergy d s (1 / 16 * smearScale d N Λ) X (withDensityReal ρ) +
          C₂ * L * ((1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i,
              fEta d s (2 * (1 / 16 * smearScale d N Λ)) (X i - X j) +
            C₂' * Λ * (1 / 16 * smearScale d N Λ) ^ ((d : ℝ) - s)) := add_le_add hB hD
    _ ≤ C₁ * (L + Fr) * (2 * (rieszEnergy d s X (withDensityReal ρ) +
            (logPart d s Λ N + (C₇ + C₅ + C₃ + C₆ + C₄ + C₂' + 2) * aNΛ d s Λ N))) +
          C₂ * L * (2 * (rieszEnergy d s X (withDensityReal ρ) +
            (logPart d s Λ N + (C₇ + C₅ + C₃ + C₆ + C₄ + C₂' + 2) * aNΛ d s Λ N))) := by
        have h1 : 0 ≤ C₁ * (L + Fr) := by positivity
        have h2 : 0 ≤ C₂ * L := by positivity
        exact add_le_add (mul_le_mul_of_nonneg_left hEY h1) (mul_le_mul_of_nonneg_left hSY' h2)
    _ ≤ 2 * (C₁ + C₂ + 1) * (L + Fr) * (rieszEnergy d s X (withDensityReal ρ) +
            (logPart d s Λ N + (C₇ + C₅ + C₃ + C₆ + C₄ + C₂' + 2) * aNΛ d s Λ N)) :=
        alg_final C₁ C₂ L Fr _ hC₁.le hC₂.le hL hFr hY0

end HRS.Commutator
