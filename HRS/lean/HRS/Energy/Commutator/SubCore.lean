import HRS.Energy.Commutator.KatoPonce
import HRS.Energy.Commutator.AbsConv

/-!
# Route H, packet H5-H6: the near-field commutator and the splitting `g = g_η + f_η`

Source: `[HCRS] Thm. 4.1` (proof): `Comm_N = Comm[g_η] + Comm[f_η]`, `Comm[g_η]` by Cor. 3.2
(`gEta_commutator`), and `|Comm[f_η]| ≤ ‖∇v‖_∞ ∬_{△^c} |x-y||∇f_η(x-y)| d(μ_N+μ)^{⊗2}`
`≲ L (N⁻² ∑_{i≠j} f_{2η}(x_i-x_j) + Λ η^{d-s})` by `fEta_grad_comparison` and `fEta_conv_bound`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator

variable {d : ℕ} {s : ℝ}

/-- **H5 (near-field commutator).**  Constants depend only on `d, s`.  (`|k(x,y)| ≤ L tdist(x,y)
‖∇f_η(x-y)‖ ≤ L (C f_{2η}(x-y) + C' η^{d-s})` pointwise by `fEta_grad_comparison`, with the *torus-negative*
`f_{2η}` kept with its own coefficient (`N = 2`, `X = (0, e_1/2)` shows that a bare `η^{d-s}` of coefficient
`C` in front of the pair sum would be false: the pair sum is `≈ -mη^{d-s}`); the three terms of
`offDiagPairing` are a finite pair sum, two `μ`-integrals bounded by `fEta_conv_bound`, and the
double integral.) -/
theorem fEta_commutator (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C C' : ℝ, 0 < C ∧ 0 ≤ C' ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 16 → ∀ (L : ℝ) (v : Torus d → Euc d), 0 ≤ L →
      IsLipschitzVF L v → ∀ (ρ : Torus d → ℝ) (Λ : ℝ), IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      ∀ (N : ℕ), 2 ≤ N → ∀ X : Config d N, X ∉ collisionSet d N →
        |commQuantityWith (fun z => Torus.grad (fEta d s η) z) v X (withDensityReal ρ)| ≤
          C * L * ((1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, fEta d s (2 * η) (X i - X j)
            + C' * Λ * η ^ ((d : ℝ) - s)) := by
  sorry

/-- **H6.1 (splitting of the commutator quantity).**  For `x ≠ 0`,
`∇g = ∇g_η + ∇f_η` (`gEta_smoothOffZero`, `periodicRieszGrad_hasGradientAt`), and each of the two
commutator kernels is absolutely integrable (`|k_g| ≲ L(1 + |log|x-y||)`, `|k_f| ≲ L|x-y|^{-s}`),
so the Bochner integrals split (`offDiagPairing` is linear on integrable kernels). -/
theorem commQuantity_split (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {η : ℝ} (hη : 0 < η) {N : ℕ}
    (X : Config d N) (hX : X ∉ collisionSet d N) {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) {Λ : ℝ}
    (hΛ : ∀ x, ρ x ≤ Λ) {L : ℝ} {v : Torus d → Euc d} (hL : 0 ≤ L) (hv : IsLipschitzVF L v) :
    commQuantity d s v X (withDensityReal ρ) =
      commQuantityWith (fun z => Torus.grad (gEta d s η) z) v X (withDensityReal ρ) +
      commQuantityWith (fun z => Torus.grad (fEta d s η) z) v X (withDensityReal ρ) := by
  sorry

/-- **H3.2 (consequence of H3.1 and `fEta_ge`).**  The truncated energy is controlled:
`E_η ≤ 2(F_N + g_η(0)/(2N)) + C Λ η^{d-s}`. -/
theorem etaEnergy_le (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 8 → ∀ (ρ : Torus d → ℝ) (Λ : ℝ), IsProbDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ (N : ℕ), 2 ≤ N → ∀ X : Config d N, X ∉ collisionSet d N →
        etaEnergy d s η X (withDensityReal ρ) ≤
          2 * (rieszEnergy d s X (withDensityReal ρ) + gEta d s η 0 / (2 * N)) +
            C * Λ * η ^ ((d : ℝ) - s) := by
  obtain ⟨C₁, hC₁, h1⟩ := energy_control_bessel hd hs0 hsd
  obtain ⟨C₂, hC₂, h2⟩ := fEta_ge hd hs0 hsd
  refine ⟨2 * C₁ + C₂, by positivity, fun η hη hη8 ρ Λ hρ hΛ N hN X hX => ?_⟩
  have hE := h1 η hη hη8 ρ Λ hρ hΛ N hN X hX
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hΛ1 : 1 ≤ Λ := by
    by_contra hlt
    push_neg at hlt
    have h : ∫ x, ρ x ≤ ∫ _x : Torus d, Λ := by
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall hρ.nonneg)
        (integrable_const _) (Filter.Eventually.of_forall hΛ)
    have := hρ.integral_one
    simp at h
    linarith
  -- lower bound of the pair sum
  have hK : 0 ≤ C₂ * η ^ ((d : ℝ) - s) := by positivity
  have hpair : -(((N : ℝ) * (N - 1)) * (C₂ * η ^ ((d : ℝ) - s))) ≤
      ∑ i, ∑ j ∈ Finset.univ.erase i, fEta d s η (X i - X j) := by
    have hterm : ∀ i : Fin N, ∀ j ∈ Finset.univ.erase i, -(C₂ * η ^ ((d : ℝ) - s)) ≤
        fEta d s η (X i - X j) := by
      intro i j hj
      have hij : i ≠ j := fun h => (Finset.ne_of_mem_erase hj) h.symm
      have hne : X i - X j ≠ 0 := fun h => hX ⟨i, j, hij, sub_eq_zero.mp h⟩
      exact h2 η hη (by linarith) _ hne
    have hs1 : ∀ i : Fin N, -(((N : ℝ) - 1) * (C₂ * η ^ ((d : ℝ) - s))) ≤
        ∑ j ∈ Finset.univ.erase i, fEta d s η (X i - X j) := by
      intro i
      have := Finset.sum_le_sum (s := Finset.univ.erase i)
        (f := fun _ => -(C₂ * η ^ ((d : ℝ) - s))) (g := fun j => fEta d s η (X i - X j))
        (fun j hj => hterm i j hj)
      simp only [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul] at this
      have hc : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; simp
      rw [hc] at this
      linarith
    have := Finset.sum_le_sum (s := Finset.univ)
      (f := fun _ : Fin N => -(((N : ℝ) - 1) * (C₂ * η ^ ((d : ℝ) - s))))
      (g := fun i => ∑ j ∈ Finset.univ.erase i, fEta d s η (X i - X j)) (fun i _ => hs1 i)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    linarith
  have hlow : -(C₂ * η ^ ((d : ℝ) - s)) / 2 ≤
      (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, fEta d s η (X i - X j) := by
    have hpos : (0 : ℝ) ≤ 1 / (2 * (N : ℝ) ^ 2) := by positivity
    have h1 := mul_le_mul_of_nonneg_left hpair hpos
    have h2 : (1 / (2 * (N : ℝ) ^ 2)) * (-(((N : ℝ) * (N - 1)) * (C₂ * η ^ ((d : ℝ) - s)))) =
        -(((N : ℝ) - 1) / (2 * N)) * (C₂ * η ^ ((d : ℝ) - s)) := by
      field_simp
    have h3 : ((N : ℝ) - 1) / (2 * N) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have h4 := mul_le_mul_of_nonneg_right h3 hK
    nlinarith
  have hΛη : η ^ ((d : ℝ) - s) ≤ Λ * η ^ ((d : ℝ) - s) := by
    have : 0 ≤ η ^ ((d : ℝ) - s) := by positivity
    nlinarith
  have hen := etaEnergy_nonneg hd hs0 hsd hη X (withDensityReal ρ)
  nlinarith [mul_nonneg hC₁ (mul_nonneg (by linarith : (0:ℝ) ≤ Λ) (Real.rpow_nonneg hη.le ((d : ℝ) - s))),
    mul_le_mul_of_nonneg_left hΛη hC₂]

/-- **H3.3 (consequence of H3.1 and `etaEnergy_nonneg`).**  Near-field control by the Bessel
truncation: `N⁻² ∑_{i≠j} f_η(x_i-x_j) ≤ 2(F_N + g_η(0)/(2N)) + C Λ η^{d-s}`. -/
theorem fEta_pairs_le (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ℝ, 0 < η → η ≤ 1 / 8 → ∀ (ρ : Torus d → ℝ) (Λ : ℝ), IsProbDensity ρ →
      (∀ x, ρ x ≤ Λ) → ∀ (N : ℕ), 2 ≤ N → ∀ X : Config d N, X ∉ collisionSet d N →
        (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, fEta d s η (X i - X j) ≤
          2 * (rieszEnergy d s X (withDensityReal ρ) + gEta d s η 0 / (2 * N)) +
            C * Λ * η ^ ((d : ℝ) - s) := by
  obtain ⟨C₁, hC₁, h1⟩ := energy_control_bessel hd hs0 hsd
  refine ⟨2 * C₁, by positivity, fun η hη hη8 ρ Λ hρ hΛ N hN X hX => ?_⟩
  have hE := h1 η hη hη8 ρ Λ hρ hΛ N hN X hX
  have hen := etaEnergy_nonneg hd hs0 hsd hη X (withDensityReal ρ)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have e : (1 / (N : ℝ) ^ 2) = 2 * (1 / (2 * (N : ℝ) ^ 2)) := by field_simp
  rw [e, mul_assoc]
  nlinarith

end HRS.Commutator
