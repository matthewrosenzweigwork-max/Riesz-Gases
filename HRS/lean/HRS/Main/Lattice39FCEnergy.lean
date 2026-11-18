import HRS.Main.Lattice39FinalSpec
import HRS.Main.Det16C1

/-!
# Example A.39, final form: the energy bound at a lattice `N = n^d` (D3)

`lattice39f_energy_proof`: `det16_pathwise_energy` (Proposition 3.36 (C1)) gives the a.s. bound
`sup_t F ≤ exp(C T Λ') F(0)` for the selected strong solution, `X^0 = perturbedLattice n κ a` a.s.;
`perturbedLattice_energy` bounds `F(0) + oN` for `κ ≥ κ₀`, and `oNΛ - oN` is absorbed in `N^{s/d-1}`.
Part (ii) is the same pathwise bound with the (finite, deterministic) real number `F(0)`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory BoundedContinuousFunction

namespace HRS

namespace Main

variable {d : ℕ}

/-- `oNΛ ≤ oN + c N^{s/d-1}` for `Λ ≥ 1`. -/
theorem l39c_oNLam_le (hd : 1 ≤ d) (s C₀ Λ : ℝ) (hΛ : 1 ≤ Λ) (N : ℕ) (hN : 1 ≤ N) :
    oNΛ d s C₀ Λ N ≤ oN d s C₀ N +
      (C₀ * (Λ ^ (s / (d : ℝ)) - 1) + Real.log Λ / (2 * d)) * (N : ℝ) ^ (s / (d : ℝ) - 1) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hP : 0 ≤ (N : ℝ) ^ (s / (d : ℝ) - 1) := Real.rpow_nonneg hN0.le _
  have hlog : 0 ≤ Real.log Λ := Real.log_nonneg hΛ
  unfold oNΛ oN
  by_cases hs : s = 0
  · subst hs
    simp only [ite_true, zero_div, Real.rpow_zero, mul_one, zero_sub]
    rw [Real.log_mul hN0.ne' (by linarith), Real.rpow_neg_one]
    field_simp
    first | exact le_rfl | (apply le_of_eq; ring)
  · simp only [hs, ite_false, zero_add, add_zero]
    have : 0 ≤ Real.log Λ / (2 * d) * (N : ℝ) ^ (s / (d : ℝ) - 1) := by positivity
    nlinarith

theorem lattice39f_energy_proof (hd2 : 1 ≤ d) (s : ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∀ (Λ T VB Λ' : ℝ) (a : Torus d → Euc d),
    Torus.IsSmooth a → ∃ κ₀ Ke : ℝ, 0 < κ₀ ∧ 0 ≤ Ke ∧
    ∀ (S : MainData d), S.s = s → S.T = T → S.μ0 = volume → (∀ N : ℕ, S.invβ N = 0) →
    Torus.SymNonpos S.M →
    (∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasTransportBound d s (meanFieldDrift (S.dyn N) (S.ρ N t)) Λ') →
    MeanFieldRegularity S (gammaIdx d + 3) Λ → PDE.VHyp (gammaIdx d) VB S.V →
    ∀ (R : ∀ N, Realization d N), SelectedFlows S R →
    ∀ n : ℕ, 2 ≤ n → (∀ᵐ ω ∂(R (n ^ d)).P, (R (n ^ d)).X₀ ω = perturbedLattice n (S.κ (n ^ d)) a) →
      (κ₀ ≤ S.κ (n ^ d) → ∀ t ∈ Set.Icc (0 : ℝ) T,
        ∫⁻ ω, ENNReal.ofReal
            (correctedEnergy (S.dyn (n ^ d)) C₀ Λ (S.ρ (n ^ d)) ((R (n ^ d)).X (Real.toNNReal t) ω) t)
          ∂(R (n ^ d)).P ≤
        ENNReal.ofReal (Ke * (((S.κ (n ^ d))⁻¹) ^ 2 + ((n ^ d : ℕ) : ℝ) ^ (s / (d : ℝ) - 1)))) ∧
      (∃ B : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) T,
        ∫⁻ ω, ENNReal.ofReal
            (correctedEnergy (S.dyn (n ^ d)) C₀ Λ (S.ρ (n ^ d)) ((R (n ^ d)).X (Real.toNNReal t) ω) t)
          ∂(R (n ^ d)).P ≤ ENNReal.ofReal B) := by
  by_cases hs : 0 ≤ s ∧ s < d
  swap
  · refine ⟨0, fun C₀ _ Λ T VB Λ' a _ => ⟨1, 0, one_pos, le_rfl, fun S hSs => ?_⟩⟩
    exact absurd (hSs ▸ ⟨S.hs0, S.hsd⟩) hs
  obtain ⟨hs0, hsd⟩ := hs
  obtain ⟨C₀min, C, hC₀min, hC, hpe⟩ := Det16.det16_pathwise_energy (by omega : 1 ≤ d) hs0 hsd
  refine ⟨C₀min, fun C₀ hC₀ Λ T VB Λ' a ha => ?_⟩
  obtain ⟨κ₀, Cpl, hκ₀, hCpl⟩ := perturbedLattice_energy (by omega : 1 ≤ d) hs0 hsd C₀ a ha
  set c1 : ℝ := C₀ * (Λ ^ (s / (d : ℝ)) - 1) + Real.log Λ / (2 * d) with hc1
  refine ⟨κ₀, Real.exp (C * T * Λ') * (|Cpl| + |c1|), hκ₀, by positivity, ?_⟩
  intro S hSs hST hμ hβ hsym hΛ' hmf hV R hflow n hn hlat
  subst hST
  have hΛ1 : 1 ≤ Λ := Det16.det16_Lam_ge_one hmf
  have hN2 : 2 ≤ n ^ d := hn.trans (Nat.le_self_pow (by omega) n)
  have hN1 : 1 ≤ n ^ d := by omega
  have hsol := Det16.det16c_strong hβ hflow hN1
  have hV2 : Torus.IsCk 2 S.V := hV.1.of_le (by exact_mod_cast (by omega : 2 ≤ gammaIdx d + 3))
  have hb := hpe C₀ hC₀ (S.dyn (n ^ d)) hSs (hβ _) hsym hV2 (n ^ d) hN2 S.T S.hT.le (S.ρ (n ^ d))
    (gammaIdx d + 3) Λ (by omega) hΛ1 (hmf.solution _ hN1) ((hmf.regular _ hN1).1) Λ' (hΛ' _ hN1)
    (R (n ^ d)).P (R (n ^ d)).X₀ (R (n ^ d)).W (R (n ^ d)).X hsol
  set E0 : ℝ := correctedEnergy (S.dyn (n ^ d)) C₀ Λ (S.ρ (n ^ d)) (perturbedLattice n (S.κ (n ^ d)) a) 0
    with hE0
  have key : ∀ t ∈ Set.Icc (0 : ℝ) S.T,
      ∫⁻ ω, ENNReal.ofReal
          (correctedEnergy (S.dyn (n ^ d)) C₀ Λ (S.ρ (n ^ d)) ((R (n ^ d)).X (Real.toNNReal t) ω) t)
        ∂(R (n ^ d)).P ≤ ENNReal.ofReal (Real.exp (C * S.T * Λ') * E0) := by
    intro t ht
    calc _ ≤ ∫⁻ _ω, ENNReal.ofReal (Real.exp (C * S.T * Λ') * E0) ∂(R (n ^ d)).P := by
          refine lintegral_mono_ae ?_
          filter_upwards [hb, hsol.init, hlat] with ω h1 h2 h3
          refine ENNReal.ofReal_le_ofReal ?_
          have := h1 t ht
          rw [h2, h3] at this
          exact this
      _ = _ := by simp
  refine ⟨fun hκ t ht => ?_, ⟨_, key⟩⟩
  refine (key t ht).trans (ENNReal.ofReal_le_ofReal ?_)
  -- the initial energy
  have hrho : withDensityReal (S.ρ (n ^ d) 0) = volume := (hmf.datum _ hN1).trans hμ
  have hE : E0 = rieszEnergy d s (perturbedLattice n (S.κ (n ^ d)) a) volume +
      oNΛ d s C₀ Λ (n ^ d) := by
    simp only [hE0, correctedEnergy, MainData.dyn, hrho, hSs]
  have h1 := hCpl n hn _ hκ
  have h2 := l39c_oNLam_le (by omega : 1 ≤ d) s C₀ Λ hΛ1 (n ^ d) hN1
  have hx : 0 ≤ ((S.κ (n ^ d))⁻¹) ^ 2 + ((n ^ d : ℕ) : ℝ) ^ (s / (d : ℝ) - 1) := by
    have : (0 : ℝ) < ((n ^ d : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < n ^ d)
    have := Real.rpow_nonneg this.le (s / (d : ℝ) - 1)
    positivity
  have hP : 0 ≤ ((n ^ d : ℕ) : ℝ) ^ (s / (d : ℝ) - 1) :=
    Real.rpow_nonneg (by positivity) _
  have hE2 : E0 ≤ (|Cpl| + |c1|) * (((S.κ (n ^ d))⁻¹) ^ 2 + ((n ^ d : ℕ) : ℝ) ^ (s / (d : ℝ) - 1)) := by
    rw [hE]
    have a1 : Cpl * (((S.κ (n ^ d))⁻¹) ^ 2 + ((n ^ d : ℕ) : ℝ) ^ (s / (d : ℝ) - 1)) ≤
        |Cpl| * (((S.κ (n ^ d))⁻¹) ^ 2 + ((n ^ d : ℕ) : ℝ) ^ (s / (d : ℝ) - 1)) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hx
    have a2 : c1 * ((n ^ d : ℕ) : ℝ) ^ (s / (d : ℝ) - 1) ≤
        |c1| * (((S.κ (n ^ d))⁻¹) ^ 2 + ((n ^ d : ℕ) : ℝ) ^ (s / (d : ℝ) - 1)) := by
      have : 0 ≤ ((S.κ (n ^ d))⁻¹) ^ 2 := by positivity
      calc c1 * ((n ^ d : ℕ) : ℝ) ^ (s / (d : ℝ) - 1) ≤ |c1| * ((n ^ d : ℕ) : ℝ) ^ (s / (d : ℝ) - 1) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) hP
        _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    nlinarith
  calc Real.exp (C * S.T * Λ') * E0
      ≤ Real.exp (C * S.T * Λ') * ((|Cpl| + |c1|) *
          (((S.κ (n ^ d))⁻¹) ^ 2 + ((n ^ d : ℕ) : ℝ) ^ (s / (d : ℝ) - 1))) :=
        mul_le_mul_of_nonneg_left hE2 (Real.exp_pos _).le
    _ = _ := by ring

example := (@lattice39f_energy_proof : type_of% @lattice39f_energy)

end Main

end HRS
