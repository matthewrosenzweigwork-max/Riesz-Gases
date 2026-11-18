/-
# HRS.Equilibrium.PairMomentsLinf -- eventual form of `reference_marginal_linf` (EQ-01b)

The sup-norm bound `‖dπ_N/dμ - 1‖_∞ ≤ C δ_N` of Lemma 4.10 with all hypotheses on the field `h_N` required
only for `N ≥ N_s` (the smallness `‖h_N‖_∞ ≤ 1` of the calibrated field holds only for large `N`).
The proof is that of `HRS.reference_marginal_linf_proof`.
-/
import HRS.Equilibrium.PinLinf

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

variable {d : ℕ} {s : ℝ}

open PinAux HRS.External HRS.External.RefMarg in
/-- Eventual form of `reference_marginal_linf_proof`: the hypotheses on `h_N` are only needed for
`N ≥ N_s` and so is the conclusion. -/
theorem reference_marginal_linf_ev (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) :
    ∃ γ₀ : ℝ, 0 < γ₀ ∧ ∀ (q : Torus d → ℝ) (Cq : ℝ), Measurable q → (∀ z, 0 ≤ q z) →
      (∀ z, q (-z) = q z) →
      (∃ k : Torus d → ℝ, Torus.IsSmooth k ∧ ∃ c : ℝ, ∀ z, z ≠ 0 → periodicRiesz d s z = q z + k z + c) →
      (∀ z, z ≠ 0 → q z ≤ Cq * (1 + Torus.eucDist z 0 ^ (-s))) →
      (∀ x, ∫⁻ y, ENNReal.ofReal (q (x - y)) ∂(withDensityReal ρ) ≤ ENNReal.ofReal γ₀) →
      ∀ (k : Torus d → ℝ) (Ck : ℝ), Measurable k → (∀ z, |k z| ≤ Ck) →
      ∀ (Ns : ℕ), 2 ≤ Ns → ∀ hN : ℕ → Torus d → ℝ,
      (∀ N, Ns ≤ N → Measurable (hN N) ∧ ∀ x, |hN N x| ≤ 1) →
      (∀ N, Ns ≤ N → weakRefMarginal q (hN N) (withDensityReal ρ) β N ≪ withDensityReal ρ) →
      (∀ N, Ns ≤ N → ∃ cN : ℝ, ∀ x, hN N x = -β * ∫ y, k (x - y) *
          (((weakRefMarginal q (hN N) (withDensityReal ρ) β N).rnDeriv
            (withDensityReal ρ) y).toReal - 1) ∂(withDensityReal ρ) + cN) →
      (∃ C₁ : ℝ, ∀ N, Ns ≤ N →
        eLpNorm (fun y => ((weakRefMarginal q (hN N) (withDensityReal ρ) β N).rnDeriv
            (withDensityReal ρ) y).toReal - 1) 2 (withDensityReal ρ) ≤
          ENNReal.ofReal (C₁ * deltaN d s N)) →
      (∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ᵐ y ∂(withDensityReal ρ),
        |((weakRefMarginal q (hN N) (withDensityReal ρ) β N).rnDeriv
            (withDensityReal ρ) y).toReal - 1| ≤ ε) →
      ∃ C : ℝ, ∀ N, Ns ≤ N → ∀ᵐ y ∂(withDensityReal ρ),
        |((weakRefMarginal q (hN N) (withDensityReal ρ) β N).rnDeriv
            (withDensityReal ρ) y).toReal - 1| ≤ C * deltaN d s N := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ s := by rw [hcrit]; linarith
  have hsd : s < d := by rw [hcrit]; linarith
  have hprob : IsProbabilityMeasure (withDensityReal ρ) := PoleCavityAux.isProbabilityMeasure_mu hρ
  refine ⟨pinGamma β, pinGamma_pos hβ, ?_⟩
  intro q Cq hqm hq0 hqe hdec hqenv hrow k Ck hkm hkb Ns hNs hN hNb hac hcal hL2 hunif
  obtain ⟨C₁, hC₁⟩ := hL2
  obtain ⟨Eδ, N₁, hEδ, hstep⟩ := linf_one_step hd hcrit β hβ ρ hρ q hq0 hqm hqe Cq hqenv hdec hrow
    k Ck hkm hkb C₁
  obtain ⟨N₀, hN₀⟩ := hunif (1 / 2) (by norm_num)
  have htend := (tendsto_deltaN (d := d) hd hs0 hsd).const_mul Eδ
  have hev := htend.eventually (gt_mem_nhds (by norm_num : Eδ * 0 < 1 / 32))
  obtain ⟨N₃, hN₃⟩ := Filter.eventually_atTop.1 hev
  set N₂ : ℕ := max (max N₀ N₁) (max N₃ Ns) with hN₂
  set Kd : ℝ := Real.exp ((β * pinGamma β + 1) + 1 + β * (1 + 0) * pinGamma β) with hKd
  have hKd0 : 0 < Kd := Real.exp_pos _
  refine ⟨max (8 * Eδ) (max 1 Kd * N₂), ?_⟩
  intro N hN2
  have hδ0 : 0 ≤ deltaN d s N := deltaN_nonneg hcrit (by omega)
  have hδ1 : 1 / (N : ℝ) ≤ deltaN d s N := deltaN_ge_inv hcrit (by omega)
  by_cases hbig : N₂ ≤ N
  · -- large N: iterate the one-step estimate
    have hN0 : N₀ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hbig
    have hN1 : N₁ ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hbig
    have hN3 : N₃ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hbig
    have hε : Eδ * deltaN d s N < 1 / 32 := by
      have := hN₃ N hN3
      simpa using this
    obtain ⟨cN, hcN⟩ := hcal N hN2
    set θ : ℝ := 4 * (β * pinGamma β) with hθ
    have hg : β * pinGamma β ≤ 1 / 16 := by
      rw [beta_mul_pinGamma hβ, div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith [Real.add_one_le_exp (10 : ℝ)]
    have hg0 : 0 ≤ β * pinGamma β := mul_nonneg hβ.le (pinGamma_pos hβ).le
    have hθ0 : 0 ≤ θ := by rw [hθ]; positivity
    have hθ1 : θ ≤ 1 / 4 := by rw [hθ]; linarith
    have hind : ∀ m : ℕ, ∃ M : ℝ, 0 ≤ M ∧ M ≤ 1 / 2 ∧ M ≤ θ ^ m / 2 + 8 * (Eδ * deltaN d s N) ∧
        ∀ᵐ y ∂(withDensityReal ρ), |((weakRefMarginal q (hN N) (withDensityReal ρ) β N).rnDeriv
          (withDensityReal ρ) y).toReal - 1| ≤ M := by
      intro m
      induction m with
      | zero =>
        refine ⟨1 / 2, by norm_num, le_rfl, ?_, hN₀ N hN0⟩
        have : 0 ≤ Eδ * deltaN d s N := mul_nonneg hEδ hδ0
        simp only [pow_zero]; linarith
      | succ m ih =>
        obtain ⟨M, hM0, hM1, hMθ, hMae⟩ := ih
        have hstp := hstep (hN N) (hNb N hN2).1 (hNb N hN2).2 N hN1 (by omega) cN hcN (hC₁ N hN2) (by linarith) M hM0 hM1 hMae
        have hε0 : 0 ≤ Eδ * deltaN d s N := mul_nonneg hEδ hδ0
        refine ⟨4 * (β * pinGamma β * M + Eδ * deltaN d s N), by positivity, ?_, ?_, hstp⟩
        · nlinarith
        · have : θ ^ (m + 1) = θ * θ ^ m := by ring
          rw [this]
          rw [hθ] at hθ0 hθ1 ⊢
          nlinarith [mul_nonneg hθ0 hε0, mul_le_mul_of_nonneg_left hMθ hθ0]
    have hall : ∀ᵐ y ∂(withDensityReal ρ), ∀ m : ℕ,
        |((weakRefMarginal q (hN N) (withDensityReal ρ) β N).rnDeriv (withDensityReal ρ) y).toReal - 1|
          ≤ θ ^ m / 2 + 8 * (Eδ * deltaN d s N) := by
      rw [ae_all_iff]
      intro m
      obtain ⟨M, -, -, hM, hae⟩ := hind m
      filter_upwards [hae] with y hy
      exact hy.trans hM
    filter_upwards [hall] with y hy
    have hlim : Filter.Tendsto (fun m : ℕ => θ ^ m / 2 + 8 * (Eδ * deltaN d s N)) Filter.atTop
        (nhds (0 / 2 + 8 * (Eδ * deltaN d s N))) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 (by linarith)).div_const 2).add_const _
    have := ge_of_tendsto hlim (Filter.Eventually.of_forall hy)
    refine this.trans ?_
    rw [zero_div, zero_add]
    calc 8 * (Eδ * deltaN d s N) = (8 * Eδ) * deltaN d s N := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hδ0
  · -- small N
    push Not at hbig
    have hK := weakRef_density_le β hβ ρ hρ q hq0 hqm hqe hrow (hN N) (hNb N hN2).1 (hNb N hN2).2 N (by omega)
    filter_upwards [hK] with y hy
    have hnn : 0 ≤ ((weakRefMarginal q (hN N) (withDensityReal ρ) β N).rnDeriv
        (withDensityReal ρ) y).toReal := ENNReal.toReal_nonneg
    have h1 : |((weakRefMarginal q (hN N) (withDensityReal ρ) β N).rnDeriv (withDensityReal ρ) y).toReal - 1|
        ≤ max 1 Kd := by
      rw [abs_le]
      constructor
      · linarith [le_max_left 1 Kd]
      · linarith [le_max_right 1 Kd, le_max_left 1 Kd]
    refine h1.trans ?_
    have hNr : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
    have hN2r : (N : ℝ) ≤ N₂ := by exact_mod_cast hbig.le
    have hmax : 1 ≤ max 1 Kd := le_max_left _ _
    have h2 : max 1 Kd ≤ (max 1 Kd * N₂) * (1 / (N : ℝ)) := by
      rw [mul_one_div, le_div_iff₀ (by linarith)]
      nlinarith
    calc max 1 Kd ≤ (max 1 Kd * N₂) * (1 / (N : ℝ)) := h2
      _ ≤ (max 1 Kd * N₂) * deltaN d s N :=
          mul_le_mul_of_nonneg_left hδ1 (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hδ0


end HRS

end
