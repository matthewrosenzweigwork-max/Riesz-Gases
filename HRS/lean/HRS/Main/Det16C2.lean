import HRS.Main.Det16C1

/-!
# Example A.16, lemma L4: `det16c_standing`

From the hypotheses of `deterministic_example` (with `TorusStanding`'s energy field replaced by the
zero-temperature hypotheses `hsym`, `hΛ'`, `hsmall`), build `TorusStanding` at the level `gammaIdx d + 2`
with `𝔈_N = e^{C T Λ'} (F_N^{C₀}(Y_N,0))₊ + 1/(N(1+κ_N))` for `N ≥ 2` and the `N = 1` bound of L2.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Main.Det16

variable {d : ℕ}

theorem det16c_sigma_eq {S : MainData d} (hβ : ∀ N, S.invβ N = 0) (N : ℕ) : S.sigma N = S.κ N := by
  unfold MainData.sigma sigmaScale
  simp [hβ N]

theorem det16c_kappa_max_tendsto {κ E : ℕ → ℝ} (hκ : ∀ N, 0 < κ N)
    (h : Tendsto (fun N => κ N * E N) atTop (𝓝 0)) :
    Tendsto (fun N => κ N * max (E N) 0) atTop (𝓝 0) := by
  have habs : Tendsto (fun N => |κ N * E N|) atTop (𝓝 0) := by
    have := h.abs
    rwa [abs_zero] at this
  refine squeeze_zero (fun N => mul_nonneg (hκ N).le (le_max_right _ _)) (fun N => ?_) habs
  rcases le_total (E N) 0 with h0 | h0
  · rw [max_eq_right h0, mul_zero]; exact abs_nonneg _
  · rw [max_eq_left h0]; exact le_abs_self _

theorem det16c_standing (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C₀min : ℝ, ∀ (Rg : PDE.Regime) (ν₀ MB Λ VB C₀ Cc Λ' : ℝ), C₀min ≤ C₀ →
    IsCoercivityPair d s C₀ Cc →
    ∀ (S : MainData d), S.s = s → (∀ N, S.invβ N = 0) →
    ∀ (R : ∀ N, Realization d N), SelectedFlows S R →
    (∀ N : ℕ, 1 ≤ N → ∃ (ℱ : MeasureTheory.Filtration ℝ (R N).mΩ)
      (W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ),
      IsFilteredSolution (R N).P ℱ W' (R N).W (R N).X) →
    S.RegimeHolds Rg ν₀ →
    MeanFieldRegularity S (gammaIdx d + 2 + 3) Λ →
    PDE.MatBound MB S.M → PDE.VHyp (gammaIdx d + 2) VB S.V → Torus.SymNonpos S.M →
    (∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) S.T,
      HasTransportBound d s (meanFieldDrift (S.dyn N) (S.ρ N t)) Λ') →
    ∀ (Y : ∀ N, Config d N), (∀ N : ℕ, 1 ≤ N → ∀ᵐ ω ∂(R N).P, (R N).X₀ ω = Y N) →
    Tendsto (fun N => S.κ N * correctedEnergy (S.dyn N) C₀ Λ (S.ρ N) (Y N) 0) atTop (𝓝 0) →
    ∃ 𝔈 : ℕ → ℝ, TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d + 2) C₀ Cc 𝔈 := by
  obtain ⟨C₀min, C, hC₀min, hC, hbd⟩ := det16c_energy_bounds hd hs0 hsd
  refine ⟨C₀min, fun Rg ν₀ MB Λ VB C₀ Cc Λ' hC₀ hcp S hSs hβ R hflow hfilt hreg hmf hmat hV hsym
    hΛ' Y hdet hsmall => ?_⟩
  have hV2 : Torus.IsCk 2 S.V := by
    have := hV.1
    exact this.of_le (by exact_mod_cast (by omega : 2 ≤ gammaIdx d + 2 + 3))
  obtain ⟨hae, B, hB⟩ := hbd C₀ hC₀ S hSs hβ R hflow (r := gammaIdx d + 2 + 3) (Λ := Λ)
    (by omega) hmf hV2 hsym Λ' hΛ' Y hdet
  set G : ℕ → ℝ := fun N => Real.exp (C * S.T * Λ') *
    max (correctedEnergy (S.dyn N) C₀ Λ (S.ρ N) (Y N) 0) 0 with hG
  set δ : ℕ → ℝ := fun N => 1 / ((N : ℝ) * (1 + S.κ N)) with hδ
  have hG0 : ∀ N, 0 ≤ G N := fun N => mul_nonneg (Real.exp_pos _).le (le_max_right _ _)
  have hδ0 : ∀ N : ℕ, 1 ≤ N → 0 < δ N := fun N hN => by
    have h1 : (0 : ℝ) < N := by exact_mod_cast hN
    have := S.hκ N
    simp only [hδ]; positivity
  refine ⟨fun N => if N = 1 then max B 0 + 1 else G N + δ N, ?_⟩
  refine ⟨hflow, hreg, hmf, hmat, hV, ⟨?_, ?_, ?_, ?_⟩, hfilt⟩
  · rw [hSs]; exact hcp
  · intro N hN
    by_cases h1 : N = 1
    · simp only [h1, ite_true]; positivity
    · simp only [h1, ite_false]
      exact add_pos_of_nonneg_of_pos (hG0 N) (hδ0 N hN)
  · intro N hN t ht
    by_cases h1 : N = 1
    · subst h1
      simp only [ite_true]
      calc ∫⁻ ω, ENNReal.ofReal (correctedEnergy (S.dyn 1) C₀ Λ (S.ρ 1)
            ((R 1).X (Real.toNNReal t) ω) t) ∂(R 1).P
          ≤ ∫⁻ _ω, ENNReal.ofReal (max B 0 + 1) ∂(R 1).P := by
            refine lintegral_mono fun ω => ENNReal.ofReal_le_ofReal ?_
            have := hB t ht ((R 1).X (Real.toNNReal t) ω)
            have := le_max_left B 0
            linarith
        _ = ENNReal.ofReal (max B 0 + 1) := by simp
    · simp only [h1, ite_false]
      have hN2 : 2 ≤ N := by omega
      calc ∫⁻ ω, ENNReal.ofReal (correctedEnergy (S.dyn N) C₀ Λ (S.ρ N)
            ((R N).X (Real.toNNReal t) ω) t) ∂(R N).P
          ≤ ∫⁻ _ω, ENNReal.ofReal (G N) ∂(R N).P := by
            refine lintegral_mono_ae ?_
            filter_upwards [hae N hN2] with ω hω
            refine ENNReal.ofReal_le_ofReal ((hω t ht).trans ?_)
            exact mul_le_mul_of_nonneg_left (le_max_left _ _) (Real.exp_pos _).le
        _ = ENNReal.ofReal (G N) := by simp
        _ ≤ ENNReal.ofReal (G N + δ N) :=
            ENNReal.ofReal_le_ofReal (by linarith [(hδ0 N hN).le])
  · have h1 := det16c_kappa_max_tendsto S.hκ hsmall
    have h2 : Tendsto (fun N : ℕ => S.κ N * G N) atTop (𝓝 0) := by
      have := h1.const_mul (Real.exp (C * S.T * Λ'))
      rw [mul_zero] at this
      refine this.congr fun N => ?_
      simp only [hG]; ring
    have h3 : Tendsto (fun N : ℕ => S.κ N * δ N) atTop (𝓝 0) := by
      refine squeeze_zero' (Eventually.of_forall fun N => ?_) ?_ tendsto_one_div_atTop_nhds_zero_nat
      · have := S.hκ N
        simp only [hδ]; positivity
      · filter_upwards [eventually_ge_atTop 1] with N hN
        have hN' : (0 : ℝ) < N := by exact_mod_cast hN
        have := S.hκ N
        simp only [hδ]
        rw [← mul_div_assoc, mul_one, div_le_div_iff₀ (by positivity) hN']
        nlinarith
    have h4 := h2.add h3
    rw [add_zero] at h4
    refine h4.congr' ?_
    filter_upwards [eventually_ge_atTop 2] with N hN
    have : N ≠ 1 := by omega
    simp only [det16c_sigma_eq hβ, this, ite_false]
    ring

end HRS.Main.Det16
