import HRS.MH.FilteredSF6
import HRS.Main.GFB2Aux3

/-!
# Packet SF7 `sf7_trace_moment_L` (moment of the trace-norm covariance error with `N^{-2L/d}`)

Statement copied verbatim from `HRS/MH/FilteredSpec.lean` (namespace `HRS.MH.Filtered` there, `HRS.MH.FilteredP` here).
Copy of `gfb2_trace_moment_of_error` (`HRS/Main/GFB2Aux3.lean:137-205`) with `herr := sf6_trace_error_L`; the core
`gfb2_trace_core` is generic in the error term and is reused unchanged.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MH.FilteredP

open HRS HRS.Uniform HRS.GF

variable {d : ℕ}


/-- `gf_trace_moment` with the exponent `N^{-2L/d}`, from `sf6_trace_error_L`. -/
theorem sf7_trace_moment_L (b : GeneralBounds d) (M : Matrix (Fin d) (Fin d) ℝ) (L : ℕ) (hL : 1 ≤ L)
    (hγL : (d : ℝ) / 2 + 1 + 2 * (L : ℝ) < (b.γ : ℝ)) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ S : GeneralSetup d, S.Within { b with C₀ := C₀ } → S.MFHypM M → ∀ N : ℕ, 2 ≤ N →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsStrongSolution P (S.dynM M N) S.T X₀ W X →
        (∃ (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
          IsFilteredSolution P ℱ W' W X) →
        S.EnergyMomentFinite P N X →
        ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (traceNormForm
          (covForm (S.γ : ℝ) (qN S N) (empirical (X (Real.toNNReal r) ω)) -
            covForm (S.γ : ℝ) (qN S N) (withDensityReal (S.ρ N r))))) ∂P ≤
          ENNReal.ofReal (C * qN S N *
            (Real.sqrt (S.energyMoment P N X) + (N : ℝ) ^ (-(2 * (L : ℝ)) / d))) := by
  classical
  by_cases hex : ∃ S₀ : GeneralSetup d, S₀.s = b.s ∧ S₀.γ = b.γ
  · obtain ⟨S₀, hs₀, hγ₀⟩ := hex
    have hd1 : 1 ≤ d := by have := S₀.hd; omega
    have hs0 : 0 ≤ b.s := hs₀ ▸ S₀.hs0
    have hsd : b.s < d := hs₀ ▸ S₀.hsd
    have hγ : 2 * d + 10 < b.γ := hγ₀ ▸ S₀.hγ
    obtain ⟨C₀min, h⟩ := sf6_trace_error_L hd1 b.s hs0 hsd b.γ hγ L hL hγL b.Λ
    refine ⟨C₀min, fun C₀ hC₀ => ?_⟩
    obtain ⟨C, hCpos, hpt⟩ := h C₀ hC₀
    refine ⟨C * (|b.T| + 1), by positivity, ?_⟩
    intro S hS hMF N hN Ω _ P _ X₀ W X hX hF hE
    unfold GeneralSetup.Within at hS
    obtain ⟨hs, hT, hγ', hΛ, hβ, hC0, hV⟩ := hS
    have hC0' : S.C₀ = C₀ := hC0
    have hq : 0 ≤ qN S N := (Q54c.qScale_bounds (by omega) (S.hκ N) (S.hinvβ N)).1
    have hn : 0 ≤ (N : ℝ) ^ (-(2 * (L : ℝ)) / d) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    obtain ⟨hMFN, hReg⟩ := hMF N
    have hpt' : ∀ r ∈ Set.Icc (0 : ℝ) S.T, ∀ x : Config d N, x ∉ collisionSet d N →
        traceNormForm (covForm (S.γ : ℝ) (qN S N) (empirical x) -
          covForm (S.γ : ℝ) (qN S N) (withDensityReal (S.ρ N r))) ≤
          C * qN S N * (Real.sqrt (S.energyCompletion N x r) + (N : ℝ) ^ (-(2 * (L : ℝ)) / d)) := by
      intro r hr x hx
      have hck : Torus.IsCk (b.γ + 2 * d + 12) (S.ρ N r) := by rw [← hγ']; exact (hReg r hr).1
      have hcb : Torus.cbNorm (b.γ + 2 * d + 12) (S.ρ N r) ≤ b.Λ := by
        rw [← hγ', ← hΛ]; exact (hReg r hr).2
      have h1 := hpt N hN (S.ρ N r) (hMFN.density r hr) hck hcb x hx (qN S N) hq
      unfold GeneralSetup.energyCompletion
      rw [hγ', hs, hC0']
      exact h1
    have hcore := gfb2_trace_core S M hMF N hN P X₀ W X hX hF hE C (qN S N) _ hCpos.le hq hn hpt'
    refine hcore.trans (ENNReal.ofReal_le_ofReal ?_)
    have hA : 0 ≤ C * qN S N * (Real.sqrt (S.energyMoment P N X) + (N : ℝ) ^ (-(2 * (L : ℝ)) / d)) :=
      mul_nonneg (mul_nonneg hCpos.le hq) (add_nonneg (Real.sqrt_nonneg _) hn)
    have hTle : S.T ≤ |b.T| + 1 := by rw [hT]; linarith [le_abs_self b.T]
    calc S.T * (C * qN S N * (Real.sqrt (S.energyMoment P N X) + (N : ℝ) ^ (-(2 * (L : ℝ)) / d)))
        ≤ (|b.T| + 1) * (C * qN S N * (Real.sqrt (S.energyMoment P N X) + (N : ℝ) ^ (-(2 * (L : ℝ)) / d))) :=
          mul_le_mul_of_nonneg_right hTle hA
      _ = C * (|b.T| + 1) * qN S N * (Real.sqrt (S.energyMoment P N X) + (N : ℝ) ^ (-(2 * (L : ℝ)) / d)) := by ring
  · refine ⟨0, fun C₀ _ => ⟨1, one_pos, ?_⟩⟩
    intro S hS
    exact absurd ⟨S, hS.1, hS.2.2.1⟩ hex

end HRS.MH.FilteredP
