import HRS.Main.A8PAux31

/-!
# Packet A8P, part 32: conversion of the initial-fluctuation assumptions (I1, I1_L2)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

variable {d : ℕ}

section I1

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ}

/-- pointwise identity `σ ⟨ψ, Ξ_0⟩ - A η(ψ) = A (κ ⟨ψ, μ_N^0 - μ°⟩ - η(ψ))` a.e. -/
theorem a8p_I_ident (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ}
    (hN : 1 ≤ N) (ψ : Torus d → ℝ) :
    ∀ᵐ ω ∂(R N).P, S.sigma N * flucPair ((R N).X 0 ω) (S.ρ N 0) ψ - S.AN N * (R N).η ω ψ =
      S.AN N * (S.κ N * (pair (empirical ((R N).X₀ ω)) ψ - pair S.μ0 ψ) - (R N).η ω ψ) := by
  obtain ⟨-, -, h0⟩ := a8p_flow_facts hS hN
  have hdat := hS.mean_field.datum N hN
  filter_upwards [h0] with ω hω
  rw [hω]
  unfold flucPair
  rw [hdat, ← a8p_A_mul_kappa S N]
  ring

theorem a8p_I1_conv {m₀ : ℕ} {Cin : ℝ} {ε : ℕ → ℝ} {Ψ : ℕ → Set (Torus d → ℝ)}
    (hIF : InitialFluctuation S R m₀ Cin ε Ψ)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 1 ≤ N)
    {ψ : Torus d → ℝ} (hψ : ψ ∈ Submodule.span ℝ (Ψ N)) (hmem : MemSobolev (m₀ : ℝ) ψ) {K : ℝ}
    (hK : sobolevNorm (m₀ : ℝ) ψ ≤ K) :
    ∫⁻ ω, ENNReal.ofReal
        |S.sigma N * flucPair ((R N).X 0 ω) (S.ρ N 0) ψ - S.AN N * (R N).η ω ψ| ∂(R N).P ≤
      ENNReal.ofReal (ε N * K) := by
  have hε : 0 ≤ ε N := hIF.eps_anti.le_of_tendsto hIF.eps_tendsto N
  have h1 := hIF.I1 N hN ψ hψ hmem
  have hid := a8p_I_ident hS hN ψ
  have hA := a8p_A_abs_le S N
  refine le_trans (lintegral_mono_ae ?_) (h1.trans (ENNReal.ofReal_le_ofReal ?_))
  · filter_upwards [hid] with ω h
    rw [h, abs_mul]
    refine ENNReal.ofReal_le_ofReal ?_
    calc |S.AN N| * |S.κ N * (pair (empirical ((R N).X₀ ω)) ψ - pair S.μ0 ψ) - (R N).η ω ψ|
        ≤ 1 * |S.κ N * (pair (empirical ((R N).X₀ ω)) ψ - pair S.μ0 ψ) - (R N).η ω ψ| :=
          mul_le_mul_of_nonneg_right hA (abs_nonneg _)
      _ = _ := one_mul _
  · exact mul_le_mul_of_nonneg_left hK hε

theorem a8p_I1L2_conv {m₀ : ℕ} {Ψ : ℕ → Set (Torus d → ℝ)} {C₀' Λ' : ℝ} {𝔈' ε2 : ℕ → ℝ}
    (hE2 : EnergySmallness2 S R C₀' Λ' m₀ Ψ 𝔈' ε2)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 1 ≤ N)
    {ψ : Torus d → ℝ} (hψ : ψ ∈ Submodule.span ℝ (Ψ N)) (hmem : MemSobolev (m₀ : ℝ) ψ) {K : ℝ}
    (hK : sobolevNorm (m₀ : ℝ) ψ ≤ K) :
    ∫⁻ ω, ENNReal.ofReal
        ((S.sigma N * flucPair ((R N).X 0 ω) (S.ρ N 0) ψ - S.AN N * (R N).η ω ψ) ^ 2) ∂(R N).P ≤
      ENNReal.ofReal ((ε2 N * K) ^ 2) := by
  have hε : 0 ≤ ε2 N := hE2.ε2_nonneg N hN
  have h1 := hE2.I1_L2 N hN ψ hψ hmem
  have hid := a8p_I_ident hS hN ψ
  have hA := a8p_A_abs_le S N
  have hn0 : 0 ≤ sobolevNorm (m₀ : ℝ) ψ := Real.sqrt_nonneg _
  refine le_trans (lintegral_mono_ae ?_) (h1.trans (ENNReal.ofReal_le_ofReal ?_))
  · filter_upwards [hid] with ω h
    rw [h, mul_pow]
    refine ENNReal.ofReal_le_ofReal ?_
    have hA2 : S.AN N ^ 2 ≤ 1 := by
      have := sq_abs (S.AN N)
      nlinarith [abs_nonneg (S.AN N)]
    calc S.AN N ^ 2 * (S.κ N * (pair (empirical ((R N).X₀ ω)) ψ - pair S.μ0 ψ) - (R N).η ω ψ) ^ 2
        ≤ 1 * (S.κ N * (pair (empirical ((R N).X₀ ω)) ψ - pair S.μ0 ψ) - (R N).η ω ψ) ^ 2 :=
          mul_le_mul_of_nonneg_right hA2 (sq_nonneg _)
      _ = _ := one_mul _
  · rw [mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hn0 hK 2) (sq_nonneg _)

end I1

end HRS.Main.A8P
