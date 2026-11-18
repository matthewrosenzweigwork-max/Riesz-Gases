import HRS.Main.A8PAux30

/-!
# Packet A8P, part 31: `L¹`/`L²` moments of the remainder vector
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

variable {d : ℕ}

section RemMoments

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ} {Ca Λ₁ : ℝ}

theorem a8p_rem_L1 (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 2 ≤ N)
    {ℱ : Filtration ℝ (R N).mΩ} {W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution (R N).P ℱ W' (R N).W (R N).X)
    {C₀' Cq cT : ℝ} (hcom : A8CommSpec d S.s C₀' Cq) (hCq : 0 ≤ Cq) (hC : C₀' ≤ C₀) (hcT0 : 0 ≤ cT)
    (hcT : ∀ (M : Matrix (Fin d) (Fin d) ℝ), PDE.MatBound MB M → ∀ ψ : Torus d → ℝ, Torus.IsCk 2 ψ →
      MemSobolev (PDE.mStar d : ℝ) ψ →
        HasTransportBound d S.s (gfb2_v M ψ) (cT * sobolevNorm (PDE.mStar d : ℝ) ψ))
    {q : ℕ} (ts : Fin q → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Torus d → ℝ)
    (hφc : ∀ a, Continuous (φ a)) (hφ : ∀ a, MemSobolev (PDE.mStar d : ℝ) (φ a)) :
    ∫⁻ ω, ENNReal.ofReal (‖a8pRem S R N ts φ ω‖ ^ (1 : ℝ)) ∂(R N).P ≤
      ENNReal.ofReal ((∑ a, S.sigma N * ((1 / 2) * (Cq * (cT * a8pK Λ₁ (ts a) (φ a))))) *
        (S.T * 𝔈 N)) := by
  have hN1 : 1 ≤ N := by omega
  have hbd := a8p_rem_norm_bound hspec hCa hS hN hF hcom hCq hC hcT0 hcT ts hts φ hφc hφ
  obtain ⟨-, h2, -⟩ := a8p_energy_integral hS hN1 hF.progressive (C₀ := C₀) (Λ := Λ)
  set cR : ℝ := ∑ a, S.sigma N * ((1 / 2) * (Cq * (cT * a8pK Λ₁ (ts a) (φ a)))) with hcR
  have hcR0 : 0 ≤ cR := by
    refine Finset.sum_nonneg fun a _ => ?_
    have := a8pK_nonneg Λ₁ (ts a) (φ a)
    have := a8p_sigma_nonneg S N
    positivity
  simp only [Real.rpow_one]
  calc ∫⁻ ω, ENNReal.ofReal ‖a8pRem S R N ts φ ω‖ ∂(R N).P
      ≤ ∫⁻ ω, ENNReal.ofReal cR * ENNReal.ofReal
          (∫ r in Set.Icc (0 : ℝ) S.T, a8pEn S R N C₀ Λ r ω) ∂(R N).P := by
        refine lintegral_mono_ae ?_
        filter_upwards [hbd] with ω h
        rw [← ENNReal.ofReal_mul hcR0]
        exact ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal cR * ∫⁻ ω, ENNReal.ofReal
          (∫ r in Set.Icc (0 : ℝ) S.T, a8pEn S R N C₀ Λ r ω) ∂(R N).P :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal cR * ENNReal.ofReal (S.T * 𝔈 N) := by gcongr
    _ = _ := (ENNReal.ofReal_mul hcR0).symm

theorem a8p_rem_L2 (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 2 ≤ N)
    {ℱ : Filtration ℝ (R N).mΩ} {W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution (R N).P ℱ W' (R N).W (R N).X)
    {C₀' Cq cT : ℝ} (hcom : A8CommSpec d S.s C₀' Cq) (hCq : 0 ≤ Cq) (hC : C₀' ≤ C₀) (hcT0 : 0 ≤ cT)
    (hcT : ∀ (M : Matrix (Fin d) (Fin d) ℝ), PDE.MatBound MB M → ∀ ψ : Torus d → ℝ, Torus.IsCk 2 ψ →
      MemSobolev (PDE.mStar d : ℝ) ψ →
        HasTransportBound d S.s (gfb2_v M ψ) (cT * sobolevNorm (PDE.mStar d : ℝ) ψ))
    {q : ℕ} (ts : Fin q → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Torus d → ℝ)
    (hφc : ∀ a, Continuous (φ a)) (hφ : ∀ a, MemSobolev (PDE.mStar d : ℝ) (φ a))
    {𝔈' : ℝ} (h𝔈' : 0 ≤ 𝔈')
    (hb : ∀ t ∈ Set.Icc (0 : ℝ) S.T, ∫⁻ ω, ENNReal.ofReal
        ((correctedEnergy (S.dyn N) C₀ Λ (S.ρ N) ((R N).X (Real.toNNReal t) ω) t) ^ 2) ∂(R N).P ≤
      ENNReal.ofReal (𝔈' ^ 2)) :
    (∫⁻ ω, ENNReal.ofReal (‖a8pRem S R N ts φ ω‖ ^ (2 : ℝ)) ∂(R N).P) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal ((∑ a, S.sigma N * ((1 / 2) * (Cq * (cT * a8pK Λ₁ (ts a) (φ a))))) *
        (S.T * 𝔈')) := by
  have hN1 : 1 ≤ N := by omega
  have hbd := a8p_rem_norm_bound hspec hCa hS hN hF hcom hCq hC hcT0 hcT ts hts φ hφc hφ
  have h2 := a8p_energy_integral2 hS hN1 hF.progressive h𝔈' hb (C₀ := C₀) (Λ := Λ)
  set cR : ℝ := ∑ a, S.sigma N * ((1 / 2) * (Cq * (cT * a8pK Λ₁ (ts a) (φ a)))) with hcR
  have hcR0 : 0 ≤ cR := by
    refine Finset.sum_nonneg fun a _ => ?_
    have := a8pK_nonneg Λ₁ (ts a) (φ a)
    have := a8p_sigma_nonneg S N
    positivity
  set X : ℝ≥0∞ := ∫⁻ ω, ENNReal.ofReal (∫ r in Set.Icc (0 : ℝ) S.T, a8pEn S R N C₀ Λ r ω) ^ 2
    ∂(R N).P with hX
  have hle : ∫⁻ ω, ENNReal.ofReal (‖a8pRem S R N ts φ ω‖ ^ (2 : ℝ)) ∂(R N).P ≤
      ENNReal.ofReal cR ^ 2 * X := by
    calc ∫⁻ ω, ENNReal.ofReal (‖a8pRem S R N ts φ ω‖ ^ (2 : ℝ)) ∂(R N).P
        ≤ ∫⁻ ω, ENNReal.ofReal cR ^ 2 * ENNReal.ofReal
            (∫ r in Set.Icc (0 : ℝ) S.T, a8pEn S R N C₀ Λ r ω) ^ 2 ∂(R N).P := by
          refine lintegral_mono_ae ?_
          filter_upwards [hbd] with ω h
          rw [← mul_pow, ← ENNReal.ofReal_mul hcR0, ← ENNReal.ofReal_pow (mul_nonneg hcR0 (setIntegral_nonneg measurableSet_Icc
            fun r _ => a8pEn_nonneg S R N C₀ Λ r ω)), Real.rpow_two]
          refine ENNReal.ofReal_le_ofReal ?_
          exact pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = ENNReal.ofReal cR ^ 2 * X := lintegral_const_mul' _ _ (by simp)
  calc (∫⁻ ω, ENNReal.ofReal (‖a8pRem S R N ts φ ω‖ ^ (2 : ℝ)) ∂(R N).P) ^ (1 / 2 : ℝ)
      ≤ (ENNReal.ofReal cR ^ 2 * X) ^ (1 / 2 : ℝ) := ENNReal.rpow_le_rpow hle (by norm_num)
    _ = ENNReal.ofReal cR * X ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
        congr 1
        rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
        norm_num
    _ ≤ ENNReal.ofReal cR * ENNReal.ofReal (S.T * 𝔈') := by gcongr
    _ = _ := (ENNReal.ofReal_mul hcR0).symm

end RemMoments

end HRS.Main.A8P
