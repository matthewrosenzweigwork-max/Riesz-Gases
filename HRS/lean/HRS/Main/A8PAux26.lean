import HRS.Main.A8PAux25

/-!
# Packet A8P, part 26: the `ℝ^q`-valued Hilbert Itô integral and its identification
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

variable {d : ℕ}

section Glue2

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ} {Ca Λ₁ : ℝ}

theorem a8p_hilbert_mart (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 1 ≤ N)
    {ℱ : Filtration ℝ (R N).mΩ} {W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution (R N).P ℱ W' (R N).W (R N).X)
    {q : ℕ} (ts : Fin q → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Torus d → ℝ)
    (hφc : ∀ a, Continuous (φ a)) (hφ : ∀ a, MemSobolev (PDE.mStar d : ℝ) (φ a)) :
    ∃ M : ℝ → (R N).Ω → EuclideanSpace ℝ (Fin q),
      IsHilbertItoIntegral (R N).P ℱ W' (a8pPhiH S R N ts φ) M ∧
      ∀ᵐ ω ∂(R N).P, M S.T ω = vectorItoIntegral (R N).P ℱ W'
        (fun a => killAfter (a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X) (ts a))
        S.T ω := by
  classical
  have hW : IsCylindricalBrownian (R N).P ℱ W' := gfb3_isCylindricalBrownian_of_filtration hF.brownian
  have hZ := fun T => a8p_phiH_isHS hspec hCa hS hN hF.progressive ts hts φ hφc hφ T
  obtain ⟨Mart, hc, had, hz, hJ⟩ := gfb3_exists_hilbert_version hW hZ
  have hMart : IsHilbertItoIntegral (R N).P ℱ W' (a8pPhiH S R N ts φ) Mart := by
    refine ⟨hc, had, hz, ?_⟩
    intro τ hτ x
    obtain ⟨J, hIJ, hae⟩ := hJ x
    refine (hIJ.approx τ hτ).congr fun s => ?_
    refine lintegral_congr_ae ?_
    filter_upwards [hae τ hτ] with ω h
    rw [h]
    rfl
  refine ⟨Mart, hMart, ?_⟩
  have hkill : ∀ a, IsProgressiveL2 (R N).P ℱ
      (killAfter (a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X) (ts a)) := fun a =>
    isProgressiveL2_indicator_set (R N).P (S := Set.Iio (ts a)) measurableSet_Iio
      (a8p_phi_progressive hspec hCa hS hN hF.progressive (hts a) (hφc a) (hφ a))
  have hT0 : 0 ≤ S.T := S.hT.le
  have hcoord : ∀ a, ∀ᵐ ω ∂(R N).P, (Mart S.T ω) a = itoIntegral (R N).P ℱ W'
      (killAfter (a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X) (ts a)) S.T ω := by
    intro a
    have hfun : (fun r ω k => inner ℝ (a8pPhiH S R N ts φ r ω k)
        (EuclideanSpace.single a (1 : ℝ))) =
        killAfter (a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X) (ts a) := by
      funext r ω k
      simp [a8pPhiH, EuclideanSpace.inner_single_right]
    have hξ' : IsProgressiveL2 (R N).P ℱ
        (fun r ω (k : (Finset.univ : Finset (Fin N × Fin d))) =>
          inner ℝ (a8pPhiH S R N ts φ r ω k) (EuclideanSpace.single a (1 : ℝ))) := by
      have h0 := gfb3_isProgressiveL2_restrict_univ (hkill a)
      rw [← hfun] at h0
      exact h0
    have := gfb3_pair_ito hF.brownian hMart (EuclideanSpace.single a (1 : ℝ)) hξ' hT0
    rw [hfun] at this
    filter_upwards [this] with ω h
    simpa [EuclideanSpace.inner_single_right] using h
  filter_upwards [ae_all_iff.2 hcoord] with ω h
  ext a
  exact h a

end Glue2

end HRS.Main.A8P
