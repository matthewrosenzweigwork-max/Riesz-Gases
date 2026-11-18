import HRS.Main.A8PAux19

/-!
# Packet A8P, part 20: the vector martingale of the scaled empirical martingales
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

variable {d : ℕ}

section VecMart

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ} {Ca Λ₁ : ℝ}

theorem a8p_phi_progressive (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 1 ≤ N)
    {ℱ : Filtration ℝ (R N).mΩ} (hprog : IsProgressive ℱ (ofNNRealTime (R N).X))
    {t : ℝ} (ht : t ∈ Set.Icc 0 S.T) {φ : Torus d → ℝ} (hφc : Continuous φ)
    (hφ : MemSobolev (PDE.mStar d : ℝ) φ) :
    IsProgressiveL2 (R N).P ℱ
      (a8pPhi (S.dyn N) (S.sigma N) t (fun r => propagator (S.dyn N) (S.ρ N) r t φ) (R N).X) := by
  obtain ⟨-, hcl, -⟩ := a8p_adj_pkg hspec hCa hS hN ht hφc hφ
  have h := isProgressiveL2_empiricalNoiseIntegrand (P := (R N).P) (ℱ := ℱ) (D := S.dyn N)
    hprog ht.1 hcl.isC12Test
  have h2 := h.smul (S.sigma N)
  exact h2

theorem a8p_vector_mart (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 1 ≤ N)
    {ℱ : Filtration ℝ (R N).mΩ} {W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution (R N).P ℱ W' (R N).W (R N).X)
    {q : ℕ} (ts : Fin q → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Torus d → ℝ)
    (hφc : ∀ a, Continuous (φ a)) (hφ : ∀ a, MemSobolev (PDE.mStar d : ℝ) (φ a)) :
    IsVectorMartingaleWithCovariation (R N).P ℱ S.T
      (vectorItoIntegral (R N).P ℱ W'
        (fun a => killAfter (a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X) (ts a)))
      (killedCovMatrix (fun a => a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X) ts) ∧
    ∀ᵐ ω ∂(R N).P, ∀ a,
      vectorItoIntegral (R N).P ℱ W'
        (fun a => killAfter (a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X) (ts a))
          S.T ω a =
        S.sigma N * empiricalMartingale (R N).P ℱ W' (S.dyn N) (ts a) (a8pF S N ts φ a) (R N).X
          ((Real.toNNReal (ts a) : ℝ≥0) : ℝ) ω := by
  have hΦ : ∀ a, IsProgressiveL2 (R N).P ℱ
      (a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X) := fun a =>
    a8p_phi_progressive hspec hCa hS hN hF.progressive (hts a) (hφc a) (hφ a)
  obtain ⟨hmart, hae⟩ := several_times_covariation (R N).P hF.brownian
    (fun a => a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X) hΦ ts
    (fun a => (hts a).1) S.T (fun a => (hts a).2)
  refine ⟨hmart, ?_⟩
  have hbase : ∀ a, IsProgressiveL2 (R N).P ℱ
      (empiricalNoiseIntegrand (S.dyn N) (ts a) (a8pF S N ts φ a) (R N).X) := fun a => by
    obtain ⟨-, hcl, -⟩ := a8p_adj_pkg hspec hCa hS hN (hts a) (hφc a) (hφ a)
    exact isProgressiveL2_empiricalNoiseIntegrand (P := (R N).P) (ℱ := ℱ) (D := S.dyn N)
      hF.progressive (hts a).1 hcl.isC12Test
  have hsm := fun a => itoIntegral_smul hF.brownian (hbase a) (S.sigma N)
  filter_upwards [hae, ae_all_iff.2 hsm] with ω h1 h2 a
  rw [h1 a]
  have := h2 a (ts a)
  unfold empiricalMartingale
  rw [Real.coe_toNNReal _ (hts a).1]
  exact this

end VecMart

end HRS.Main.A8P
