import HRS.Main.A8PAux6
import HRS.Stochastic.DualityProof
import HRS.Stochastic.EmpiricalIto

/-!
# Packet A8P, part 7: the flow facts and the duality identity for one test (including `t = 0`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

variable {d : ℕ}

section Flow

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ}

theorem a8p_flow_facts (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ}
    (hN : 1 ≤ N) :
    IsContactStrongSolution (R N).P (S.dyn N) S.T (R N).X₀ (R N).W (R N).X ∧
    ((S.dyn N).M = 0 ∨ NullContactOccupation (R N).P S.T (R N).X) ∧
    ∀ᵐ ω ∂(R N).P, (R N).X 0 ω = (R N).X₀ ω := by
  have h := hS.flow N hN
  rcases h.flow with ⟨h1, -⟩ | ⟨-, -, -, -, h2⟩ | ⟨-, -, -, h3, h4⟩
  · exact ⟨h1.toContact, Or.inr (nullContactOccupation_of_strong h1), h1.init⟩
  · exact ⟨h2.toContact, Or.inr h2.occupation, h2.toContact.init⟩
  · exact ⟨h4, Or.inl h3, h4.init⟩



variable {Ca Λ₁ : ℝ}

/-- The duality identity for one test `φ` at a time `t ∈ [0,T]` (`t = 0` included, with the convention
`U^{0,0}φ = φ`, `M = 0`, `R = 0`). -/
theorem a8p_dual_coord (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 2 ≤ N) {t : ℝ}
    (ht : t ∈ Set.Icc 0 S.T) {φ : Torus d → ℝ} (hφc : Continuous φ)
    (hφ : MemSobolev (PDE.mStar d : ℝ) φ)
    {ℱ : Filtration ℝ (R N).mΩ} {W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution (R N).P ℱ W' (R N).W (R N).X) :
    ∀ᵐ ω ∂(R N).P,
      flucPair ((R N).X (Real.toNNReal t) ω) (S.ρ N t) φ =
        flucPair ((R N).X 0 ω) (S.ρ N 0) (propagator (S.dyn N) (S.ρ N) 0 t φ) +
        empiricalMartingale (R N).P ℱ W' (S.dyn N) t (fun r => propagator (S.dyn N) (S.ρ N) r t φ)
          (R N).X ((Real.toNNReal t : ℝ≥0) : ℝ) ω +
        ∫ r in (0 : ℝ)..t, flucInteraction (S.dyn N) (propagator (S.dyn N) (S.ρ N) r t φ)
          ((R N).X (Real.toNNReal r) ω) (S.ρ N r) := by
  classical
  have hN1 : 1 ≤ N := by omega
  haveI : NeZero N := ⟨by omega⟩
  obtain ⟨hCk, hcl, -⟩ := a8p_adj_pkg hspec hCa hS hN1 ht hφc hφ
  rcases ht.1.eq_or_lt with h0 | hpos
  · subst h0
    refine Eventually.of_forall fun ω => ?_
    have hterm : propagator (S.dyn N) (S.ρ N) 0 0 φ = φ := hcl.terminal
    rw [hterm]
    have : empiricalMartingale (R N).P ℱ W' (S.dyn N) 0
        (fun r => propagator (S.dyn N) (S.ρ N) r 0 φ) (R N).X ((Real.toNNReal 0 : ℝ≥0) : ℝ) ω = 0 := by
      unfold empiricalMartingale
      exact itoIntegral_of_nonpos (R N).P ℱ W' _ (by simp) ω
    rw [this, intervalIntegral.integral_same]
    simp
  · obtain ⟨hXc, hocc, -⟩ := a8p_flow_facts hS hN1
    have hV : Torus.IsCk 2 (S.dyn N).V := by
      have := hS.potential.1
      exact this.of_le (by exact_mod_cast (by omega : 2 ≤ PDE.mStar d + 3))
    have hdual := duality_identity_final S.hd hN hV ((hS.mean_field.solution N hN1))
      (a8p_regular3 hS hN1) hXc hF hocc ⟨hpos, ht.2⟩ hCk ⟨_, hcl⟩
    filter_upwards [hdual] with ω hω
    exact hω

end Flow

end HRS.Main.A8P
