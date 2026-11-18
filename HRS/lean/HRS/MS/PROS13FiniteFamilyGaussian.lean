import HRS.MS.PROS13QuadraticChaos
import HRS.MS.PROS13FamilyMoment

/-!
# S13: simultaneous actual Gaussian quadratic witnesses for finite kernel families

Every coordinate is constructed on the same ProductGaussian probability space.
The finite-rank approximants converge jointly in squared L2, even for atomic
reference measures. This does not yet assert the joint particle CLT or the
all-ONB Wick identity.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.R2Chaos
variable {d : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]

theorem pro_s13_generic_finite_family_actual_gaussian_L2_witness
    (I : ProductGaussian μ) {m : ℕ}
    (h : Fin m → Euc d → Euc d → ℝ)
    (hh : ∀ k, MemLp (fun z : Euc d × Euc d => h k z.1 z.2) 2 (μ.prod μ))
    (hs : ∀ k x y, h k x y = h k y x) :
    ∃ (Q : Fin m → I.Ω → ℝ),
      (∀ k, MemLp (Q k) 2 I.P ∧ InSecondChaos I.P I.ξ 3 (Q k)) ∧
      ∃ (r : Fin m → ℕ → ℕ)
        (c : (k : Fin m) → (j : ℕ) →
          Fin (r k j) → Fin (r k j) → ℝ)
        (u : (k : Fin m) → (j : ℕ) →
          Fin (r k j) → Euc d → ℝ),
        (∀ k j, IsR2FiniteRankData (c k j) (u k j)) ∧
        (∀ k, Tendsto
          (fun j => eLpNorm
            (fun z : Euc d × Euc d =>
              r2FiniteRankKernel (c k j) (u k j) z.1 z.2 - h k z.1 z.2)
            2 (μ.prod μ)) atTop (𝓝 0)) ∧
        Tendsto
          (fun j : ℕ => ∑ k : Fin m,
            ∫ ω : I.Ω,
              (((1 / 2 : ℝ) * ∑ a : Fin (r k j), ∑ b : Fin (r k j),
                  c k j a b *
                    (I.η (u k j a) ω * I.η (u k j b) ω -
                      ∫ ζ, I.η (u k j a) ζ * I.η (u k j b) ζ ∂I.P)) -
                  Q k ω) ^ 2 ∂I.P)
          atTop (𝓝 0) := by
  classical
  have hchoices : ∀ k : Fin m,
      ∃ Q : I.Ω → ℝ,
        MemLp Q 2 I.P ∧ InSecondChaos I.P I.ξ 3 Q ∧
        ∃ (r : ℕ → ℕ)
          (c : (j : ℕ) → Fin (r j) → Fin (r j) → ℝ)
          (u : (j : ℕ) → Fin (r j) → Euc d → ℝ),
          (∀ j, IsR2FiniteRankData (c j) (u j)) ∧
          Tendsto (fun j => eLpNorm
            (fun z : Euc d × Euc d =>
              r2FiniteRankKernel (c j) (u j) z.1 z.2 - h k z.1 z.2)
              2 (μ.prod μ)) atTop (𝓝 0) ∧
          Tendsto (fun j : ℕ => ∫ ω : I.Ω,
            (((1 / 2 : ℝ) * ∑ a : Fin (r j), ∑ b : Fin (r j), c j a b *
              (I.η (u j a) ω * I.η (u j b) ω -
                ∫ ζ, I.η (u j a) ζ * I.η (u j b) ζ ∂I.P)) -
              Q ω) ^ 2 ∂I.P) atTop (𝓝 0) :=
    fun k => pro_s13_generic_actual_second_chaos_witness I (h k) (hh k) (hs k)
  choose Q hQ hSecond hdata using hchoices
  choose r c u hd hK hlim using hdata
  refine ⟨Q, (fun k => ⟨hQ k, hSecond k⟩), r, c, u, hd, hK, ?_⟩
  have hsum := tendsto_finset_sum (Finset.univ : Finset (Fin m))
    (fun k _ => hlim k)
  simpa using hsum

end HRS.MS.R26T3
