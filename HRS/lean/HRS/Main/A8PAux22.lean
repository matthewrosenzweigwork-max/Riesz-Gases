import HRS.Main.A8PAux21

/-!
# Packet A8P, part 22: the smooth-metric core estimate at fixed `N`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

variable {d : ℕ}

theorem a8p_vec_meas {Ω' : Type*} {m : MeasurableSpace Ω'} {q : ℕ} (f : Fin q → Ω' → ℝ)
    (hf : ∀ a, Measurable (f a)) :
    Measurable fun ω => (WithLp.toLp 2 fun a => f a ω : EuclideanSpace ℝ (Fin q)) :=
  (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 hf)

theorem a8p_flucPair_meas {Ω' : Type*} {m : MeasurableSpace Ω'} {N : ℕ} {Y : Ω' → Config d N}
    (hY : Measurable Y) {ψ : Torus d → ℝ} (hψ : Continuous ψ) (ρ : Torus d → ℝ) :
    Measurable fun ω => flucPair (Y ω) ρ ψ := by
  unfold flucPair pair
  simp only [gfb2_integral_empirical]
  refine Measurable.sub (measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)) measurable_const
  exact hψ.measurable.comp ((measurable_pi_apply i).comp hY)

/-- The scaled initial statistics. -/
def a8pIemp (S : MainData d) (R : ∀ N, Realization d N) (N : ℕ) {q : ℕ} (ts : Fin q → ℝ)
    (φ : Fin q → Torus d → ℝ) (ω : (R N).Ω) : EuclideanSpace ℝ (Fin q) :=
  WithLp.toLp 2 fun a => S.sigma N * flucPair ((R N).X 0 ω) (S.ρ N 0)
    (propagator (S.dyn N) (S.ρ N) 0 (ts a) (φ a))

/-- The surrogate initial statistics. -/
def a8pItil (S : MainData d) (R : ∀ N, Realization d N) (N : ℕ) {q : ℕ} (ts : Fin q → ℝ)
    (φ : Fin q → Torus d → ℝ) (ω : (R N).Ω) : EuclideanSpace ℝ (Fin q) :=
  WithLp.toLp 2 fun a => S.AN N * (R N).η ω (propagator (S.dyn N) (S.ρ N) 0 (ts a) (φ a))

/-- The scaled remainders. -/
def a8pRem (S : MainData d) (R : ∀ N, Realization d N) (N : ℕ) {q : ℕ} (ts : Fin q → ℝ)
    (φ : Fin q → Torus d → ℝ) (ω : (R N).Ω) : EuclideanSpace ℝ (Fin q) :=
  WithLp.toLp 2 fun a => S.sigma N * ∫ r in (0 : ℝ)..(ts a),
    flucInteraction (S.dyn N) (a8pF S N ts φ a r) ((R N).X (Real.toNNReal r) ω) (S.ρ N r)

section Core

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ} {Ca Λ₁ : ℝ}

/-- The decomposition `Z = I + M + R` and the integrability/size of the remainder. -/
theorem a8p_decomp (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 2 ≤ N)
    {ℱ : Filtration ℝ (R N).mΩ} {W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution (R N).P ℱ W' (R N).W (R N).X)
    {q : ℕ} (ts : Fin q → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Torus d → ℝ)
    (hφc : ∀ a, Continuous (φ a)) (hφ : ∀ a, MemSobolev (PDE.mStar d : ℝ) (φ a)) :
    ∀ᵐ ω ∂(R N).P, fluctStat (S.sigma N) (R N).X (S.ρ N) ts φ ω =
      a8pIemp S R N ts φ ω +
        vectorItoIntegral (R N).P ℱ W'
          (fun a => killAfter (a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X) (ts a))
          S.T ω + a8pRem S R N ts φ ω := by
  have hN1 : 1 ≤ N := by omega
  obtain ⟨-, hMid⟩ := a8p_vector_mart hspec hCa hS hN1 hF ts hts φ hφc hφ
  have hdual := fun a => a8p_dual_coord hspec hCa hS hN (hts a) (hφc a) (hφ a) hF
  filter_upwards [hMid, ae_all_iff.2 hdual] with ω hM hD
  ext a
  have hD' : flucPair ((R N).X (Real.toNNReal (ts a)) ω) (S.ρ N (ts a)) (φ a) =
      flucPair ((R N).X 0 ω) (S.ρ N 0) (propagator (S.dyn N) (S.ρ N) 0 (ts a) (φ a)) +
      empiricalMartingale (R N).P ℱ W' (S.dyn N) (ts a) (a8pF S N ts φ a) (R N).X
        ((Real.toNNReal (ts a) : ℝ≥0) : ℝ) ω +
      ∫ r in (0 : ℝ)..(ts a), flucInteraction (S.dyn N) (a8pF S N ts φ a r)
        ((R N).X (Real.toNNReal r) ω) (S.ρ N r) := hD a
  have hMa := hM a
  simp only [fluctStat, a8pIemp, a8pRem, PiLp.add_apply]
  unfold flucPair at hD' ⊢
  linear_combination (S.sigma N) * hD' - hMa

end Core

end HRS.Main.A8P
