import HRS.Main.A8PAux22

/-!
# Packet A8P, part 23: the remainder and initial-difference terms; the smooth core
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

variable {d : ℕ}

theorem a8p_abs_integral_le {Ω' : Type*} {m : MeasurableSpace Ω'} {P : Measure Ω'}
    {g : Ω' → ℝ} (hg : AEMeasurable g P) {B : ℝ} (hB : 0 ≤ B)
    (h : ∫⁻ ω, ENNReal.ofReal |g ω| ∂P ≤ ENNReal.ofReal B) :
    Integrable g P ∧ ∫ ω, |g ω| ∂P ≤ B := by
  have hi : Integrable g P := by
    refine ⟨hg.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    refine lt_of_le_of_lt (le_of_eq ?_) (lt_of_le_of_lt h ENNReal.ofReal_lt_top)
    refine lintegral_congr fun ω => ?_
    rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
  refine ⟨hi, ?_⟩
  have e : ENNReal.ofReal (∫ ω, |g ω| ∂P) = ∫⁻ ω, ENNReal.ofReal |g ω| ∂P :=
    ofReal_integral_eq_lintegral_ofReal hi.abs (Eventually.of_forall fun ω => abs_nonneg _)
  rw [← e] at h
  exact (ENNReal.ofReal_le_ofReal_iff hB).1 h

section Core2

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ} {Ca Λ₁ : ℝ}

/-- The pathwise bound of the remainder vector. -/
theorem a8p_rem_norm_bound (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 2 ≤ N)
    {ℱ : Filtration ℝ (R N).mΩ} {W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution (R N).P ℱ W' (R N).W (R N).X)
    {C₀' Cq cT : ℝ} (hcom : A8CommSpec d S.s C₀' Cq) (hCq : 0 ≤ Cq) (hC : C₀' ≤ C₀) (hcT0 : 0 ≤ cT)
    (hcT : ∀ (M : Matrix (Fin d) (Fin d) ℝ), PDE.MatBound MB M → ∀ ψ : Torus d → ℝ, Torus.IsCk 2 ψ →
      MemSobolev (PDE.mStar d : ℝ) ψ →
        HasTransportBound d S.s (gfb2_v M ψ) (cT * sobolevNorm (PDE.mStar d : ℝ) ψ))
    {q : ℕ} (ts : Fin q → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Torus d → ℝ)
    (hφc : ∀ a, Continuous (φ a)) (hφ : ∀ a, MemSobolev (PDE.mStar d : ℝ) (φ a)) :
    ∀ᵐ ω ∂(R N).P, ‖a8pRem S R N ts φ ω‖ ≤
      (∑ a, S.sigma N * ((1 / 2) * (Cq * (cT * a8pK Λ₁ (ts a) (φ a))))) *
        ∫ r in Set.Icc (0 : ℝ) S.T, a8pEn S R N C₀ Λ r ω := by
  have hrem := fun a => a8p_rem_ae hspec hCa hS hN hF hcom hCq hC hcT0 hcT (hts a) (hφc a) (hφ a)
  have hσ := a8p_sigma_nonneg S N
  filter_upwards [ae_all_iff.2 hrem] with ω hω
  refine (a8p_norm_le_sum_abs _).trans ?_
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun a _ => ?_
  have h := hω a
  have e : (a8pRem S R N ts φ ω) a = S.sigma N * ∫ r in (0 : ℝ)..(ts a),
      flucInteraction (S.dyn N) (a8pF S N ts φ a r) ((R N).X (Real.toNNReal r) ω) (S.ρ N r) := rfl
  rw [e, abs_mul, abs_of_nonneg hσ, mul_assoc]
  exact mul_le_mul_of_nonneg_left h hσ

theorem a8p_Een (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 1 ≤ N)
    {ℱ : Filtration ℝ (R N).mΩ} (hprog : IsProgressive ℱ (ofNNRealTime (R N).X)) :
    Integrable (fun ω => ∫ r in Set.Icc (0 : ℝ) S.T, a8pEn S R N C₀ Λ r ω) (R N).P ∧
    ∫ ω, (∫ r in Set.Icc (0 : ℝ) S.T, a8pEn S R N C₀ Λ r ω) ∂(R N).P ≤ S.T * 𝔈 N := by
  obtain ⟨-, h2, h3⟩ := a8p_energy_integral hS hN hprog (C₀ := C₀) (Λ := Λ)
  have hnn : ∀ ω, 0 ≤ ∫ r in Set.Icc (0 : ℝ) S.T, a8pEn S R N C₀ Λ r ω := fun ω =>
    setIntegral_nonneg measurableSet_Icc fun r _ => a8pEn_nonneg S R N C₀ Λ r ω
  have hint : Integrable (fun ω => ∫ r in Set.Icc (0 : ℝ) S.T, a8pEn S R N C₀ Λ r ω) (R N).P := by
    refine ⟨h3.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    refine lt_of_le_of_lt (le_of_eq ?_) (lt_of_le_of_lt h2 ENNReal.ofReal_lt_top)
    refine lintegral_congr fun ω => ?_
    rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg (hnn ω)]
  refine ⟨hint, ?_⟩
  have e : ENNReal.ofReal (∫ ω, (∫ r in Set.Icc (0 : ℝ) S.T, a8pEn S R N C₀ Λ r ω) ∂(R N).P) =
      ∫⁻ ω, ENNReal.ofReal (∫ r in Set.Icc (0 : ℝ) S.T, a8pEn S R N C₀ Λ r ω) ∂(R N).P :=
    ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall hnn)
  rw [← e] at h2
  have hE0 : 0 ≤ 𝔈 N := (hS.energy.pos N hN).le
  exact (ENNReal.ofReal_le_ofReal_iff (by have := S.hT; positivity)).1 h2

end Core2

end HRS.Main.A8P
