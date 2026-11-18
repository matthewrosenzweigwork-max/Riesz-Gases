import HRS.Main.A8PAux17

/-!
# Packet A8P, part 18: the expected covariance discrepancy
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A8P

open HRS.GF HRS.Uniform

variable {d : ℕ}

theorem a8p_affine_integral {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (e : α → ℝ) (he : Integrable e μ) (k c1 c2 : ℝ) :
    Integrable (fun x => k * (c1 + c2 * e x)) μ ∧
      ∫ x, k * (c1 + c2 * e x) ∂μ = k * (μ.real Set.univ * c1 + c2 * ∫ x, e x ∂μ) := by
  have h1 : Integrable (fun x => c1 + c2 * e x) μ := (integrable_const c1).add (he.const_mul c2)
  refine ⟨h1.const_mul k, ?_⟩
  rw [integral_const_mul, integral_add (integrable_const c1) (he.const_mul c2), integral_const_mul,
    integral_const, smul_eq_mul]

section CovCost

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ} {Ca Λ₁ : ℝ}

/-- The covariance cost constant. -/
def a8pCovCost (S : MainData d) (N : ℕ) (Cq Cp Ca Λ₁ Λ E : ℝ) {q : ℕ} (ts : Fin q → ℝ)
    (φ : Fin q → Torus d → ℝ) : ℝ :=
  ∑ a, ∑ b, 2 * (S.sigma N ^ 2 * S.invβ N / N) *
    (S.T * (Cq * (2 * d * (Ca * a8pK Λ₁ (ts a) (φ a)) * (Ca * a8pK Λ₁ (ts b) (φ b))) * smearScale d N Λ) +
      Cq * (Cp * a8pK Λ₁ (ts a) (φ a) * a8pK Λ₁ (ts b) (φ b)) * (S.T * Real.sqrt E))

/-- The killed covariance density of the scaled empirical martingales. -/
def a8pSg (S : MainData d) (R : ∀ N, Realization d N) (N : ℕ) {q : ℕ} (ts : Fin q → ℝ)
    (φ : Fin q → Torus d → ℝ) : ℝ → (R N).Ω → Matrix (Fin q) (Fin q) ℝ :=
  killedCovMatrix (fun a => a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X) ts

/-- The deterministic covariance density of the surrogate. -/
def a8pSb (S : MainData d) (N : ℕ) {q : ℕ} (ts : Fin q → ℝ) (φ : Fin q → Torus d → ℝ) :
    ℝ → Matrix (Fin q) (Fin q) ℝ :=
  a8pSigBar ts (a8pG ts (a8pF S N ts φ)) (fun r => S.ρ N (Q54c.clampT S.T r))
    (2 * (S.sigma N ^ 2 * S.invβ N / N))

theorem a8p_cov_cost_gen (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 2 ≤ N)
    {C₀' Cq Cp : ℝ} (hcom : A8CommSpec d S.s C₀' Cq) (hCq : 0 ≤ Cq) (hC : C₀' ≤ C₀) (hCp0 : 0 ≤ Cp)
    (hCp : ∀ f g : Torus d → ℝ, Torus.IsCk 2 f → Torus.IsCk 2 g →
      MemSobolev (PDE.mStar d : ℝ) f → MemSobolev (PDE.mStar d : ℝ) g →
      HasFiniteHomSobolev (((d : ℝ) - S.s) / 2) (fun x => inner ℝ (Torus.grad f x) (Torus.grad g x)) ∧
      homSobolev (((d : ℝ) - S.s) / 2) (fun x => inner ℝ (Torus.grad f x) (Torus.grad g x)) ≤
        Cp * sobolevNorm (PDE.mStar d : ℝ) f * sobolevNorm (PDE.mStar d : ℝ) g)
    {q : ℕ} (ts : Fin q → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Torus d → ℝ)
    (hφc : ∀ a, Continuous (φ a)) (hφ : ∀ a, MemSobolev (PDE.mStar d : ℝ) (φ a))
    {ℱ : Filtration ℝ (R N).mΩ} (hprog : IsProgressive ℱ (ofNNRealTime (R N).X))
    (hnull : NullContactOccupation (R N).P S.T (R N).X)
    (F : ℝ → (R N).Ω → ℝ) (hF0 : ∀ r ω, 0 ≤ F r ω)
    (hFle : ∀ r ω, F r ω ≤ ∑ a, ∑ b, |a8pSg S R N ts φ r ω a b - a8pSb S N ts φ r a b|) :
    ∫ ω, (∫ σ in Set.Icc (0 : ℝ) S.T, F σ ω) ∂(R N).P ≤
      a8pCovCost S N Cq Cp Ca Λ₁ Λ (𝔈 N) ts φ := by
  have hN1 : 1 ≤ N := by omega
  have hT0 : 0 ≤ S.T := S.hT.le
  obtain ⟨hsqi, hsqint, hsqle⟩ := a8p_sqrt_energy hS hN1 hprog (C₀ := C₀) (Λ := Λ)
  set Sg := a8pSg S R N ts φ with hSg
  set sb := a8pSb S N ts φ with hsb
  set qq : ℝ := S.sigma N ^ 2 * S.invβ N / N with hqq
  have hqq0 : 0 ≤ qq := by
    have := S.hinvβ N
    positivity
  set c1 : Fin q → Fin q → ℝ := fun a b =>
    Cq * (2 * d * (Ca * a8pK Λ₁ (ts a) (φ a)) * (Ca * a8pK Λ₁ (ts b) (φ b))) * smearScale d N Λ with hc1
  set c2 : Fin q → Fin q → ℝ := fun a b =>
    Cq * (Cp * a8pK Λ₁ (ts a) (φ a) * a8pK Λ₁ (ts b) (φ b)) with hc2
  have hsm : 0 ≤ smearScale d N Λ := by
    unfold smearScale
    exact Real.rpow_nonneg (by have : (0 : ℝ) ≤ N := Nat.cast_nonneg N; have := a8p_Lam_ge_one hS; positivity) _
  have hc20 : ∀ a b, 0 ≤ c2 a b := fun a b => by
    have := a8pK_nonneg Λ₁ (ts a) (φ a)
    have := a8pK_nonneg Λ₁ (ts b) (φ b)
    simp only [hc2]; positivity
  have hc10 : ∀ a b, 0 ≤ c1 a b := fun a b => by
    have := a8pK_nonneg Λ₁ (ts a) (φ a)
    have := a8pK_nonneg Λ₁ (ts b) (φ b)
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    simp only [hc1]; positivity
  -- the pointwise bound in `(r, ω)`
  set Bd : (R N).Ω → ℝ := fun ω =>
    ∑ a, ∑ b, 2 * qq * (S.T * c1 a b + c2 a b * ∫ r in Set.Icc (0 : ℝ) S.T, Real.sqrt (a8pEn S R N C₀ Λ r ω))
    with hBd
  have hsqnn : ∀ ω, 0 ≤ ∫ r in Set.Icc (0 : ℝ) S.T, Real.sqrt (a8pEn S R N C₀ Λ r ω) := fun ω =>
    setIntegral_nonneg measurableSet_Icc fun r _ => Real.sqrt_nonneg _
  have hBdint : Integrable Bd (R N).P := by
    refine integrable_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ => ?_
    exact (a8p_affine_integral (R N).P _ hsqint (2 * qq) (S.T * c1 a b) (c2 a b)).1
  have hg : ∀ᵐ ω ∂(R N).P, (∫ σ in Set.Icc (0 : ℝ) S.T, F σ ω) ≤ Bd ω := by
    filter_upwards [hnull, hsqi] with ω hω hωi
    have hpt : ∀ᵐ r ∂(volume.restrict (Set.Icc (0 : ℝ) S.T)), ∀ a b,
        |Sg r ω a b - sb r a b| ≤ 2 * (S.sigma N ^ 2 * S.invβ N / N) *
          (Cq * (2 * d * (Ca * a8pK Λ₁ (ts a) (φ a)) * (Ca * a8pK Λ₁ (ts b) (φ b))) * smearScale d N Λ +
            Cq * (Cp * a8pK Λ₁ (ts a) (φ a) * a8pK Λ₁ (ts b) (φ b)) *
              Real.sqrt (a8pEn S R N C₀ Λ r ω)) :=
      a8p_cov_rpt hspec hCa hS hN hcom hCq hC hCp0 hCp ts hts φ hφc hφ ω hω
    set Bf : ℝ → ℝ := fun r => ∑ a, ∑ b, 2 * qq * (c1 a b + c2 a b * Real.sqrt (a8pEn S R N C₀ Λ r ω))
      with hBf
    have hIf : ∀ a b, Integrable (fun r => 2 * qq * (c1 a b + c2 a b * Real.sqrt (a8pEn S R N C₀ Λ r ω)))
        (volume.restrict (Set.Icc (0 : ℝ) S.T)) := fun a b =>
      (a8p_affine_integral _ _ hωi (2 * qq) (c1 a b) (c2 a b)).1
    have hBfint : IntegrableOn Bf (Set.Icc (0 : ℝ) S.T) :=
      integrable_finset_sum _ fun a _ => integrable_finset_sum _ fun b _ => hIf a b
    have hle : ∀ᵐ r ∂(volume.restrict (Set.Icc (0 : ℝ) S.T)), F r ω ≤ Bf r := by
      filter_upwards [hpt] with r hr
      refine (hFle r ω).trans ?_
      refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
      have := hr a b
      have e : 2 * qq * (c1 a b + c2 a b * Real.sqrt (a8pEn S R N C₀ Λ r ω)) =
          2 * (S.sigma N ^ 2 * S.invβ N / N) *
          (Cq * (2 * d * (Ca * a8pK Λ₁ (ts a) (φ a)) * (Ca * a8pK Λ₁ (ts b) (φ b))) * smearScale d N Λ +
            Cq * (Cp * a8pK Λ₁ (ts a) (φ a) * a8pK Λ₁ (ts b) (φ b)) *
              Real.sqrt (a8pEn S R N C₀ Λ r ω)) := by
        simp only [hc1, hc2, hqq] <;> ring
      rw [e]
      exact this
    have h1 := integral_mono_of_nonneg (μ := volume.restrict (Set.Icc (0 : ℝ) S.T))
      (Eventually.of_forall fun r => hF0 r ω) hBfint hle
    refine h1.trans (le_of_eq ?_)
    simp only [hBf, hBd]
    rw [integral_finset_sum _ (fun a _ => integrable_finset_sum _ fun b _ => hIf a b)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finset_sum _ (fun b _ => hIf a b)]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [(a8p_affine_integral _ _ hωi (2 * qq) (c1 a b) (c2 a b)).2]
    simp [Measure.real, Real.volume_Icc, hT0]
  have h2 := integral_mono_of_nonneg (μ := (R N).P)
    (Eventually.of_forall fun ω => setIntegral_nonneg measurableSet_Icc fun σ _ => hF0 σ ω)
    hBdint hg
  refine h2.trans ?_
  simp only [hBd]
  have hIb : ∀ a b, Integrable (fun ω => 2 * qq * (S.T * c1 a b + c2 a b *
      ∫ r in Set.Icc (0 : ℝ) S.T, Real.sqrt (a8pEn S R N C₀ Λ r ω))) (R N).P := fun a b =>
    (a8p_affine_integral (R N).P _ hsqint (2 * qq) (S.T * c1 a b) (c2 a b)).1
  rw [integral_finset_sum _ (fun a _ => integrable_finset_sum _ fun b _ => hIb a b)]
  unfold a8pCovCost
  refine Finset.sum_le_sum fun a _ => ?_
  rw [integral_finset_sum _ (fun b _ => hIb a b)]
  refine Finset.sum_le_sum fun b _ => ?_
  rw [(a8p_affine_integral (R N).P _ hsqint (2 * qq) (S.T * c1 a b) (c2 a b)).2]
  have hP1 : (R N).P.real Set.univ = 1 := by simp [Measure.real]
  rw [hP1, one_mul]
  have := mul_le_mul_of_nonneg_left hsqle (hc20 a b)
  have h2q : 0 ≤ 2 * qq := by positivity
  have e : 2 * (S.sigma N ^ 2 * S.invβ N / N) = 2 * qq := by simp only [hqq]
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ h2q
  simp only [hc1, hc2] at *
  nlinarith [this]

theorem a8p_cov_cost (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 2 ≤ N)
    {C₀' Cq Cp : ℝ} (hcom : A8CommSpec d S.s C₀' Cq) (hCq : 0 ≤ Cq) (hC : C₀' ≤ C₀) (hCp0 : 0 ≤ Cp)
    (hCp : ∀ f g : Torus d → ℝ, Torus.IsCk 2 f → Torus.IsCk 2 g →
      MemSobolev (PDE.mStar d : ℝ) f → MemSobolev (PDE.mStar d : ℝ) g →
      HasFiniteHomSobolev (((d : ℝ) - S.s) / 2) (fun x => inner ℝ (Torus.grad f x) (Torus.grad g x)) ∧
      homSobolev (((d : ℝ) - S.s) / 2) (fun x => inner ℝ (Torus.grad f x) (Torus.grad g x)) ≤
        Cp * sobolevNorm (PDE.mStar d : ℝ) f * sobolevNorm (PDE.mStar d : ℝ) g)
    {q : ℕ} (ts : Fin q → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Torus d → ℝ)
    (hφc : ∀ a, Continuous (φ a)) (hφ : ∀ a, MemSobolev (PDE.mStar d : ℝ) (φ a))
    {ℱ : Filtration ℝ (R N).mΩ} (hprog : IsProgressive ℱ (ofNNRealTime (R N).X))
    (hnull : NullContactOccupation (R N).P S.T (R N).X) :
    covDiscrepancyMatrix (R N).P S.T
      (killedCovMatrix (fun a => a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X) ts)
      (a8pSigBar ts (a8pG ts (a8pF S N ts φ)) (fun r => S.ρ N (Q54c.clampT S.T r))
        (2 * (S.sigma N ^ 2 * S.invβ N / N))) ≤
      a8pCovCost S N Cq Cp Ca Λ₁ Λ (𝔈 N) ts φ := by
  refine a8p_cov_cost_gen hspec hCa hS hN hcom hCq hC hCp0 hCp ts hts φ hφc hφ hprog hnull
    (fun r ω => s1Norm (a8pSg S R N ts φ r ω - a8pSb S N ts φ r)) (fun r ω => traceNormMatrix_nonneg _)
    (fun r ω => ?_)
  refine (a8p_s1Norm_le_sum _).trans (le_of_eq ?_)
  simp only [Matrix.sub_apply]

end CovCost

end HRS.Main.A8P
