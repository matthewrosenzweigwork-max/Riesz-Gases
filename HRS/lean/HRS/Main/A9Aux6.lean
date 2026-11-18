import HRS.Main.A9Aux5

/-!
# Packet A9, part 6: first moments of the remainder and martingale coordinates of one mode test
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A9

open HRS HRS.A33 HRS.Main.A8P HRS.GF HRS.Uniform

variable {d : ℕ}

section Mode

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ} {Ca Λ₁ : ℝ}

/-- First moment of one coordinate of the remainder vector. -/
theorem a9_rem_moment (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 2 ≤ N)
    {ℱ : Filtration ℝ (R N).mΩ} {W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution (R N).P ℱ W' (R N).W (R N).X)
    {C₀' Cq cT : ℝ} (hcom : A8CommSpec d S.s C₀' Cq) (hCq : 0 ≤ Cq) (hC : C₀' ≤ C₀) (hcT0 : 0 ≤ cT)
    (hcT : ∀ (M : Matrix (Fin d) (Fin d) ℝ), PDE.MatBound MB M → ∀ ψ : Torus d → ℝ, Torus.IsCk 2 ψ →
      MemSobolev (PDE.mStar d : ℝ) ψ →
        HasTransportBound d S.s (gfb2_v M ψ) (cT * sobolevNorm (PDE.mStar d : ℝ) ψ))
    {q : ℕ} (ts : Fin q → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Torus d → ℝ)
    (hφc : ∀ a, Continuous (φ a)) (hφ : ∀ a, MemSobolev (PDE.mStar d : ℝ) (φ a)) (a : Fin q) :
    ∫⁻ ω, ENNReal.ofReal |a8pRem S R N ts φ ω a| ∂(R N).P ≤
      ENNReal.ofReal (S.sigma N * ((1 / 2) * (Cq * (cT * a8pK Λ₁ (ts a) (φ a)))) * (S.T * 𝔈 N)) := by
  have hN1 : 1 ≤ N := by omega
  have hσ := a8p_sigma_nonneg S N
  have hK0 := a8pK_nonneg Λ₁ (ts a) (φ a)
  set cc : ℝ := S.sigma N * ((1 / 2) * (Cq * (cT * a8pK Λ₁ (ts a) (φ a)))) with hcc
  have hcc0 : 0 ≤ cc := by
    rw [hcc]; exact mul_nonneg hσ (mul_nonneg (by norm_num) (mul_nonneg hCq (mul_nonneg hcT0 hK0)))
  obtain ⟨hEint, hEle⟩ := a8p_Een hS hN1 (hF.progressive) (C₀ := C₀) (Λ := Λ)
  have hrem := a8p_rem_ae hspec hCa hS hN hF hcom hCq hC hcT0 hcT (hts a) (hφc a) (hφ a)
  have hbd : ∀ᵐ ω ∂(R N).P, |a8pRem S R N ts φ ω a| ≤
      cc * ∫ r in Set.Icc (0 : ℝ) S.T, a8pEn S R N C₀ Λ r ω := by
    filter_upwards [hrem] with ω h
    have e : (a8pRem S R N ts φ ω) a = S.sigma N * ∫ r in (0 : ℝ)..(ts a),
        flucInteraction (S.dyn N) (propagator (S.dyn N) (S.ρ N) r (ts a) (φ a))
          ((R N).X (Real.toNNReal r) ω) (S.ρ N r) := rfl
    rw [e, abs_mul, abs_of_nonneg hσ, hcc, mul_assoc]
    exact mul_le_mul_of_nonneg_left h hσ
  have hnn : ∀ ω, 0 ≤ ∫ r in Set.Icc (0 : ℝ) S.T, a8pEn S R N C₀ Λ r ω := fun ω =>
    setIntegral_nonneg measurableSet_Icc fun r _ => a8pEn_nonneg S R N C₀ Λ r ω
  calc ∫⁻ ω, ENNReal.ofReal |a8pRem S R N ts φ ω a| ∂(R N).P
      ≤ ∫⁻ ω, ENNReal.ofReal (cc * ∫ r in Set.Icc (0 : ℝ) S.T, a8pEn S R N C₀ Λ r ω) ∂(R N).P :=
        lintegral_mono_ae (by filter_upwards [hbd] with ω h using ENNReal.ofReal_le_ofReal h)
    _ = ENNReal.ofReal (∫ ω, (cc * ∫ r in Set.Icc (0 : ℝ) S.T, a8pEn S R N C₀ Λ r ω) ∂(R N).P) :=
        (ofReal_integral_eq_lintegral_ofReal (hEint.const_mul cc)
          (Eventually.of_forall fun ω => mul_nonneg hcc0 (hnn ω))).symm
    _ ≤ ENNReal.ofReal (cc * (S.T * 𝔈 N)) := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left hEle hcc0

/-- The diagonal covariation density of the killed martingale is bounded. -/
theorem a9_sigma_diag_le (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 2 ≤ N)
    {q : ℕ} (ts : Fin q → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Torus d → ℝ)
    (hφc : ∀ a, Continuous (φ a)) (hφ : ∀ a, MemSobolev (PDE.mStar d : ℝ) (φ a)) (a : Fin q)
    (r : ℝ) (ω : (R N).Ω) :
    0 ≤ killedCovMatrix (fun a => a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X) ts
        r ω a a ∧
    killedCovMatrix (fun a => a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X) ts
        r ω a a ≤
      2 * (S.sigma N ^ 2 * S.invβ N / N) * (d * (Ca * a8pK Λ₁ (ts a) (φ a))) ^ 2 := by
  have hN1 : 1 ≤ N := by omega
  have hq0 : 0 ≤ S.sigma N ^ 2 * S.invβ N / N := by
    have := S.hinvβ N
    positivity
  have hK0 := a8pK_nonneg Λ₁ (ts a) (φ a)
  have hB0 : 0 ≤ 2 * (S.sigma N ^ 2 * S.invβ N / N) * (d * (Ca * a8pK Λ₁ (ts a) (φ a))) ^ 2 := by
    positivity
  have hsum := a8pPhi_cov hN1 (S.dyn N) (S.sigma N) (ts a) (ts a) (a8pF S N ts φ a) (a8pF S N ts φ a)
    (R N).X r ω
  unfold killedCovMatrix
  simp only [Matrix.of_apply, min_self]
  by_cases hr : r < ts a
  · rw [if_pos hr, hsum]
    by_cases hmem : r ∈ Set.Icc 0 (ts a) ∧ r ∈ Set.Icc 0 (ts a)
    · rw [if_pos hmem]
      obtain ⟨-, hcl, hb⟩ := a8p_adj_pkg hspec hCa hS hN1 (hts a) (hφc a) (hφ a)
      obtain ⟨-, -, hcb⟩ := hb r hmem.1
      have hCk := hcl.c2 r hmem.1
      have : IsProbabilityMeasure (empirical ((R N).X (Real.toNNReal r) ω)) :=
        empirical_isProbabilityMeasure hN1 _
      have hpt : ∀ x, inner ℝ (Torus.grad (a8pF S N ts φ a r) x) (Torus.grad (a8pF S N ts φ a r) x) ≤
          (d * (Ca * a8pK Λ₁ (ts a) (φ a))) ^ 2 := by
        intro x
        rw [real_inner_self_eq_norm_sq]
        have h1 := a8p_grad_norm_le hCk x
        have h2 : (d : ℝ) * Torus.cbNorm 2 (propagator (S.dyn N) (S.ρ N) r (ts a) (φ a)) ≤
            d * (Ca * a8pK Λ₁ (ts a) (φ a)) :=
          mul_le_mul_of_nonneg_left hcb (Nat.cast_nonneg d)
        exact pow_le_pow_left₀ (norm_nonneg _) (h1.trans h2) 2
      have hint : ∫ x, inner ℝ (Torus.grad (a8pF S N ts φ a r) x) (Torus.grad (a8pF S N ts φ a r) x)
          ∂(empirical ((R N).X (Real.toNNReal r) ω)) ≤ (d * (Ca * a8pK Λ₁ (ts a) (φ a))) ^ 2 := by
        calc _ ≤ ∫ _x, (d * (Ca * a8pK Λ₁ (ts a) (φ a))) ^ 2 ∂(empirical ((R N).X (Real.toNNReal r) ω)) :=
              integral_mono_of_nonneg (Eventually.of_forall fun x => by
                rw [real_inner_self_eq_norm_sq]; positivity) (integrable_const _)
                (Eventually.of_forall hpt)
          _ = _ := by simp
      have hint0 : 0 ≤ ∫ x, inner ℝ (Torus.grad (a8pF S N ts φ a r) x) (Torus.grad (a8pF S N ts φ a r) x)
          ∂(empirical ((R N).X (Real.toNNReal r) ω)) :=
        integral_nonneg fun x => by rw [real_inner_self_eq_norm_sq]; positivity
      exact ⟨mul_nonneg (by positivity) hint0, mul_le_mul_of_nonneg_left hint (by positivity)⟩
    · rw [if_neg hmem]
      exact ⟨le_rfl, hB0⟩
  · rw [if_neg hr]
    exact ⟨le_rfl, hB0⟩

/-- Second moment of one martingale coordinate. -/
theorem a9_mart_moment (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 2 ≤ N)
    {ℱ : Filtration ℝ (R N).mΩ} {W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution (R N).P ℱ W' (R N).W (R N).X)
    {q : ℕ} (ts : Fin q → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Torus d → ℝ)
    (hφc : ∀ a, Continuous (φ a)) (hφ : ∀ a, MemSobolev (PDE.mStar d : ℝ) (φ a)) (a : Fin q) :
    MemLp (fun ω => vectorItoIntegral (R N).P ℱ W'
        (fun a => killAfter (a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X) (ts a))
          S.T ω a) 2 (R N).P ∧
    ∫ ω, (vectorItoIntegral (R N).P ℱ W'
        (fun a => killAfter (a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X) (ts a))
          S.T ω a) ^ 2 ∂(R N).P ≤
      S.T * (2 * (S.sigma N ^ 2 * S.invβ N / N) * (d * (Ca * a8pK Λ₁ (ts a) (φ a))) ^ 2) := by
  have hN1 : 1 ≤ N := by omega
  have hT0 : 0 ≤ S.T := S.hT.le
  obtain ⟨hmart, -⟩ := a8p_vector_mart hspec hCa hS hN1 hF ts hts φ hφc hφ
  set Mv := vectorItoIntegral (R N).P ℱ W'
    (fun a => killAfter (a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X) (ts a)) with hMv
  set Sg := killedCovMatrix (fun a => a8pPhi (S.dyn N) (S.sigma N) (ts a) (a8pF S N ts φ a) (R N).X) ts
    with hSg
  set B : ℝ := 2 * (S.sigma N ^ 2 * S.invβ N / N) * (d * (Ca * a8pK Λ₁ (ts a) (φ a))) ^ 2 with hB
  have hmem := hmart.sq_int S.T ⟨hT0, le_rfl⟩
  have hMT : MemLp (fun ω => Mv S.T ω a) 2 (R N).P :=
    hmem.mono ((EuclideanSpace.proj a).continuous.comp_aestronglyMeasurable hmem.aestronglyMeasurable)
      (ae_of_all _ fun ω => PiLp.norm_apply_le (Mv S.T ω) a)
  refine ⟨hMT, ?_⟩
  have hcov := hmart.covariation a a
  have htime := HRS.SimpleIntegrand.martingale_integral_eq_zero_time hcov S.T
  have hsq : Integrable (fun ω => Mv S.T ω a ^ 2) (R N).P := hMT.integrable_sq
  have hdiff := hcov.integrable S.T
  have hY : Integrable (fun ω => ∫ σ in Set.Icc 0 S.T, Sg σ ω a a) (R N).P := by
    have := hsq.sub hdiff
    refine this.congr (ae_of_all _ fun ω => ?_)
    simp only [Pi.sub_apply]; ring
  have h0 : ∫ ω, (Mv 0 ω a * Mv 0 ω a - ∫ σ in Set.Icc 0 (0 : ℝ), Sg σ ω a a) ∂(R N).P = 0 := by
    have : ∀ᵐ ω ∂(R N).P, (Mv 0 ω a * Mv 0 ω a - ∫ σ in Set.Icc 0 (0 : ℝ), Sg σ ω a a) = 0 := by
      filter_upwards [hmart.zero] with ω hω
      rw [hω]; simp
    rw [integral_congr_ae this]; simp
  have hsplit : ∫ ω, Mv S.T ω a ^ 2 ∂(R N).P = ∫ ω, (∫ σ in Set.Icc 0 S.T, Sg σ ω a a) ∂(R N).P := by
    have e := htime
    rw [h0] at e
    have e2 : ∫ ω, (Mv S.T ω a * Mv S.T ω a - ∫ σ in Set.Icc 0 S.T, Sg σ ω a a) ∂(R N).P =
        ∫ ω, Mv S.T ω a ^ 2 ∂(R N).P - ∫ ω, (∫ σ in Set.Icc 0 S.T, Sg σ ω a a) ∂(R N).P := by
      rw [← integral_sub hsq hY]
      refine integral_congr_ae (ae_of_all _ fun ω => ?_)
      simp only [sq]
    linarith
  rw [hsplit]
  have hYle : ∀ ω, ∫ σ in Set.Icc 0 S.T, Sg σ ω a a ≤ S.T * B := by
    intro ω
    have h1 : ∫ σ in Set.Icc 0 S.T, Sg σ ω a a ≤ ∫ _σ in Set.Icc 0 S.T, B :=
      integral_mono_of_nonneg (Eventually.of_forall fun σ =>
        (a9_sigma_diag_le hspec hCa hS hN ts hts φ hφc hφ a σ ω).1) (integrable_const _)
        (Eventually.of_forall fun σ => (a9_sigma_diag_le hspec hCa hS hN ts hts φ hφc hφ a σ ω).2)
    refine h1.trans (le_of_eq ?_)
    rw [setIntegral_const, smul_eq_mul]
    simp [Measure.real, Real.volume_Icc, hT0]
  have hYnn : ∀ ω, 0 ≤ ∫ σ in Set.Icc 0 S.T, Sg σ ω a a := fun ω =>
    setIntegral_nonneg measurableSet_Icc fun σ _ =>
      (a9_sigma_diag_le hspec hCa hS hN ts hts φ hφc hφ a σ ω).1
  calc ∫ ω, (∫ σ in Set.Icc 0 S.T, Sg σ ω a a) ∂(R N).P
      ≤ ∫ _ω, S.T * B ∂(R N).P :=
        integral_mono_of_nonneg (Eventually.of_forall hYnn) (integrable_const _)
          (Eventually.of_forall hYle)
    _ = S.T * B := by simp

end Mode

end HRS.Main.A9
