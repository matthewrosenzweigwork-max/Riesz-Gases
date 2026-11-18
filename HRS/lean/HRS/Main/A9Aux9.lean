import HRS.Main.A9Aux8

/-!
# Packet A9, part 9: first moment of one coordinate of the Gaussian field `G^t_N`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A9

open HRS HRS.A33 HRS.PDE HRS.Main.A8P HRS.GF HRS.Uniform

variable {d : ℕ}

section GaussMode

variable {S : MainData d} {R : ∀ N, Realization d N} {Rg : PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ}
  {𝔈 : ℕ → ℝ} {Ca Λ₁ : ℝ}

/-- The noise covariance of one mode test is bounded by `2 q t (d Ca K)²`. -/
theorem a9_noiseCov_le (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 1 ≤ N)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) {φ : Torus d → ℝ} (hφc : Continuous φ)
    (hφ : MemSobolev (PDE.mStar d : ℝ) φ) :
    0 ≤ noiseCovariance (S.dyn N) (S.ρ N) (S.qN N) t φ φ ∧
    noiseCovariance (S.dyn N) (S.ρ N) (S.qN N) t φ φ ≤
      2 * S.qN N * t * (d * (Ca * a8pK Λ₁ t φ)) ^ 2 := by
  have hq := (a8p_q_bounds S hN).1
  obtain ⟨-, hcl, hb⟩ := a8p_adj_pkg hspec hCa hS hN ht hφc hφ
  have hK0 := a8pK_nonneg Λ₁ t φ
  set B0 : ℝ := (d * (Ca * a8pK Λ₁ t φ)) ^ 2 with hB0
  have hB00 : 0 ≤ B0 := by positivity
  have hinner : ∀ r ∈ Set.Icc (0 : ℝ) t,
      0 ≤ ∫ x, inner ℝ (Torus.grad (propagator (S.dyn N) (S.ρ N) r t φ) x)
        (Torus.grad (propagator (S.dyn N) (S.ρ N) r t φ) x) * S.ρ N r x ∧
      ∫ x, inner ℝ (Torus.grad (propagator (S.dyn N) (S.ρ N) r t φ) x)
        (Torus.grad (propagator (S.dyn N) (S.ρ N) r t φ) x) * S.ρ N r x ≤ B0 := by
    intro r hr
    have hrT : r ∈ Set.Icc (0 : ℝ) S.T := ⟨hr.1, hr.2.trans ht.2⟩
    have hdens := (hS.mean_field.solution N hN).density r hrT
    obtain ⟨-, -, hcb⟩ := hb r hr
    have hCk := hcl.c2 r hr
    have hint : Integrable (S.ρ N r) := by
      by_contra h
      have := hdens.integral_one
      rw [integral_undef h] at this
      exact absurd this (by norm_num)
    have hpt : ∀ x, inner ℝ (Torus.grad (propagator (S.dyn N) (S.ρ N) r t φ) x)
        (Torus.grad (propagator (S.dyn N) (S.ρ N) r t φ) x) ≤ B0 := by
      intro x
      rw [real_inner_self_eq_norm_sq]
      have h1 := a8p_grad_norm_le hCk x
      have h2 : (d : ℝ) * Torus.cbNorm 2 (propagator (S.dyn N) (S.ρ N) r t φ) ≤
          d * (Ca * a8pK Λ₁ t φ) := mul_le_mul_of_nonneg_left hcb (Nat.cast_nonneg d)
      exact pow_le_pow_left₀ (norm_nonneg _) (h1.trans h2) 2
    refine ⟨integral_nonneg fun x => mul_nonneg (by rw [real_inner_self_eq_norm_sq]; positivity)
      (hdens.nonneg x), ?_⟩
    calc _ ≤ ∫ x, B0 * S.ρ N r x :=
          integral_mono_of_nonneg (Eventually.of_forall fun x =>
            mul_nonneg (by rw [real_inner_self_eq_norm_sq]; positivity) (hdens.nonneg x))
            (hint.const_mul B0)
            (Eventually.of_forall fun x => mul_le_mul_of_nonneg_right (hpt x) (hdens.nonneg x))
      _ = B0 := by rw [integral_const_mul, hdens.integral_one, mul_one]
  have hT0 : 0 ≤ t := ht.1
  unfold noiseCovariance
  have hout0 : 0 ≤ ∫ r in Set.Icc 0 t, ∫ x, inner ℝ (Torus.grad (propagator (S.dyn N) (S.ρ N) r t φ) x)
      (Torus.grad (propagator (S.dyn N) (S.ρ N) r t φ) x) * S.ρ N r x :=
    setIntegral_nonneg measurableSet_Icc fun r hr => (hinner r hr).1
  have hout : (∫ r in Set.Icc 0 t, ∫ x, inner ℝ (Torus.grad (propagator (S.dyn N) (S.ρ N) r t φ) x)
      (Torus.grad (propagator (S.dyn N) (S.ρ N) r t φ) x) * S.ρ N r x) ≤ t * B0 := by
    have h1 : (∫ r in Set.Icc 0 t, ∫ x, inner ℝ (Torus.grad (propagator (S.dyn N) (S.ρ N) r t φ) x)
        (Torus.grad (propagator (S.dyn N) (S.ρ N) r t φ) x) * S.ρ N r x) ≤ ∫ _r in Set.Icc 0 t, B0 :=
      integral_mono_of_nonneg
        ((ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun r hr => (hinner r hr).1))
        (integrable_const _)
        ((ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun r hr => (hinner r hr).2))
    refine h1.trans (le_of_eq ?_)
    rw [setIntegral_const, smul_eq_mul]
    simp [Measure.real, Real.volume_Icc, hT0]
  exact ⟨mul_nonneg (by positivity) hout0, by
    calc 2 * S.qN N * _ ≤ 2 * S.qN N * (t * B0) := mul_le_mul_of_nonneg_left hout (by positivity)
      _ = _ := by ring⟩

/-- First moment of one coordinate of the Gaussian field. -/
theorem a9_gauss_coord_moment (hspec : A8AdjSpec d S.s Rg MB Λ VB ν₀ Ca Λ₁) (hCa : 0 ≤ Ca)
    (hS : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈) {N : ℕ} (hN : 1 ≤ N)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) (k : NonzeroLattice d)
    {νG : Measure (NegSobolev d (gammaIdx d : ℝ))}
    (hνG : IsLinearFieldNoise (S.dyn N) (S.ρ N) (S.qN N) t (gammaIdx d : ℝ) νG) :
    ∫⁻ F, ENNReal.ofReal |NegSobolev.coord F k| ∂νG ≤
      ENNReal.ofReal (Real.sqrt (2 * S.qN N * t * (d * (Ca * a8pK Λ₁ t (a9phi d k))) ^ 2)) := by
  obtain ⟨hprob, hcg, hcov⟩ := hνG
  haveI := hprob
  haveI : IsGaussian νG := hcg.1
  have hL : MemLp (fun F : NegSobolev d (gammaIdx d : ℝ) => NegSobolev.coord F k) 2 νG := by
    have e : (fun F : NegSobolev d (gammaIdx d : ℝ) => NegSobolev.coord F k) =
        fun F => innerSL ℝ (a9unit (gammaIdx d : ℝ) k) F := by
      funext F; rw [innerSL_apply_apply, a9unit_inner]
    rw [e]
    exact IsGaussian.memLp_dual νG (innerSL ℝ (a9unit (gammaIdx d : ℝ) k)) 2 (by simp)
  have hvar : ∫ F, NegSobolev.coord F k ^ 2 ∂νG = noiseCovariance (S.dyn N) (S.ρ N) (S.qN N) t
      (a9phi d k) (a9phi d k) := by
    rw [← hcov _ _ (a9phi_smooth k) (a9phi_smooth k)]
    refine integral_congr_ae (Eventually.of_forall fun F => ?_)
    simp only [a9_eval_phi, sq]
  have hle := (a9_noiseCov_le hspec hCa hS hN ht (a9phi_cont k) (a9phi_mem _ k)).2
  have hint : Integrable (fun F : NegSobolev d (gammaIdx d : ℝ) => |NegSobolev.coord F k|) νG :=
    (hL.integrable one_le_two).abs
  have e : ENNReal.ofReal (∫ F, |NegSobolev.coord F k| ∂νG) =
      ∫⁻ F, ENNReal.ofReal |NegSobolev.coord F k| ∂νG :=
    ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun F => abs_nonneg _)
  rw [← e]
  refine ENNReal.ofReal_le_ofReal ?_
  refine (a33_integral_abs_le (P := νG) _ hL).trans (Real.sqrt_le_sqrt ?_)
  rw [hvar]; exact hle

end GaussMode

end HRS.Main.A9
