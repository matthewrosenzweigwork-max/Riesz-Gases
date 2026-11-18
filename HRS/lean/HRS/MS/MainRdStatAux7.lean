import HRS.MS.MainRdStatAux6

/-!
# SA2, packet 6b: the covariance of the martingale versus the surrogate covariance

* `sa2U`, `sa2Rho`: the truncated gradient components and the clamped density;
* `sa2_sb_isDet`: `Σ̄` is a deterministic covariance density (`IsDetCovMatrix`);
* `sa2_sigma_eq`: the Gaussian covariance of the surrogate (`noiseCovW`) is `∫_0^T Σ̄`;
* `sa2_Sg_entry`: `Σ_r^{ab} = 2q_N ⟨h_{ab}^r, μ_N^r⟩`, so that `Σ - Σ̄ = 2q_N ⟨h_{ab}^r, μ_N^r - ρ_r⟩`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS.Whole HRS.Whole.AppendixA HRS.Uniform HRS.GF
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MainRdStat

variable {d : ℕ}

/-- The gradient components of `U^{r,t_a}φ_a`, cut off to `r ∈ [0,t_a]`. -/
def sa2U (S : WholeMainData d) (N : ℕ) {q : ℕ} (ts : Fin q → ℝ) (φ : Fin q → Euc d → ℝ) (a : Fin q)
    (j : Fin d) (r : ℝ) (x : Euc d) : ℝ :=
  if r ∈ Set.Icc (0 : ℝ) (ts a) then gradient (propagatorW (S.coeff N) r (ts a) (φ a)) x j else 0

/-- The mean-field density with the time clamped to `[0,T]` (a probability density for every `r`). -/
def sa2Rho (S : WholeMainData d) (N : ℕ) (r : ℝ) (x : Euc d) : ℝ :=
  S.ρ N (HRS.MP.RdRem.mrrClamp S.T r) x

theorem sa2_inner_eq_sum (f g : Euc d → ℝ) (x : Euc d) :
    inner ℝ (gradient f x) (gradient g x) = ∑ j, gradient f x j * gradient g x j := by
  rw [PiLp.inner_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [RCLike.inner_apply, conj_trivial]
  ring

section Cov

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {r mV : ℕ}
  {𝔈 : ℕ → ℝ}

theorem sa2_sb_isDet (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) {N : ℕ} (hN : 1 ≤ N) {q : ℕ}
    (ts : Fin q → ℝ) (φ : Fin q → Euc d → ℝ) {B : Fin q → ℝ} (hB0 : ∀ a, 0 ≤ B a)
    (hB : ∀ a, ∀ rr ∈ Set.Icc (0 : ℝ) (ts a), MemCb 2 (propagatorW (S.coeff N) rr (ts a) (φ a)) ∧
      cbNorm 2 (propagatorW (S.coeff N) rr (ts a) (φ a)) ≤ B a) :
    IsDetCovMatrix S.T (sa2SigBar ts (sa2U S N ts φ) (sa2Rho S N) (2 * S.qN N)) := by
  have hT : 0 ≤ S.T := S.hT.le
  refine sa2_sigBar_isDet (B := B) (fun a j => ?_) (HRS.MP.RdRem.mrr_rho_meas hS hN) hB0
    (fun a j rr x => ?_) (fun rr => ?_) (by have := sa2_q_nonneg S N; positivity) S.T
  · exact HRS.MP.RdMart.mrm_meas_grad (S.coeff N) (ts a) (φ a) j
  · unfold sa2U
    by_cases h : rr ∈ Set.Icc (0 : ℝ) (ts a)
    · rw [if_pos h]
      exact (sa2_grad_coord_le (hB a rr h).1 x j).trans (hB a rr h).2
    · rw [if_neg h]; simpa using hB0 a
  · exact (hS.mean_field.solution N hN).density _ (HRS.MP.RdRem.mrrClamp_mem hT rr)

theorem sa2_sigma_eq (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) {N : ℕ} {q : ℕ}
    (ts : Fin q → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Euc d → ℝ) :
    (Matrix.of fun a b => noiseCovW (S.coeff N) (S.qN N) (ts a) (ts b) (φ a) (φ b)) =
      integratedCov S.T (sa2SigBar ts (sa2U S N ts φ) (sa2Rho S N) (2 * S.qN N)) := by
  have hT : 0 ≤ S.T := S.hT.le
  ext a b
  simp only [Matrix.of_apply, integratedCov]
  unfold noiseCovW
  set m : ℝ := min (ts a) (ts b) with hm
  have hmT : m ≤ S.T := (min_le_left _ _).trans (hts a).2
  set J : ℝ → ℝ := fun σ => ∫ x, inner ℝ (gradient (propagatorW (S.coeff N) σ (ts a) (φ a)) x)
    (gradient (propagatorW (S.coeff N) σ (ts b) (φ b)) x) * (S.coeff N).ρ σ x with hJ
  have hpt : ∀ σ, sa2SigBar ts (sa2U S N ts φ) (sa2Rho S N) (2 * S.qN N) σ a b =
      (Set.Ico 0 m).indicator (fun σ => 2 * S.qN N * J σ) σ := by
    intro σ
    unfold sa2SigBar
    simp only [Matrix.of_apply]
    by_cases hσ : σ ∈ Set.Ico 0 m
    · rw [Set.indicator_of_mem hσ, if_pos ⟨hσ.1, hσ.2⟩]
      have h1 : σ ∈ Set.Icc (0 : ℝ) (ts a) := ⟨hσ.1, (hσ.2.trans_le (min_le_left _ _)).le⟩
      have h2 : σ ∈ Set.Icc (0 : ℝ) (ts b) := ⟨hσ.1, (hσ.2.trans_le (min_le_right _ _)).le⟩
      have hσT : σ ∈ Set.Icc (0 : ℝ) S.T := ⟨hσ.1, (hσ.2.trans_le hmT).le⟩
      congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only [sa2U, if_pos h1, if_pos h2, sa2Rho, HRS.MP.RdRem.mrrClamp_of_mem hσT,
        sa2_inner_eq_sum]
      rfl
    · rw [Set.indicator_of_notMem hσ, if_neg]
      intro h
      exact hσ ⟨h.1, h.2⟩
  simp_rw [hpt]
  rw [setIntegral_indicator measurableSet_Ico]
  have hsub : Set.Icc (0 : ℝ) S.T ∩ Set.Ico 0 m = Set.Ico 0 m := by
    refine Set.inter_eq_right.2 fun σ hσ => ⟨hσ.1, (hσ.2.trans_le hmT).le⟩
  rw [hsub, ← integral_Icc_eq_integral_Ico, integral_const_mul]

/-- the killed covariance density of the scaled empirical martingales -/
def sa2Sg (S : WholeMainData d) (R : ∀ N, RealizationRd d N) (N : ℕ) {q : ℕ} (ts : Fin q → ℝ)
    (φ : Fin q → Euc d → ℝ) : ℝ → (R N).Ω → Matrix (Fin q) (Fin q) ℝ :=
  killedCovMatrix (fun a => sa2Phi S (ts a) (φ a) (R N).X) ts

theorem sa2_Sg_entry {N : ℕ} (hN : 0 < N) {q : ℕ} (ts : Fin q → ℝ) (φ : Fin q → Euc d → ℝ)
    (ζ : (R N).Ω) (a b : Fin q) {rr : ℝ} (hrr : 0 ≤ rr ∧ rr < min (ts a) (ts b)) :
    sa2Sg S R N ts φ rr ζ a b = 2 * S.qN N * HRS.Whole.pair (HRS.Whole.empirical ((R N).X (Real.toNNReal rr) ζ))
      (fun x => ∑ j, sa2U S N ts φ a j rr x * sa2U S N ts φ b j rr x) := by
  have h1 : rr ∈ Set.Icc (0 : ℝ) (ts a) := ⟨hrr.1, (hrr.2.trans_le (min_le_left _ _)).le⟩
  have h2 : rr ∈ Set.Icc (0 : ℝ) (ts b) := ⟨hrr.1, (hrr.2.trans_le (min_le_right _ _)).le⟩
  unfold sa2Sg killedCovMatrix
  simp only [Matrix.of_apply, if_pos hrr.2]
  rw [HRS.Whole.pair_empirical hN]
  set c : ℝ := S.sigma N * (Real.sqrt (2 * S.invβ N) / N) with hc
  have hc2 : c ^ 2 * N = 2 * S.qN N := by
    rw [sa2_q_eq, hc, mul_pow, div_pow, Real.sq_sqrt (by have := S.hinvβ N; positivity)]
    have : (N : ℝ) ≠ 0 := by positivity
    field_simp
  have hsum : ∑ k : Fin N × Fin d, sa2Phi S (ts a) (φ a) (R N).X rr ζ k *
      sa2Phi S (ts b) (φ b) (R N).X rr ζ k =
      c ^ 2 * ∑ i : Fin N, ∑ j : Fin d, sa2U S N ts φ a j rr ((R N).X (Real.toNNReal rr) ζ i) *
        sa2U S N ts φ b j rr ((R N).X (Real.toNNReal rr) ζ i) := by
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [sa2Phi, HRS.MH.DualityRd.truncGradIntegrand, Pi.smul_apply, smul_eq_mul, if_pos h1, if_pos h2,
      sa2U, gradComp]
    ring
  rw [hsum]
  have : (N : ℝ) * ((N : ℝ)⁻¹ * ∑ i : Fin N, ∑ j : Fin d, sa2U S N ts φ a j rr ((R N).X (Real.toNNReal rr) ζ i) *
        sa2U S N ts φ b j rr ((R N).X (Real.toNNReal rr) ζ i)) =
      ∑ i : Fin N, ∑ j : Fin d, sa2U S N ts φ a j rr ((R N).X (Real.toNNReal rr) ζ i) *
        sa2U S N ts φ b j rr ((R N).X (Real.toNNReal rr) ζ i) := by
    field_simp
  calc c ^ 2 * ∑ i : Fin N, ∑ j : Fin d, _ = c ^ 2 * ((N : ℝ) * ((N : ℝ)⁻¹ * ∑ i : Fin N, ∑ j : Fin d,
        sa2U S N ts φ a j rr ((R N).X (Real.toNNReal rr) ζ i) *
          sa2U S N ts φ b j rr ((R N).X (Real.toNNReal rr) ζ i))) := by rw [this]
    _ = 2 * S.qN N * ((N : ℝ)⁻¹ * ∑ i : Fin N, ∑ j : Fin d,
        sa2U S N ts φ a j rr ((R N).X (Real.toNNReal rr) ζ i) *
          sa2U S N ts φ b j rr ((R N).X (Real.toNNReal rr) ζ i)) := by
        rw [← hc2]; ring

end Cov

end HRS.MS.MainRdStat
