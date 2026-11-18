import HRS.MS.MainRdStatAux11

/-!
# SA2, packet 7b: the trivial covariance bound, the smooth rate arithmetic, the per-`N` smooth theorem
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS.Whole HRS.Whole.AppendixA HRS.Uniform HRS.GF HRS.Whole.AppendixALemmas
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MainRdStat

variable {d : ℕ}

section Triv

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {r mV : ℕ}
  {𝔈 : ℕ → ℝ}

theorem sa2_U_bound {N : ℕ} {q : ℕ} {ts : Fin q → ℝ} {φ : Fin q → Euc d → ℝ} {B : Fin q → ℝ}
    (hB0 : ∀ a, 0 ≤ B a)
    (hB : ∀ a, ∀ rr ∈ Set.Icc (0 : ℝ) (ts a), MemCb 2 (propagatorW (S.coeff N) rr (ts a) (φ a)) ∧
      cbNorm 2 (propagatorW (S.coeff N) rr (ts a) (φ a)) ≤ B a) (a : Fin q) (j : Fin d) (rr : ℝ)
    (x : Euc d) : |sa2U S N ts φ a j rr x| ≤ B a := by
  unfold sa2U
  by_cases h : rr ∈ Set.Icc (0 : ℝ) (ts a)
  · rw [if_pos h]
    exact (sa2_grad_coord_le (hB a rr h).1 x j).trans (hB a rr h).2
  · rw [if_neg h]; simpa using hB0 a

/-- The trivial covariance cost. -/
theorem sa2_cov_triv (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) {N : ℕ} (hN : 1 ≤ N) {q : ℕ}
    (ts : Fin q → ℝ) (φ : Fin q → Euc d → ℝ) {B : Fin q → ℝ} (hB0 : ∀ a, 0 ≤ B a)
    (hB : ∀ a, ∀ rr ∈ Set.Icc (0 : ℝ) (ts a), MemCb 2 (propagatorW (S.coeff N) rr (ts a) (φ a)) ∧
      cbNorm 2 (propagatorW (S.coeff N) rr (ts a) (φ a)) ≤ B a) :
    covDiscrepancyMatrix (R N).P S.T (sa2Sg S R N ts φ)
        (sa2SigBar ts (sa2U S N ts φ) (sa2Rho S N) (2 * S.qN N)) ≤
      4 * S.qN N * d * S.T * (∑ a, B a) ^ 2 := by
  have hq := sa2_q_nonneg S N
  have hT0 : 0 ≤ S.T := S.hT.le
  have hN0 : 0 < N := by omega
  have hUb := fun a j rr x => sa2_U_bound (S := S) (N := N) (ts := ts) (φ := φ) hB0 hB a j rr x
  have hUm : ∀ a j, Measurable fun p : ℝ × Euc d => sa2U S N ts φ a j p.1 p.2 := fun a j =>
    HRS.MP.RdMart.mrm_meas_grad (S.coeff N) (ts a) (φ a) j
  have hρm := HRS.MP.RdRem.mrr_rho_meas hS hN
  have hρ : ∀ rr, HRS.Whole.IsProbDensity (sa2Rho S N rr) := fun rr =>
    (hS.mean_field.solution N hN).density _ (HRS.MP.RdRem.mrrClamp_mem hT0 rr)
  have hentry : ∀ (ζ : (R N).Ω) (σ : ℝ) (a b : Fin q),
      |(sa2Sg S R N ts φ σ ζ - sa2SigBar ts (sa2U S N ts φ) (sa2Rho S N) (2 * S.qN N) σ) a b| ≤
        4 * S.qN N * (d * (B a * B b)) := by
    intro ζ σ a b
    rw [Matrix.sub_apply]
    by_cases hab : 0 ≤ σ ∧ σ < min (ts a) (ts b)
    · have h1 := sa2_sigBar_entry_bound (ts := ts) (c := 2 * S.qN N) hUm hρm hB0 hUb hρ a b σ
      rw [sa2_Sg_entry hN0 ts φ ζ a b hab]
      set M : ℝ := d * (B a * B b) with hM
      have hp : |HRS.Whole.pair (HRS.Whole.empirical ((R N).X (Real.toNNReal σ) ζ))
          (fun x => ∑ j, sa2U S N ts φ a j σ x * sa2U S N ts φ b j σ x)| ≤ M := by
        rw [HRS.Whole.pair_empirical hN0, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (N : ℝ)⁻¹)]
        calc (N : ℝ)⁻¹ * |∑ i, ∑ j, sa2U S N ts φ a j σ ((R N).X (Real.toNNReal σ) ζ i) *
              sa2U S N ts φ b j σ ((R N).X (Real.toNNReal σ) ζ i)| ≤ (N : ℝ)⁻¹ * ∑ _i : Fin N, M := by
              refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
                (Finset.sum_le_sum fun i _ => sa2_sum_bound hUb a b σ _)) (by positivity)
          _ = M := by
              rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
              exact inv_mul_cancel_left₀ (by positivity) _
      rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * S.qN N)] at h1
      · calc |2 * S.qN N * HRS.Whole.pair (HRS.Whole.empirical ((R N).X (Real.toNNReal σ) ζ))
              (fun x => ∑ j, sa2U S N ts φ a j σ x * sa2U S N ts φ b j σ x) -
              sa2SigBar ts (sa2U S N ts φ) (sa2Rho S N) (2 * S.qN N) σ a b|
            ≤ |2 * S.qN N * HRS.Whole.pair (HRS.Whole.empirical ((R N).X (Real.toNNReal σ) ζ))
              (fun x => ∑ j, sa2U S N ts φ a j σ x * sa2U S N ts φ b j σ x)| +
              |sa2SigBar ts (sa2U S N ts φ) (sa2Rho S N) (2 * S.qN N) σ a b| := abs_sub _ _
          _ ≤ 2 * S.qN N * M + 2 * S.qN N * M := by
              refine add_le_add ?_ h1
              rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * S.qN N)]
              exact mul_le_mul_of_nonneg_left hp (by positivity)
          _ = 4 * S.qN N * M := by ring
    · rw [sa2_Sg_entry_zero ts φ ζ a b hab]
      simp only [sa2SigBar, Matrix.of_apply, if_neg hab, sub_self, abs_zero]
      have := hB0 a
      have := hB0 b
      positivity
  set K : ℝ := 4 * S.qN N * d * (∑ a, B a) ^ 2 with hK
  have hKs : ∀ (ζ : (R N).Ω) (σ : ℝ),
      s1Norm (sa2Sg S R N ts φ σ ζ - sa2SigBar ts (sa2U S N ts φ) (sa2Rho S N) (2 * S.qN N) σ) ≤ K := by
    intro ζ σ
    refine (HRS.Main.A8P.a8p_s1Norm_le_sum _).trans ?_
    calc _ ≤ ∑ a, ∑ b, 4 * S.qN N * (d * (B a * B b)) :=
          Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hentry ζ σ a b
      _ = K := by
          rw [hK, sq, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun b _ => ?_
          ring
  have hin : ∀ ζ : (R N).Ω, ∫ σ in Set.Icc (0 : ℝ) S.T,
      s1Norm (sa2Sg S R N ts φ σ ζ - sa2SigBar ts (sa2U S N ts φ) (sa2Rho S N) (2 * S.qN N) σ) ≤ K * S.T := by
    intro ζ
    calc _ ≤ ∫ σ in Set.Icc (0 : ℝ) S.T, K :=
          integral_mono_of_nonneg (ae_of_all _ fun σ => traceNormMatrix_nonneg _)
            (integrableOn_const (by simp)) (ae_of_all _ fun σ => hKs ζ σ)
      _ = K * S.T := by simp [Measure.real, Real.volume_Icc, hT0, mul_comm]
  unfold covDiscrepancyMatrix
  calc _ ≤ ∫ ζ, K * S.T ∂(R N).P :=
        integral_mono_of_nonneg (ae_of_all _ fun ζ => setIntegral_nonneg measurableSet_Icc
          fun σ _ => traceNormMatrix_nonneg _) (integrable_const _) (ae_of_all _ hin)
    _ = 4 * S.qN N * d * S.T * (∑ a, B a) ^ 2 := by
        rw [integral_const]; simp [hK]; ring

end Triv

section Arith

/-- the real arithmetic of the smooth rate -/
theorem sa2_arith_smooth {Bs c0 Cy Ct dd T ε q σ E w Ccov : ℝ} (hBs : 0 ≤ Bs) (hc0 : 0 ≤ c0)
    (hCy : 0 ≤ Cy) (hCt : 0 ≤ Ct) (hdd : 0 ≤ dd) (hT : 0 ≤ T) (hε : 0 ≤ ε) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hσ : 0 ≤ σ) (hE : 0 ≤ E) (hw : 0 ≤ w)
    (hC1 : ε + Real.sqrt q * Real.sqrt w + σ * (E + 0) < 1 → Ccov ≤ 2 * q * Ct * Bs ^ 2 * T * w)
    (hC2 : 1 ≤ ε + Real.sqrt q * Real.sqrt w + σ * (E + 0) → Ccov ≤ 4 * q * dd * T * Bs ^ 2) :
    σ * c0 * Bs * (E * T) + ε * (Cy * Bs) + 1 / 2 * Ccov ≤
      (c0 * T + Cy + Ct * T + 2 * dd * T) * (Bs + Bs ^ 2) *
        (ε + Real.sqrt q * Real.sqrt w + σ * (E + 0)) := by
  set r : ℝ := ε + Real.sqrt q * Real.sqrt w + σ * (E + 0) with hr
  have hsq : 0 ≤ Real.sqrt q * Real.sqrt w := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hσE : 0 ≤ σ * (E + 0) := by positivity
  have hr0 : 0 ≤ r := by rw [hr]; linarith
  have hσEr : σ * E ≤ r := by rw [hr]; linarith
  have hεr : ε ≤ r := by rw [hr]; linarith
  have hB2 : 0 ≤ Bs ^ 2 := sq_nonneg _
  have h1 : σ * c0 * Bs * (E * T) ≤ c0 * T * Bs * r := by
    calc σ * c0 * Bs * (E * T) = (c0 * T * Bs) * (σ * E) := by ring
      _ ≤ (c0 * T * Bs) * r := mul_le_mul_of_nonneg_left hσEr (by positivity)
  have h2 : ε * (Cy * Bs) ≤ Cy * Bs * r := by
    calc ε * (Cy * Bs) = (Cy * Bs) * ε := by ring
      _ ≤ (Cy * Bs) * r := mul_le_mul_of_nonneg_left hεr (by positivity)
  by_cases hr1 : r < 1
  · have hqw : q * w ≤ r := by
      have hs2 : (Real.sqrt q * Real.sqrt w) ^ 2 = q * w := by
        rw [mul_pow, Real.sq_sqrt hq0, Real.sq_sqrt hw]
      have hsr : Real.sqrt q * Real.sqrt w ≤ r := by rw [hr]; linarith
      have hs1 : Real.sqrt q * Real.sqrt w < 1 := lt_of_le_of_lt hsr hr1
      calc q * w = (Real.sqrt q * Real.sqrt w) ^ 2 := hs2.symm
        _ ≤ Real.sqrt q * Real.sqrt w := by nlinarith
        _ ≤ r := hsr
    have h3 : 1 / 2 * Ccov ≤ Ct * T * Bs ^ 2 * r := by
      have := hC1 hr1
      calc 1 / 2 * Ccov ≤ 1 / 2 * (2 * q * Ct * Bs ^ 2 * T * w) := by linarith
        _ = (Ct * T * Bs ^ 2) * (q * w) := by ring
        _ ≤ (Ct * T * Bs ^ 2) * r := mul_le_mul_of_nonneg_left hqw (by positivity)
    have hK1 : c0 * T * Bs + Cy * Bs + Ct * T * Bs ^ 2 ≤
        (c0 * T + Cy + Ct * T + 2 * dd * T) * (Bs + Bs ^ 2) := by
      have : 0 ≤ dd * T * Bs := by positivity
      have : 0 ≤ dd * T * Bs ^ 2 := by positivity
      have : 0 ≤ c0 * T * Bs ^ 2 := by positivity
      have : 0 ≤ Cy * Bs ^ 2 := by positivity
      have : 0 ≤ Ct * T * Bs := by positivity
      nlinarith
    calc σ * c0 * Bs * (E * T) + ε * (Cy * Bs) + 1 / 2 * Ccov
        ≤ c0 * T * Bs * r + Cy * Bs * r + Ct * T * Bs ^ 2 * r := add_le_add (add_le_add h1 h2) h3
      _ = (c0 * T * Bs + Cy * Bs + Ct * T * Bs ^ 2) * r := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hK1 hr0
  · push Not at hr1
    have h3 : 1 / 2 * Ccov ≤ 2 * dd * T * Bs ^ 2 * r := by
      have := hC2 hr1
      calc 1 / 2 * Ccov ≤ 1 / 2 * (4 * q * dd * T * Bs ^ 2) := by linarith
        _ = (2 * dd * T * Bs ^ 2) * q := by ring
        _ ≤ (2 * dd * T * Bs ^ 2) * r :=
            mul_le_mul_of_nonneg_left (hq1.trans hr1) (by positivity)
    have hK1 : c0 * T * Bs + Cy * Bs + 2 * dd * T * Bs ^ 2 ≤
        (c0 * T + Cy + Ct * T + 2 * dd * T) * (Bs + Bs ^ 2) := by
      have : 0 ≤ Ct * T * Bs := by positivity
      have : 0 ≤ Ct * T * Bs ^ 2 := by positivity
      have : 0 ≤ c0 * T * Bs ^ 2 := by positivity
      have : 0 ≤ Cy * Bs ^ 2 := by positivity
      have : 0 ≤ dd * T * Bs := by positivity
      nlinarith
    calc σ * c0 * Bs * (E * T) + ε * (Cy * Bs) + 1 / 2 * Ccov
        ≤ c0 * T * Bs * r + Cy * Bs * r + 2 * dd * T * Bs ^ 2 * r := add_le_add (add_le_add h1 h2) h3
      _ = (c0 * T * Bs + Cy * Bs + 2 * dd * T * Bs ^ 2) * r := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hK1 hr0

end Arith

end HRS.MS.MainRdStat
