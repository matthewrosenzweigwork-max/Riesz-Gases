import HRS.MS.R26T8AO03b5

/-!
# S8.2 T8A O03b (part 6): linearity and smoothness of the corrected pair statistic `Q`, and the jet functionals
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82U HRS.MS.S82W HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_o03b_ps_add {N : ℕ} (F G : Euc d → Euc d → ℝ) (X : EucConfig d N) :
    pairStatistic (F + G) X = pairStatistic F X + pairStatistic G X := by
  unfold pairStatistic Phase2S82.pairSum
  simp only [Pi.add_apply, Finset.sum_add_distrib, mul_add]

theorem r26t8a_o03b_ps_smul {N : ℕ} (c : ℝ) (F : Euc d → Euc d → ℝ) (X : EucConfig d N) :
    pairStatistic (c • F) X = c * pairStatistic F X := by
  unfold pairStatistic Phase2S82.pairSum
  simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
  ring

theorem r26t8a_o03b_Q_add (N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N) (a beta M C : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (hM : 0 ≤ M) (hC : 0 ≤ C) (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ) (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    {A B : ℝ} {f g : Euc d → ℝ} (hf : TestBound (testOrder d) A f) (hg : TestBound (testOrder d) B g) :
    r26t8a_correctedQ (N := N) a beta Psi (f + g) =
      r26t8a_correctedQ (N := N) a beta Psi f + r26t8a_correctedQ (N := N) a beta Psi g := by
  have hk : 1 ≤ testOrder d := by unfold testOrder; omega
  have hA := r26t8a_o03b_tb_nonneg hk hf
  have hB := r26t8a_o03b_tb_nonneg hk hg
  have i1 := r26t8a_o03b_ps_int hd N hN a beta M ha hbeta hM hrho (mul_nonneg hC hA) (hPsi.corrector f A hA hf)
  have i2 := r26t8a_o03b_ps_int hd N hN a beta M ha hbeta hM hrho (mul_nonneg hC hB) (hPsi.corrector g B hB hg)
  funext X
  show pairStatistic (Psi (f + g)) X - ∫ Y, pairStatistic (Psi (f + g)) Y ∂(canonicalP d N a beta) =
    (pairStatistic (Psi f) X - ∫ Y, pairStatistic (Psi f) Y ∂(canonicalP d N a beta)) +
      (pairStatistic (Psi g) X - ∫ Y, pairStatistic (Psi g) Y ∂(canonicalP d N a beta))
  rw [r26t8a_o03b_psi_add hPsi hf hg]
  simp only [r26t8a_o03b_ps_add]
  rw [integral_add i1 i2]
  ring

theorem r26t8a_o03b_Q_smul (N : ℕ) (a beta M C : ℝ) (rho : Euc d → ℝ)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ) (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    {A : ℝ} {f : Euc d → ℝ} (hf : TestBound (testOrder d) A f) (c : ℝ) :
    r26t8a_correctedQ (N := N) a beta Psi (c • f) = c • r26t8a_correctedQ (N := N) a beta Psi f := by
  funext X
  show pairStatistic (Psi (c • f)) X - ∫ Y, pairStatistic (Psi (c • f)) Y ∂(canonicalP d N a beta) =
    c * (pairStatistic (Psi f) X - ∫ Y, pairStatistic (Psi f) Y ∂(canonicalP d N a beta))
  rw [r26t8a_o03b_psi_smul hPsi hf]
  simp only [r26t8a_o03b_ps_smul]
  rw [integral_const_mul]
  ring

theorem r26t8a_o03b_Q_contDiffAt (N : ℕ) (hd : 2 ≤ d) (a beta M C : ℝ) (hC : 0 ≤ C) (rho : Euc d → ℝ)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ) (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    {A : ℝ} {f : Euc d → ℝ} (hf : TestBound (testOrder d) A f) {X : EucConfig d N}
    (hX : X ∉ eucCollisionSet d N) :
    ContDiffAt ℝ 2 (r26t8a_correctedQ (N := N) a beta Psi f) X := by
  have hk : 1 ≤ testOrder d := by unfold testOrder; omega
  have hA := r26t8a_o03b_tb_nonneg hk hf
  have hjet := (w_pairstat_jets (N := N) hd (hPsi.corrector f A hA hf) (mul_nonneg hC hA)
    (∫ Y, pairStatistic (Psi f) Y ∂(canonicalP d N a beta))).1
  exact hjet.contDiffAt (r26t8a_o03b_coll_closed.isOpen_compl.mem_nhds hX)

theorem r26t8a_o03b_Q_lin (N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N) (a beta M C : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (hM : 0 ≤ M) (hC : 0 ≤ C) (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ) (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    {X : EucConfig d N} (hX : X ∉ eucCollisionSet d N) (ell : ℕ) (hell : ell ≤ 2) :
    r26t8a_o03b_Lin d (fun f : Euc d → ℝ => iteratedFDeriv ℝ ell (r26t8a_correctedQ (N := N) a beta Psi f) X) := by
  have hle : (ell : WithTop ℕ∞) ≤ 2 := by exact_mod_cast hell
  refine ⟨fun A B f g hf hg => ?_, fun A c f hf => ?_⟩
  · have c1 := (r26t8a_o03b_Q_contDiffAt N hd a beta M C hC rho Psi hPsi hf hX).of_le hle
    have c2 := (r26t8a_o03b_Q_contDiffAt N hd a beta M C hC rho Psi hPsi hg hX).of_le hle
    show iteratedFDeriv ℝ ell (r26t8a_correctedQ (N := N) a beta Psi (f + g)) X = _
    rw [r26t8a_o03b_Q_add N hd hN a beta M C ha hbeta hM hC rho hrho Psi hPsi hf hg,
      iteratedFDeriv_add_apply c1 c2]
  · have c1 := (r26t8a_o03b_Q_contDiffAt N hd a beta M C hC rho Psi hPsi hf hX).of_le hle
    show iteratedFDeriv ℝ ell (r26t8a_correctedQ (N := N) a beta Psi (c • f)) X = _
    rw [r26t8a_o03b_Q_smul N a beta M C rho Psi hPsi hf c, iteratedFDeriv_const_smul_apply c1]

end HRS.MS.R26T8A
