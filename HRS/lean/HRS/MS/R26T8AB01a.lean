import HRS.MS.R26T8AO06

/-!
# S8.2 T8A B01 (part a): the corrected pair statistic along the invariant path has `L²` norm `≤ C A N^{-1/2}`
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_b01_sq_of_eLp {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ} {y : ℝ} (hy : 0 ≤ y)
    (hf : AEStronglyMeasurable f μ) (h : eLpNorm f 2 μ ≤ ENNReal.ofReal y) : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ ≤ ENNReal.ofReal (y ^ 2) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num) (by norm_num) hf] at h
  simp only [ENNReal.toReal_ofNat] at h
  have h2 := ENNReal.rpow_le_rpow h (by norm_num : (0 : ℝ) ≤ 2)
  rw [← ENNReal.rpow_mul] at h2
  norm_num at h2
  calc ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ = ∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ := by simp [ENNReal.rpow_two]
    _ ≤ (ENNReal.ofReal y) ^ (2 : ℝ) := by simpa using h2
    _ = ENNReal.ofReal (y ^ 2) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hy (by norm_num), Real.rpow_two]

set_option maxHeartbeats 6400000 in
theorem r26t8a_b01_Qnorm (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N) (a beta M C : ℝ) (ha : 0 < a) (hbeta : 0 < beta)
    (hM : 0 ≤ M) (hC : 0 ≤ C) (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ) (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    {Omega : Type} [mOmega : MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (X0 : Omega → EucConfig d N) (W : ℝ≥0 → Omega → Fin N → Euc d) (X : ℝ≥0 → Omega → EucConfig d N)
    (hX : IsCanonicalRealization d (criticalS d) a beta N P X0 W X) (r : ℝ) (hr : 0 ≤ r)
    {A : ℝ} {f : Euc d → ℝ} (hf : TestBound (testOrder d) A f) :
    MemLp (fun w => r26t8a_correctedQ (N := N) a beta Psi f (X r.toNNReal w)) 2 P ∧
    ∫⁻ w, ‖r26t8a_correctedQ (N := N) a beta Psi f (X r.toNNReal w)‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal ((C * A) ^ 2 / (N : ℝ)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  haveI hPp : IsProbabilityMeasure (canonicalP d N a beta) := HRS.MS.S82U.u4_prob (N := N) hd ha hbeta
  have hk : 1 ≤ testOrder d := by unfold testOrder; omega
  have hA := r26t8a_o03b_tb_nonneg hk hf
  set t : ℝ≥0 := r.toNNReal with ht
  have hlaw : law P (X t) = canonicalP d N a beta :=
    hX.invariant P (t : ℝ) X0 W X hX.brownian hX.indep hX.init (hX.solution t) t le_rfl
  have hXm : Measurable (X t) := (hX.solution (t : ℝ)).adapted t
  have hQm : Measurable (r26t8a_correctedQ (N := N) a beta Psi f) := by
    have hQ := hPsi.corrector f A hA hf
    have key : ∀ i j : Fin N, Measurable (fun Y : EucConfig d N => Psi f (Y i) (Y j)) := fun i j => by
      have h2 : Measurable (fun Y : EucConfig d N => (Y i, Y j)) :=
        (measurable_pi_apply i).prodMk (measurable_pi_apply j)
      exact hQ.measurable.comp h2
    have hps : Measurable (pairStatistic (N := N) (Psi f)) := by
      unfold pairStatistic Phase2S82.pairSum
      exact measurable_const.mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => key i j)
    exact hps.sub measurable_const
  have hb := (hPsi.bound N hN f A hA hf).2
  have hE : eLpNorm (r26t8a_correctedQ (N := N) a beta Psi f) 2 (canonicalP d N a beta) ≤
      ENNReal.ofReal (C * A * (N : ℝ) ^ (-(1 / 2 : ℝ))) :=
    (le_self_add.trans le_self_add).trans hb
  have hcomp : eLpNorm (fun w => r26t8a_correctedQ (N := N) a beta Psi f (X t w)) 2 P =
      eLpNorm (r26t8a_correctedQ (N := N) a beta Psi f) 2 (canonicalP d N a beta) := by
    rw [← hlaw]
    exact (eLpNorm_map_measure hQm.aestronglyMeasurable hXm.aemeasurable).symm
  have hmem : MemLp (fun w => r26t8a_correctedQ (N := N) a beta Psi f (X t w)) 2 P :=
    memLp_iff.2 (by rw [hcomp]; exact lt_of_le_of_lt hE ENNReal.ofReal_lt_top)
  refine ⟨hmem, ?_⟩
  have hy0 : 0 ≤ C * A * (N : ℝ) ^ (-(1 / 2 : ℝ)) := mul_nonneg (mul_nonneg hC hA) (Real.rpow_nonneg hN0.le _)
  have := r26t8a_b01_sq_of_eLp hy0 (hQm.comp hXm).aestronglyMeasurable (hcomp ▸ hE : eLpNorm (fun w => r26t8a_correctedQ (N := N) a beta Psi f (X t w)) 2 P ≤ _)
  refine this.trans (le_of_eq ?_)
  congr 1
  have hNrt : ((N : ℝ) ^ (-(1 / 2 : ℝ))) ^ 2 = 1 / (N : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
    norm_num
    exact Real.rpow_neg_one _
  rw [mul_pow, hNrt]
  field_simp

end HRS.MS.R26T8A

end
