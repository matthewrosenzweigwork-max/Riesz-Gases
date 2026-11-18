import HRS.MS.R26T8AB04a
import HRS.MS.S82P2Var1

/-!
# S8.2 T8A B04b: the moving endpoint `t ↦ QAge 0 0 (X (a0+t))` (reversible graph maximal bound)

Apply V13 to `F = correctedQ(ageTest 0 0)`: `∫F = 0`, so the centered process is the process itself; the energies are controlled by
`NormalFormFamily.bound`.  Constant `10 √(1+T/β) C Cf`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.PDE.ToolboxRd

theorem r26t8a_b04_center_int {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsProbabilityMeasure μ]
    (g : E → ℝ) : ∫ x, centerUnder μ g x ∂μ = 0 := by
  by_cases h : Integrable g μ
  · unfold centerUnder
    rw [integral_sub h (integrable_const _)]
    simp
  · have h0 : ∫ y, g y ∂μ = 0 := integral_undef h
    simp only [centerUnder, h0, sub_zero]

theorem r26t8a_b04_Qmeas (d N : ℕ) (a beta M C : ℝ) (hk : 1 ≤ testOrder d) (rho : Euc d → ℝ)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ) (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    {B : ℝ} {f : Euc d → ℝ} (hf : TestBound (testOrder d) B f) :
    Measurable (r26t8a_correctedQ (N := N) a beta Psi f) := by
  have hB := r26t8a_o03b_tb_nonneg hk hf
  have hQ := hPsi.corrector f B hB hf
  have key : ∀ i j : Fin N, Measurable (fun Y : EucConfig d N => Psi f (Y i) (Y j)) := fun i j => by
    have h2 : Measurable (fun Y : EucConfig d N => (Y i, Y j)) :=
      (measurable_pi_apply i).prodMk (measurable_pi_apply j)
    exact hQ.measurable.comp h2
  have hps : Measurable (pairStatistic (N := N) (Psi f)) := by
    unfold pairStatistic Phase2S82.pairSum
    exact measurable_const.mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => key i j)
  exact hps.sub measurable_const

set_option maxHeartbeats 12800000 in
theorem r26t8a_b04_moving (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N) (a beta m M C Cf c : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) (hC : 0 ≤ C) (hCf : 0 ≤ Cf)
    (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ)
    (hPsi : r26t8a_NormalFormFamily d a beta M C rho Psi)
    (horb : r26t8a_FeatureOrbits d a beta m Cf c rho) (alpha : MultiIndex d)
    {Omega : Type} [mOmega : MeasurableSpace Omega] (P : Measure Omega) [IsProbabilityMeasure P]
    (X0 : Omega → EucConfig d N) (W : ℝ≥0 → Omega → Fin N → Euc d) (X : ℝ≥0 → Omega → EucConfig d N)
    (hX : IsCanonicalRealization d (criticalS d) a beta N P X0 W X) (hrev : r26t8a_ReversibleWindows P X)
    (a0 T : ℝ) (ha0 : 0 ≤ a0) (hT : 0 < T) :
    let Y1 := fun t w => r26t8a_QAge a beta m rho Psi alpha 0 0 (X (a0 + t).toNNReal w)
    AEMeasurable (fun w => ⨆ t : Set.Icc (0 : ℝ) T, ‖Y1 t w‖ₑ) P ∧
      (r26t8a_scalarSupSq P T Y1) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal
        (10 * Real.sqrt (1 + T / beta) * (C * Cf * HRS.MS.S82BD.s82Weight d m alpha * (N : ℝ) ^ (-(1 / 2 : ℝ)))) := by
  intro Y1
  classical
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hP0 : IsProbabilityMeasure (canonicalP d N a beta) := HRS.MS.S82U.u4_prob (N := N) hd ha hbeta
  have hW0 : 0 ≤ HRS.MS.S82BD.s82Weight d m alpha := by
    unfold HRS.MS.S82BD.s82Weight oscEigenvalue
    exact Real.rpow_nonneg (by positivity) _
  set w0 := HRS.MS.S82BD.s82Weight d m alpha with hw0
  set A : ℝ := Cf * w0 with hA
  have hA0 : 0 ≤ A := by positivity
  set f : Euc d → ℝ := r26t8a_ageTest a beta m rho alpha 0 0 with hf
  have hTB : TestBound (testOrder d) A f := by
    have := horb.bound alpha 0 le_rfl 0 (by norm_num)
    refine r26t8a_o03b_tb_mono this ?_
    simp [hA, hw0]
  set F : EucConfig d N → ℝ := r26t8a_correctedQ (N := N) a beta Psi f with hF
  have hF2 : ContDiffOn ℝ 2 F (eucCollisionSet d N)ᶜ :=
    r26t8a_o03b_Q_contDiffOn N hd a beta M C hC rho Psi hPsi hTB
  have hdom := hPsi.domain N hN f A hA0 hTB
  obtain ⟨hmeas, hbd⟩ := r26t8a_reversible_corrector_maximal d N hd hN a beta ha hbeta P X0 W X hX hrev F _ hF2 hdom
    a0 T ha0 hT
  have hFc : centerUnder (canonicalP d N a beta) F = F := by
    funext x
    have : ∫ y, F y ∂canonicalP d N a beta = 0 := r26t8a_b04_center_int _ _
    simp only [centerUnder, this, sub_zero]
  have hY : Y1 = fun t w => centerUnder (canonicalP d N a beta) F (X (a0 + t).toNNReal w) := by
    funext t w; rw [hFc]; rfl
  rw [hY]
  refine ⟨hmeas, ?_⟩
  -- energies
  obtain ⟨hDm, hb⟩ := hPsi.bound N hN f A hA0 hTB
  set Eb : ℝ := C * A * (N : ℝ) ^ (-(1 / 2 : ℝ)) with hEb
  have hEb0 : 0 ≤ Eb := by positivity
  have hQ : eLpNorm F 2 (canonicalP d N a beta) ≤ ENNReal.ofReal Eb :=
    (le_self_add.trans le_self_add).trans hb
  have hG : (∫⁻ X, ∑ i, ‖Phase2S82.configGrad F X i‖ₑ ^ 2 ∂canonicalP d N a beta) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal Eb := by
    exact (le_add_self.trans le_self_add).trans hb
  have hk : 1 ≤ testOrder d := by unfold testOrder; omega
  have hFm : Measurable F := r26t8a_b04_Qmeas d N a beta M C hk rho Psi hPsi hTB
  have hFint0 : ∫ y, F y ∂canonicalP d N a beta = 0 := r26t8a_b04_center_int _ _
  have hvar : evariance F (canonicalP d N a beta) ≤ ENNReal.ofReal Eb ^ 2 := by
    have : evariance F (canonicalP d N a beta) = ∫⁻ x, ‖F x‖ₑ ^ 2 ∂canonicalP d N a beta := by
      unfold evariance; simp [hFint0]
    rw [this, lintegral_enorm_sq_eq_eLpNorm_sq hFm.aestronglyMeasurable]
    exact pow_le_pow_left' hQ 2
  have hgr : ∫⁻ X, ∑ i, ‖Phase2S82.configGrad F X i‖ₑ ^ 2 ∂canonicalP d N a beta ≤ ENNReal.ofReal Eb ^ 2 := by
    have h1 := pow_le_pow_left' hG 2
    refine le_trans (le_of_eq ?_) h1
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hsq : r26t8a_scalarSupSq P T (fun t w => centerUnder (canonicalP d N a beta) F (X (a0 + t).toNNReal w)) ≤
      ENNReal.ofReal (100 * (Eb ^ 2 + T / beta * Eb ^ 2)) := by
    refine hbd.trans ?_
    have hT0 : 0 ≤ T / beta := by positivity
    rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul hT0, ENNReal.ofReal_pow hEb0]
    have : (ENNReal.ofReal 100) = 100 := by simp
    rw [this]
    gcongr
  have hz : 100 * (Eb ^ 2 + T / beta * Eb ^ 2) = (10 * Real.sqrt (1 + T / beta) * Eb) ^ 2 := by
    have h2 : Real.sqrt (1 + T / beta) ^ 2 = 1 + T / beta := Real.sq_sqrt (by positivity)
    have : (10 * Real.sqrt (1 + T / beta) * Eb) ^ 2 = 100 * Real.sqrt (1 + T / beta) ^ 2 * Eb ^ 2 := by ring
    rw [this, h2]; ring
  refine (ENNReal.rpow_le_rpow hsq (by norm_num)).trans (le_of_eq ?_)
  rw [hz, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num), ← Real.sqrt_eq_rpow,
    Real.sqrt_sq (by positivity)]
  congr 1
  rw [hEb, hA]; ring

end HRS.MS.R26T8A

end
