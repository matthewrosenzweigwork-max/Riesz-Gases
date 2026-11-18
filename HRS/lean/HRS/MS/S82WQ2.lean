import HRS.MS.S82WQ1
import HRS.MS.S82WA04
import HRS.MS.S82QDom

/-!
# S8.2 A05 (S82W), part 6: one-particle marginal domination of `canonicalP` and the `L²` bound of the linear correction
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82W
open HRS HRS.Whole HRS.MS.Phase2S82

section marg
variable {d : ℕ}

/-- every one-particle marginal of `canonicalP` is dominated by `μ` (weak reference setup + pin-free reference marginal). -/
theorem w_marg_dom {a beta C0 : ℝ} {rho : Euc d → ℝ} {q : Euc d → ℝ} {h : ℕ → Euc d → ℝ}
    [IsProbabilityMeasure (HRS.Whole.withDensityReal rho)]
    (hW : WeakReferenceSetup d a beta rho q h C0) (hbeta : 0 < beta) {N : ℕ} (hN : 2 ≤ N) (i : Fin N) :
    (canonicalP d N a beta).map (fun X => X i) ≤
      ENNReal.ofReal C0 • (ENNReal.ofReal C0 • HRS.Whole.withDensityReal rho) := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 1 := ⟨N - 1, by omega⟩
  have hdom := hW.domination (m + 1) hN
  have hU := HRS.MS.S82Q.s82q_marg_le_nu hW hbeta hN (p := 0) (m := m) (by norm_num) (by omega)
    (fun j : Fin 0 => j.elim0) i
  have hnu := HRS.MS.S82Q.s82q_nu_le q hW.short.nonneg (HRS.Whole.withDensityReal rho) beta hbeta
    (m + 1) (fun j : Fin 0 => j.elim0)
  refine Measure.le_iff.2 fun s hs => ?_
  have hS : MeasurableSet ((fun X : EucConfig d (m + 1) => X i) ⁻¹' s) := measurable_pi_apply i hs
  rw [Measure.map_apply (measurable_pi_apply i) hs, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
  refine (hdom _).trans ?_
  rw [Measure.smul_apply, smul_eq_mul]
  refine mul_le_mul' le_rfl ?_
  have := hU s
  rw [Measure.map_apply (measurable_pi_apply i) hs] at this
  refine this.trans ?_
  rw [Measure.smul_apply, smul_eq_mul]
  exact mul_le_mul' le_rfl (hnu s)

lemma w_center_L2 {α : Type*} [MeasurableSpace α] {P : Measure α} [IsProbabilityMeasure P] {G : α → ℝ}
    (hG : AEStronglyMeasurable G P) : eLpNorm (centerUnder P G) 2 P ≤ eLpNorm G 2 P := by
  have hc : AEStronglyMeasurable (centerUnder P G) P := hG.sub aestronglyMeasurable_const
  rw [w_eLp_two hc, w_eLp_two hG]
  refine ENNReal.rpow_le_rpow ?_ (by norm_num)
  have h1 : ∫⁻ x, ‖centerUnder P G x‖ₑ ^ (2 : ℝ) ∂P = evariance G P := by
    unfold evariance centerUnder
    simp_rw [ENNReal.rpow_two]
  have h2 : ∫⁻ x, ‖G x‖ₑ ^ (2 : ℝ) ∂P = ∫⁻ x, ‖G x‖ₑ ^ 2 ∂P := by simp_rw [ENNReal.rpow_two]
  rw [h1, h2, evariance_def' hG]
  exact tsub_le_self

theorem w_zeta_L2 {a beta K : ℝ} {μ : Measure (Euc d)} {N : ℕ} (hN : 0 < N) (hK : 0 ≤ K)
    [IsProbabilityMeasure (canonicalP d N a beta)]
    (hdom : ∀ i : Fin N, (canonicalP d N a beta).map (fun X => X i) ≤ ENNReal.ofReal K • μ)
    {g : Euc d → ℝ} (hg : MemLp g 2 μ) :
    eLpNorm (fun X : EucConfig d N => (1 / (N : ℝ)) * ∑ i, g (X i)) 2 (canonicalP d N a beta) ≤
      ENNReal.ofReal (Real.sqrt K) * eLpNorm g 2 μ := by
  set P := canonicalP d N a beta
  have hgi : ∀ i : Fin N, eLpNorm (fun X : EucConfig d N => g (X i)) 2 P ≤
      ENNReal.ofReal (Real.sqrt K) * eLpNorm g 2 μ := by
    intro i
    have hac : P.map (fun X => X i) ≪ μ := by
      refine Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_
      have := hdom i s
      rw [Measure.smul_apply, h0, smul_zero] at this
      exact le_antisymm this bot_le
    have hm : AEStronglyMeasurable g (P.map (fun X => X i)) := hg.aestronglyMeasurable.mono_ac hac
    have e := eLpNorm_map_measure (p := 2) hm (measurable_pi_apply i).aemeasurable
    have e' : eLpNorm (fun X : EucConfig d N => g (X i)) 2 P = eLpNorm g 2 (P.map (fun X => X i)) := e.symm
    rw [e']
    refine (eLpNorm_mono_measure g (hdom i)).trans ?_
    rw [eLpNorm_smul_measure_of_ne_top (by simp)]
    simp only [ENNReal.toReal_ofNat, smul_eq_mul]
    rw [ENNReal.ofReal_rpow_of_nonneg hK (by norm_num), Real.sqrt_eq_rpow]
    norm_num
    exact hg.aestronglyMeasurable
  have hsum : eLpNorm (∑ i : Fin N, fun X : EucConfig d N => g (X i)) 2 P ≤
      ∑ i : Fin N, eLpNorm (fun X : EucConfig d N => g (X i)) 2 P :=
    eLpNorm_sum_le (by norm_num)
  have e : (fun X : EucConfig d N => (1 / (N : ℝ)) * ∑ i, g (X i)) =
      (1 / (N : ℝ)) • ∑ i : Fin N, fun X : EucConfig d N => g (X i) := by
    funext X; simp [Finset.sum_apply]
  rw [e, eLpNorm_const_smul]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hB : ∑ i : Fin N, eLpNorm (fun X : EucConfig d N => g (X i)) 2 P ≤
      ∑ _i : Fin N, ENNReal.ofReal (Real.sqrt K) * eLpNorm g 2 μ := Finset.sum_le_sum fun i _ => hgi i
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hB
  calc ‖(1 / (N : ℝ))‖ₑ * eLpNorm (∑ i : Fin N, fun X : EucConfig d N => g (X i)) 2 P
      ≤ ‖(1 / (N : ℝ))‖ₑ * ((N : ℝ≥0∞) * (ENNReal.ofReal (Real.sqrt K) * eLpNorm g 2 μ)) :=
        mul_le_mul' le_rfl (hsum.trans hB)
    _ = ENNReal.ofReal (Real.sqrt K) * eLpNorm g 2 μ := by
        rw [← mul_assoc]
        have : ‖(1 / (N : ℝ))‖ₑ * (N : ℝ≥0∞) = 1 := by
          rw [Real.enorm_eq_ofReal (by positivity), ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity)]
          rw [one_div, inv_mul_cancel₀ hN0.ne']; simp
        rw [this, one_mul]

end marg

end HRS.MS.S82W
