import HRS.MS.Fp81S21EmbedIdent
import HRS.MS.R2InterpAux12

/-! Weighted action of an empirical fluctuation representative. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.R2Interp

/-- At each fixed nonnegative time, a strong empirical representative acts
on every weighted test on a single full-measure event. -/
theorem fp81s21_emp_MomentRep_weighted_action
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) (N : ℕ) (hN : 2 ≤ N)
    (A : Particle R N)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    {qsη : ℝ → A.Ω → r26t6_Coeff} {M2 : ℝ}
    (hrep : fp81s21_MomentRep Es A.P (fp81s21_particleEmpField R N A) qsη M2)
    (hmom : ∀ u, 0 ≤ u → Integrable
      (fun x : Euc p.d => jbracket x ^ ((p.d : ℝ) + 4)) (r26t3_mu R u)) :
    ∀ u, 0 ≤ u → ∀ᵐ ω ∂A.P, ∀ f,
      IsR2WeightedTest (2 * p.d + 6) ((p.d : ℝ) + 4) f →
        fp81s21_chartAction Es (qsη u ω) f = fp81s21_particleEmpField R N A u ω f := by
  have hd : 1 ≤ p.d := le_trans (by decide : 1 ≤ 2) p.hd
  have hp : 0 ≤ (p.d : ℝ) + 4 := by positivity
  have hr : (p.d : ℝ) / 2 < (2 * p.d + 6 : ℕ) := by push_cast; nlinarith
  have hc : (p.d : ℝ) < 2 * ((p.d : ℝ) + 4) := by nlinarith
  intro u hu
  obtain ⟨_, _, hfield⟩ := hrep.2 u hu
  filter_upwards [hfield] with ω hω
  have hZ : S102Z (2 * p.d + 6) ((p.d : ℝ) + 4)
      (fp81s21_particleEmpField R N A u ω) := by
    change S102Z (2 * p.d + 6) ((p.d : ℝ) + 4)
      (fun f => Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical (A.X u.toNNReal ω)) f -
        HRS.Whole.pair (r26t3_mu R u) f))
    exact s102_Z_fluct hd hp (2 * p.d + 6) hr
        (lt_of_lt_of_le (by decide : 0 < 2) hN)
        (A.X u.toNNReal ω) (r26t3_mu R u) (hmom u hu) (Real.sqrt N)
  intro f hf
  exact fp81s21_chartAction_eq_of_compact_agreement hc Es (qsη u ω)
    (fp81s21_particleEmpField R N A u ω) hZ hω.1 f hf

#print axioms HRS.Fp81.S21.fp81s21_emp_MomentRep_weighted_action

end HRS.Fp81.S21
end
