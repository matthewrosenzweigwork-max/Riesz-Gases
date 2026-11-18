import HRS.MS.R26T8AB09d
import HRS.MS.R26T8AF14

/-!
# S8.2 T8A B09: `r26t8a_scalar_blocks` from O01

`r26t8a_O01_stmt` is exactly the statement of packet O01 (`r26t8a_normal_form_family`, the unconditional common linear
`NormalFormFamily`), the only input of B09 not yet proved.  `r26t8a_scalar_blocks_of_O01 hO01 : S82ScalarBlocks`; once O01 is
proved, `r26t8a_scalar_blocks := r26t8a_scalar_blocks_of_O01 r26t8a_normal_form_family`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.PDE.ToolboxRd

/-- The statement of packet O01 `r26t8a_normal_form_family`. -/
def r26t8a_O01_stmt : Prop :=
  ∀ (d : ℕ) (_ : 2 ≤ d) (a beta : ℝ) (_ : 0 < a) (_ : 0 < beta),
    ∃ C M : ℝ, 0 ≤ C ∧ 0 ≤ M ∧ ∀ rho : Euc d → ℝ,
      IsThermalEquilibrium d (criticalS d) a beta rho →
      ∃ Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ,
        r26t8a_NormalFormFamily d a beta M C rho Psi

set_option maxHeartbeats 12800000 in
theorem r26t8a_scalar_blocks_of_O01 (hO01 : r26t8a_O01_stmt) : HRS.MS.S82BD.S82ScalarBlocks := by
  intro d hd a beta ha hbeta m hm T hT
  obtain ⟨Cf, c, hCf, hc, horb⟩ := r26t8a_high_order_feature_orbits d hd a beta m ha hbeta hm
  obtain ⟨C, M, hC, hM, hpsi⟩ := hO01 d hd a beta ha hbeta
  have hs1 := Classical.choose_spec (r26t8a_old_endpoint d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT)
  have hs2 := Classical.choose_spec (r26t8a_old_drift d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT)
  have hs3 := Classical.choose_spec (r26t8a_old_noise d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT)
  have hs4 := Classical.choose_spec (r26t8a_recent_endpoint d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT)
  have hs5 := Classical.choose_spec (r26t8a_recent_drift d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT)
  have hs6 := Classical.choose_spec (r26t8a_recent_noise d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT)
  set B1 := r26t8a_b09_B1 d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT with hB1
  set B2 := r26t8a_b09_B2 d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT with hB2
  set B3 := r26t8a_b09_B3 d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT with hB3
  set B4 := r26t8a_b09_B4 d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT with hB4
  set B5 := r26t8a_b09_B5 d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT with hB5
  set B6 := r26t8a_b09_B6 d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT with hB6
  have hB1n : 0 ≤ B1 := hs1.1
  have hB2n : 0 ≤ B2 := hs2.1
  have hB3n : 0 ≤ B3 := hs3.1
  have hB4n : 0 ≤ B4 := hs4.1
  have hB5n : 0 ≤ B5 := hs5.1
  have hB6n : 0 ≤ B6 := hs6.1
  refine ⟨max (B4 + B5 + B6) (2 * B1 + B2 + B3), Real.exp (-c), ?_, Real.exp_pos _, ?_, ?_⟩
  · exact le_max_of_le_left (by positivity)
  · rw [← Real.exp_zero]; exact Real.exp_lt_exp.2 (by linarith)
  intro rho hrho N hN Omega mOmega P hP X0 W X hX a0 ha0 alpha
  obtain ⟨Psi, hPsi⟩ := hpsi rho hrho
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hW0 : 0 ≤ HRS.MS.S82BD.s82Weight d m alpha := by
    unfold HRS.MS.S82BD.s82Weight oscEigenvalue
    exact Real.rpow_nonneg (by positivity) _
  have hNr : 0 ≤ (N : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hN0.le _
  obtain ⟨hrm, hrb⟩ := r26t8a_b09_recent d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT rho hrho Psi hPsi (horb rho hrho) N hN P
    X0 W X hX a0 ha0 alpha
  refine ⟨hrm, ?_, fun j => ?_⟩
  · refine hrb.trans (ENNReal.ofReal_le_ofReal ?_)
    have : (B4 + B5 + B6) ≤ max (B4 + B5 + B6) (2 * B1 + B2 + B3) := le_max_left _ _
    gcongr
  · obtain ⟨hpm, hpb⟩ := r26t8a_b09_past d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT rho hrho Psi hPsi (horb rho hrho) N hN P
      X0 W X hX a0 ha0 alpha j
    refine ⟨hpm, hpb.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    have hq : Real.exp (-c) ^ j = Real.exp (-c * (j : ℝ)) := by
      rw [← Real.exp_nat_mul]; congr 1; ring
    rw [hq]
    have : (2 * B1 + B2 + B3) ≤ max (B4 + B5 + B6) (2 * B1 + B2 + B3) := le_max_right _ _
    have hE : 0 ≤ Real.exp (-c * (j : ℝ)) := (Real.exp_pos _).le
    gcongr

end HRS.MS.R26T8A

end
