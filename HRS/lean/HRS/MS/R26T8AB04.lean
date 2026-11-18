import HRS.MS.R26T8AB04c

/-!
# S8.2 T8A B04: `r26t8a_recent_endpoint` (Pro contract, verbatim)

`Y t = -QAge 0 0 (X (a0+t)) + QAge 0 t (X a0)`: the moving endpoint by the reversible graph maximal bound (B04b), the fixed
endpoint by B01 at `j = 0`, `r = a0`; Minkowski for suprema (B04a), measurability by path continuity (B04c).
`B = 10 √(1+T/β) C Cf + B01`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.PDE.ToolboxRd

set_option maxHeartbeats 12800000 in
theorem r26t8a_recent_endpoint (d : ℕ) (hd : 2≤d) (a beta m M C Cf c : ℝ)
    (ha : 0<a) (hbeta : 0<beta) (hM : 0≤M) (hC : 0≤C) (hCf : 0≤Cf) (hc : 0<c)
    (T : ℝ) (hT : 0<T) :
    ∃ B : ℝ, 0≤B ∧ ∀ rho : Euc d → ℝ, IsThermalEquilibrium d (criticalS d) a beta rho →
      ∀ Psi : (Euc d → ℝ) → Euc d → Euc d → ℝ,
      r26t8a_NormalFormFamily d a beta M C rho Psi →
      r26t8a_FeatureOrbits d a beta m Cf c rho →
      ∀ N : ℕ, 2≤N → ∀ {Omega : Type} [mOmega : MeasurableSpace Omega],
      ∀ P : Measure Omega, ∀ [IsProbabilityMeasure P],
      ∀ X0 : Omega → EucConfig d N, ∀ W : ℝ≥0 → Omega → Fin N → Euc d,
      ∀ X : ℝ≥0 → Omega → EucConfig d N,
      IsCanonicalRealization d (criticalS d) a beta N P X0 W X →
      ∀ a0 : ℝ, 0≤a0 → ∀ alpha : MultiIndex d,
      r26t8a_ReversibleWindows P X →
      let Y := fun t w => -r26t8a_QAge a beta m rho Psi alpha 0 0 (X (a0+t).toNNReal w)+r26t8a_QAge a beta m rho Psi alpha 0 t (X a0.toNNReal w)
      AEMeasurable (fun w => ⨆ t : Set.Icc (0:ℝ) T, ‖Y t w‖ₑ) P ∧
        (r26t8a_scalarSupSq P T Y)^(1/2:ℝ) ≤ ENNReal.ofReal (B*HRS.MS.S82BD.s82Weight d m alpha*(N:ℝ)^(-(1/2:ℝ))) := by
  classical
  obtain ⟨B1, hB1, hend⟩ := r26t8a_old_endpoint d hd a beta m M C Cf c ha hbeta hM hC hCf hc T hT
  refine ⟨10 * Real.sqrt (1 + T / beta) * C * Cf + B1, by positivity, ?_⟩
  intro rho hrho Psi hPsi horb N hN Omega mOmega P hP X0 W X hX a0 ha0 alpha hrev
  intro Y
  obtain ⟨hmov_m, hmov⟩ := r26t8a_b04_moving d N hd hN a beta m M C Cf c ha hbeta hM hC hCf rho hrho Psi hPsi horb
    alpha P X0 W X hX hrev a0 T ha0 hT
  obtain ⟨hfix_m, hfix⟩ := hend rho hrho Psi hPsi horb N hN P X0 W X hX a0 ha0 alpha 0 a0 ha0 (by simp)
  simp only [add_sub_cancel_left] at hfix_m hfix
  obtain ⟨hsl, hco⟩ := r26t8a_b04_cont d N hd hN a beta m M C Cf c ha hbeta hM hC rho hrho Psi hPsi horb alpha P X0 W X
    hX a0 T ha0 hT
  refine ⟨r26t8a_b04_sup_meas P T Y hsl hco, ?_⟩
  have hY : Y = fun t w => (fun t w => r26t8a_QAge a beta m rho Psi alpha 0 t (X a0.toNNReal w)) t w -
      (fun t w => r26t8a_QAge a beta m rho Psi alpha 0 0 (X (a0 + t).toNNReal w)) t w := by
    funext t w; simp only [Y]; ring
  rw [hY]
  refine (r26t8a_b04_sup_sub P T _ _ hmov_m hfix_m).trans ?_
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hW0 : 0 ≤ HRS.MS.S82BD.s82Weight d m alpha := by
    unfold HRS.MS.S82BD.s82Weight oscEigenvalue
    exact Real.rpow_nonneg (by positivity) _
  refine (add_le_add hmov hfix).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
  simp only [Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
  ring

end HRS.MS.R26T8A

end
