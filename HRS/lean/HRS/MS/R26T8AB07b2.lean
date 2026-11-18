import HRS.MS.R26T8AB07b1
import HRS.MS.R26T8AO03a

/-!
# S8.2 observed-time layer, packet T8A.B07b2: the source functional along a feature orbit

For the projected orbit `q v = projectedOrbit v φ_α` of a feature, the functions `Ψ v y = scalarForcing (q v) y` are
(i) dominated by `B * env y` uniformly for `v ∈ [0,V]` off collisions, (ii) continuous in `v ∈ [0,∞)` at every
collision-free `y` (additivity B07b1 plus continuity of the orbit in the positive-jet norm), (iii) measurable in `y`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_b07b2_meas (d N : ℕ) (a beta : ℝ) (rho : Euc d → ℝ) (f : Euc d → ℝ)
    [SFinite (HRS.Whole.withDensityReal rho)] :
    Measurable (fun y : EucConfig d N => scalarForcing a beta rho f y) := by
  have hDm := HRS.MS.Wr.wr14a_measurable_D (N := N) (r26t8a_b07b1_hmeas f)
    (HRS.Whole.withDensityReal rho)
  unfold scalarForcing centerUnder
  exact measurable_const.mul (hDm.sub measurable_const)

theorem r26t8a_b07b2_orbit (d N : ℕ) (hd : 2 ≤ d) (hN : 2 ≤ N) (a beta m Cf c : ℝ) (ha : 0 < a)
    (hbeta : 0 < beta) (rho : Euc d → ℝ) (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    (horb : r26t8a_FeatureOrbits d a beta m Cf c rho) (alpha : MultiIndex d) :
    (∀ V : ℝ, 0 ≤ V → ∃ B : ℝ, 0 ≤ B ∧ ∀ v ∈ Set.Icc (0 : ℝ) V, ∀ y ∉ eucCollisionSet d N,
      |scalarForcing a beta rho (r26t8a_projectedOrbit (critCoeff d a beta rho)
        (HRS.Whole.withDensityReal rho) v (oscTestFun m alpha)) y| ≤
        B * r26t8a_configPoleEnvelope (d := d) (N := N) (criticalS d) y) ∧
    (∀ y ∉ eucCollisionSet d N, ∀ v0 : ℝ, 0 ≤ v0 →
      ContinuousWithinAt (fun v => scalarForcing a beta rho (r26t8a_projectedOrbit (critCoeff d a beta rho)
        (HRS.Whole.withDensityReal rho) v (oscTestFun m alpha)) y) (Set.Ici 0) v0) := by
  classical
  obtain ⟨C0, hC0, hCb⟩ := r26t8a_b07a1_int_bound' d hd a beta ha hbeta
  obtain ⟨c0, K, hc0, hK, hm, henv1, hL2, hE⟩ := r26t8a_b07a_explicit d N hd hN a beta ha hbeta rho hrho
  set q : ℝ → Euc d → ℝ := fun v => r26t8a_projectedOrbit (critCoeff d a beta rho)
    (HRS.Whole.withDensityReal rho) v (oscTestFun m alpha) with hq
  set w : ℝ := HRS.MS.S82BD.s82Weight d m alpha with hw
  have hTB : ∀ v : ℝ, 0 ≤ v → TestBound (testOrder d) (Cf * w * Real.exp (-c * v)) (q v) :=
    fun v hv => horb.bound alpha v hv 0 (by norm_num)
  have hAnn : ∀ v : ℝ, 0 ≤ v → 0 ≤ Cf * w * Real.exp (-c * v) := fun v hv => by
    have h := (hTB v hv).2 1 le_rfl (by unfold testOrder; omega) 0
    exact (norm_nonneg _).trans h
  have hCw : 0 ≤ Cf * w := by
    have := hAnn 0 le_rfl
    simpa using this
  refine ⟨fun V hV => ⟨K * (Cf * w * Real.exp (|c| * V)), mul_nonneg hK
    (mul_nonneg hCw (Real.exp_pos _).le), fun v hv y hy => ?_⟩, fun y hy v0 hv0 => ?_⟩
  · have h1 := (hE (q v) _ (hAnn v hv.1) (hTB v hv.1)).2 y hy
    have h2 : Cf * w * Real.exp (-c * v) ≤ Cf * w * Real.exp (|c| * V) := by
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hCw
      have h3 : -c * v ≤ |c| * v := by nlinarith [neg_abs_le c, abs_nonneg c, hv.1]
      have h4 : |c| * v ≤ |c| * V := mul_le_mul_of_nonneg_left hv.2 (abs_nonneg c)
      linarith
    have h0 : 0 ≤ r26t8a_configPoleEnvelope (d := d) (N := N) (criticalS d) y := by
      linarith [henv1 y]
    calc _ ≤ _ := h1
      _ ≤ (Cf * w * Real.exp (|c| * V)) * (K * r26t8a_configPoleEnvelope (d := d) (N := N) (criticalS d) y) := by
          gcongr
      _ = _ := by ring
  · set e := r26t8a_configPoleEnvelope (d := d) (N := N) (criticalS d) y with he
    have he0 : 0 ≤ e := by linarith [henv1 y]
    have hcont := horb.continuity alpha 0 (by norm_num) v0 hv0
    unfold ContinuousWithinAt
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hη : 0 < ε / (K * e + 1) := by positivity
    have hev := (ENNReal.tendsto_nhds_zero.1 hcont) (ENNReal.ofReal (ε / (K * e + 1)))
      (ENNReal.ofReal_pos.2 hη)
    filter_upwards [hev, self_mem_nhdsWithin] with v hv hv0'
    have hv0'' : 0 ≤ v := hv0'
    have hdiff : TestBound (testOrder d) (ε / (K * e + 1)) (fun x => q v x - q v0 x) := by
      refine ⟨(hTB v hv0'').1.sub (hTB v0 hv0).1, fun j hj1 hjk x => ?_⟩
      have := r26t8a_o03a_le_testSize (k := testOrder d) (fun x => q v x - q v0 x) _ hη.le hv j hj1 hjk x
      exact this
    have hsub := r26t8a_b07b1_sub d N hd hN a beta ha hbeta rho hrho (q v) (q v0) _ _
      (hAnn v hv0'') (hAnn v0 hv0) (hTB v hv0'') (hTB v0 hv0) y
    have hb := (hE _ _ hη.le hdiff).2 y hy
    rw [Real.dist_eq, ← hsub]
    calc |scalarForcing a beta rho (fun x => q v x - q v0 x) y| ≤ _ := hb
      _ < ε := by
        have : ε / (K * e + 1) * (K * e) < ε := by
          have hKe : 0 ≤ K * e := mul_nonneg hK he0
          calc ε / (K * e + 1) * (K * e) < ε / (K * e + 1) * (K * e + 1) := by
                gcongr; linarith
            _ = ε := by field_simp
        exact this

end HRS.MS.R26T8A
