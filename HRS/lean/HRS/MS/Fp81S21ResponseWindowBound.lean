import HRS.MS.Fp81S21ResponseWindow3
import HRS.MS.Fp81S21InitialKappa

/-!
# S2.1(iii): public quantitative uniform bound for the response window

The response-window sup norm is bounded by a constant chosen after the
trajectory and before the shift `b` and the point `x`.  The constant is
the square root of the summable envelope of the response mode bound, so it
does not depend on `b` or `x`.  The cubic integral bound follows under the
time-zero probability law, and the initial cubic tensor norm is bounded by
the same constant.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3

/-- The response window has a uniform sup-norm bound: the constant `K` is
chosen after the radius, the trajectory, and the positivity of `γ`, and
before the shift `b` and the point `x`. -/
theorem fp81s21_responseWindow_uniform_bound (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ, 0 < p.γ →
        ∃ K : ℝ, 0 ≤ K ∧ ∀ b : ℝ, 0 ≤ b → ∀ x : Euc p.d,
          ‖responseWindow R b x‖ ≤ K := by
  classical
  obtain ⟨δcommon, Co, co, hcommon0, hcommonHalf, -, hcommon⟩ :=
    fp81s21_common_radius p
  obtain ⟨δpath, hpath0, hpathHalf, hpath⟩ :=
    fp81s21_responseWindow_genuine p
  refine ⟨min δcommon δpath, lt_min hcommon0 hpath0,
    (min_le_left _ _).trans hcommonHalf, fun δ hδ hδle R hγ => ?_⟩
  have hδcommon : δ ≤ δcommon := hδle.trans (min_le_left _ _)
  have hδpath : δ ≤ δpath := hδle.trans (min_le_right _ _)
  have hδh : δ ≤ 1 / 2 := hδcommon.trans hcommonHalf
  obtain ⟨hclaims, -, hterm, -⟩ := hcommon δ hδ hδcommon R.ρβ R.thermal
  obtain ⟨C, hC0, hmode⟩ := fp81s21_response_mode_bound_of_orbits
    hδ hδh R hγ hclaims hterm
  let env : MultiIndex p.d → ℝ := fun α =>
    C * (|Co| * HRS.MS.R2WinOrb.s103_b p.d α)
  have henvSq : Summable (fun α : MultiIndex p.d => env α ^ 2) := by
    have hd1 : 1 ≤ p.d := le_trans (by norm_num) p.hd
    have hbase := HRS.MS.ProClosureS111.stationary_weight_square_summable hd1
    have hscaled := hbase.mul_left ((C * |Co|) ^ 2)
    convert hscaled using 1
    ext α
    dsimp [env]
    ring
  refine ⟨Real.sqrt (∑' α, env α ^ 2), Real.sqrt_nonneg _, fun b hb x => ?_⟩
  obtain ⟨-, -, hcoordGen⟩ := hpath δ hδ hδpath R hγ b hb x
  have hvec : ∀ t : Icc (0 : ℝ) p.T,
      OscPath.at' (responseWindow R b x) t =
        ellVec (d := p.d) (wholeSpaceIndex p.d : ℝ)
          (fun α => r26t3_a R (propagatorW (r26t3_coeff R) 0
            (b + (t : ℝ)) (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x) := by
    intro t
    apply HRS.MS.CovMeas.s101_ellVec_ext
    intro α
    rw [HRS.MS.CovMeas.s101_ellVec_coord
      (fp81s21_response_modes_memℓp_of_orbits hδ hδh R hγ hclaims hterm b hb t x)]
    exact hcoordGen t α
  have henv : ∀ α (t : Icc (0 : ℝ) p.T), |r26t3_a R
      (propagatorW (r26t3_coeff R) 0 (b + (t : ℝ))
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) x| ≤ env α := by
    intro α t
    have ht : 0 ≤ b + (t : ℝ) := by linarith [hb, t.2.1]
    simpa [env, mul_assoc, mul_left_comm, mul_comm] using
      hmode (b + (t : ℝ)) ht α x
  have hnormAt : ∀ t : Icc (0 : ℝ) p.T,
      ‖OscPath.at' (responseWindow R b x) t‖ ≤ Real.sqrt (∑' α, env α ^ 2) := by
    intro t
    rw [hvec t]
    exact HRS.MS.CovMeas.s101_norm_ellVec_le henvSq (fun α => henv α t)
  exact (ContinuousMap.norm_le (responseWindow R b x) (Real.sqrt_nonneg _)).2 hnormAt

/-- The cubic path norm and the product form of the response window are both
bounded by `K ^ 3` under the time-zero law, with the same constant `K` for
every shift `b ≥ 0`.  The probability instance is derived from the reference
density data, as in `fp81s21_responseWindow_cubic_integrable`. -/
theorem fp81s21_responseWindow_cubic_integral_le (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ, 0 < p.γ →
        ∃ K : ℝ, 0 ≤ K ∧ ∀ b : ℝ, 0 ≤ b →
          ∫ x, ‖responseWindow R b x‖ ^ 3 ∂(r26t3_mu R 0) ≤ K ^ 3 ∧
          ∫ x, ‖responseWindow R b x‖ * ‖responseWindow R b x‖ *
              ‖responseWindow R b x‖ ∂(r26t3_mu R 0) ≤ K ^ 3 := by
  classical
  obtain ⟨δU, hU0, hUHalf, hU⟩ := fp81s21_responseWindow_uniform_bound p
  obtain ⟨δC, hC0, -, hC⟩ := fp81s21_responseWindow_cubic_integrable p
  refine ⟨min δU δC, lt_min hU0 hC0, (min_le_left _ _).trans hUHalf,
    fun δ hδ hδle R hγ => ?_⟩
  have hδU : δ ≤ δU := hδle.trans (min_le_left _ _)
  have hδC : δ ≤ δC := hδle.trans (min_le_right _ _)
  have hδh : δ ≤ 1 / 2 := hδU.trans hUHalf
  obtain ⟨K, hK0, hK⟩ := hU δ hδ hδU R hγ
  refine ⟨K, hK0, fun b hb => ?_⟩
  haveI hprob : IsProbabilityMeasure (r26t3_mu R 0) := by
    obtain ⟨-, -, -, href⟩ := r26t3_reference_data p δ hδ hδh R
    obtain ⟨M₀, c₀, S, hc₀, hTc⟩ := href 0
    change IsProbabilityMeasure (HRS.Whole.withDensityReal (R.ρ 0))
    exact HRS.Whole.Q34.isProbabilityMeasure_nu hTc.prob
  obtain ⟨-, hint⟩ := hC δ hδ hδC R hγ b hb
  have hpt : ∀ x : Euc p.d, ‖responseWindow R b x‖ ^ 3 ≤ K ^ 3 := fun x =>
    pow_le_pow_left₀ (norm_nonneg _) (hK b hb x) 3
  have hconst : ∫ _x : Euc p.d, K ^ 3 ∂(r26t3_mu R 0) = K ^ 3 := by
    simp
  have hcube : ∫ x, ‖responseWindow R b x‖ ^ 3 ∂(r26t3_mu R 0) ≤ K ^ 3 := by
    calc ∫ x, ‖responseWindow R b x‖ ^ 3 ∂(r26t3_mu R 0)
        ≤ ∫ _x : Euc p.d, K ^ 3 ∂(r26t3_mu R 0) :=
          integral_mono hint (integrable_const _) (fun x => hpt x)
      _ = K ^ 3 := hconst
  have hprod : ∀ x : Euc p.d,
      ‖responseWindow R b x‖ * ‖responseWindow R b x‖ * ‖responseWindow R b x‖ =
        ‖responseWindow R b x‖ ^ 3 := fun x => by ring
  have hprodInt : ∫ x, ‖responseWindow R b x‖ * ‖responseWindow R b x‖ *
      ‖responseWindow R b x‖ ∂(r26t3_mu R 0) =
        ∫ x, ‖responseWindow R b x‖ ^ 3 ∂(r26t3_mu R 0) :=
    integral_congr_ae (Filter.Eventually.of_forall hprod)
  refine ⟨hcube, ?_⟩
  rw [hprodInt]
  exact hcube

/-- The initial cubic tensor is bounded by the same constant cube: for every
shift `b ≥ 0`, `‖initialKappa R b‖ ≤ K ^ 3`.  The probability instance is the
one required by `initialKappa`; it is taken as a hypothesis, as in
`fp81s21_initialKappa_props`. -/
theorem fp81s21_initialKappa_norm_le_cube (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ, 0 < p.γ →
        ∃ K : ℝ, 0 ≤ K ∧ ∀ b : ℝ, 0 ≤ b → ∀ [IsProbabilityMeasure (r26t3_mu R 0)],
          ‖initialKappa R b‖ ≤ K ^ 3 := by
  classical
  obtain ⟨δA, hA0, hAHalf, hA⟩ := fp81s21_responseWindow_cubic_integral_le p
  obtain ⟨δI, hI0, -, hI⟩ := fp81s21_initialKappa_props p
  refine ⟨min δA δI, lt_min hA0 hI0, (min_le_left _ _).trans hAHalf,
    fun δ hδ hδle R hγ => ?_⟩
  have hδA : δ ≤ δA := hδle.trans (min_le_left _ _)
  have hδI : δ ≤ δI := hδle.trans (min_le_right _ _)
  obtain ⟨K, hK0, hK⟩ := hA δ hδ hδA R hγ
  refine ⟨K, hK0, fun b hb => ?_⟩
  intro hprob
  have hn := (hI δ hδ hδI R hγ b hb).2.2.1
  exact hn.trans (hK b hb).2

#print axioms HRS.Fp81.S21.fp81s21_responseWindow_uniform_bound
#print axioms HRS.Fp81.S21.fp81s21_responseWindow_cubic_integral_le
#print axioms HRS.Fp81.S21.fp81s21_initialKappa_norm_le_cube

end HRS.Fp81.S21

end
