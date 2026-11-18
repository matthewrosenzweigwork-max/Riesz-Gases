import HRS.MS.WsStatAux18

/-!
# S21 packet F3e: definitions, measurability and continuity of the centred remainder

`s21Xi S X nubar t = sigma (mu_N^t - nubar)`, `s21K0c`, `s21Rt = s21Xi - A(s21K0c) - T M` (see `WsStatAux18`).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.MS.S21

open HRS.Whole HRS.MS.GenPath HRS.MP.RdRem
open HRS (Euc)

variable {d : ℕ}

section Defs

variable {b : WholeBounds d} (S : WholeSetup b) {N : ℕ} {Ω : Type*}

/-- The exactly centred field `σ (μ_N^t - ν̄)`. -/
def s21Xi (X : ℝ≥0 → Ω → EucConfig d N) (νb : Measure (Euc d)) (t : ℝ) (ζ : Ω) : OscDual d b.m :=
  S.σ N • OscDual.ofMeasureDiff b.m (HRS.Whole.empirical (X (Real.toNNReal t) ζ)) νb

/-- The centred initial state. -/
def s21K0c (X : ℝ≥0 → Ω → EucConfig d N) (νb : Measure (Euc d)) (ζ : Ω) : KSpace d b.m b.T :=
  s56k0 (S.coeff N) b.m b.T (S.σ N) (HRS.Whole.empirical (X 0 ζ)) νb

/-- The centred remainder. -/
def s21Rt (X : ℝ≥0 → Ω → EucConfig d N) (νb : Measure (Euc d)) (M : ℝ → Ω → KSpace d b.m b.T)
    (t : ℝ) (ζ : Ω) : OscDual d b.m :=
  s21Xi S X νb t ζ - (s21K0c S X νb ζ).evalA t - reconstructPath b.m b.T M ζ t

end Defs

theorem s21_dm (b : WholeBounds d) (hbv : b.Valid) : 1 ≤ d ∧ (d : ℝ) < b.m := by
  refine ⟨by have := hbv.hd; omega, ?_⟩
  have := hbv.hm
  have h1 : (0 : ℝ) ≤ b.J := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  linarith

theorem s21_Xi_meas (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) {N : ℕ} (hN : 0 < N)
    {Ω : Type*} [MeasurableSpace Ω] (X : ℝ≥0 → Ω → EucConfig d N) (hXm : ∀ t, Measurable (X t))
    (νb : Measure (Euc d)) [IsProbabilityMeasure νb] (t : ℝ) : Measurable (s21Xi S X νb t) :=
  (s56_xi_cont_config (s21_dm b hbv).1 (s21_dm b hbv).2 (S.σ N) hN νb).measurable.comp (hXm _)

theorem s21_Xi_cont (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) {N : ℕ} (hN : 0 < N)
    {Ω : Type*} (X : ℝ≥0 → Ω → EucConfig d N) (νb : Measure (Euc d)) [IsProbabilityMeasure νb] (ζ : Ω)
    (hX : ∀ i, Continuous fun t : ℝ≥0 => X t ζ i) : Continuous fun t : ℝ => s21Xi S X νb t ζ := by
  have h1 : Continuous fun t : ℝ≥0 => X t ζ := continuous_pi hX
  exact (s56_xi_cont_config (s21_dm b hbv).1 (s21_dm b hbv).2 (S.σ N) hN νb).comp
    (h1.comp continuous_real_toNNReal)

theorem s21_K0c_meas (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) {N : ℕ} (hN : 1 ≤ N)
    (hC : OscAdjointInput (S.coeff N) b.m b.T) {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → EucConfig d N) (hX0 : Measurable (X 0)) (νb : Measure (Euc d))
    [IsProbabilityMeasure νb] (hν : Integrable (fun x : Euc d => ‖x‖) νb) :
    Measurable (s21K0c S X νb) := by
  have hT : 0 ≤ b.T := hbv.hT.le
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) b.T := ⟨le_rfl, hT⟩
  obtain ⟨Cf, hCf⟩ := HRS.MS.Star.general_orbits_features_proof b hbv
  have hbd : ∀ (a : Fin d) (z : Euc d), ‖gradFeature (S.coeff N) b.m b.T a 0 z‖ ≤ |Cf| := fun a z => by
    have := (hCf S N a 0 h0).2 0 (Nat.zero_le _) z
    rw [norm_iteratedFDeriv_zero] at this
    exact this.trans (le_abs_self _)
  have hmeas : ∀ a : Fin d, Measurable fun z : Euc d => gradFeature (S.coeff N) b.m b.T a 0 z := by
    intro a
    have := (s56_feat_meas b hbv S N hC a).comp (measurable_const (a := (0 : ℝ)).prodMk measurable_id)
    have e := mrrClamp_of_mem h0
    simp only [Function.comp_def, e] at this
    exact this
  exact (s56_k0_meas (S.coeff N) b.m b.T (S.σ N) |Cf| (abs_nonneg _) hmeas hbd (by omega) νb hν).comp hX0

theorem s21_Rt_meas (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) {N : ℕ} (hN : 1 ≤ N)
    (hC : OscAdjointInput (S.coeff N) b.m b.T) {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → EucConfig d N) (hXm : ∀ t, Measurable (X t)) (νb : Measure (Euc d))
    [IsProbabilityMeasure νb] (hν : Integrable (fun x : Euc d => ‖x‖) νb)
    (M : ℝ → Ω → KSpace d b.m b.T) (hMm : ∀ t, Measurable (M t)) (t : ℝ) :
    Measurable (s21Rt S X νb M t) := by
  have hT : 0 ≤ b.T := hbv.hT.le
  unfold s21Rt
  refine ((s21_Xi_meas b hbv S (by omega) X hXm νb t).sub
    ((s56_evalA_cont hT t).measurable.comp (s21_K0c_meas b hbv S hN hC X (hXm 0) νb hν))).sub ?_
  unfold reconstructPath
  exact (((s56_evalA_cont hT t).measurable.comp (hMm b.T)).sub
    (HRS.MS.U9.u9_continuous_B.measurable.comp (hMm b.T))).add
    (HRS.MS.U9.u9_continuous_B.measurable.comp (hMm t))

theorem s21_Rt_cont (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) {N : ℕ} (hN : 1 ≤ N)
    {Ω : Type*} (X : ℝ≥0 → Ω → EucConfig d N) (νb : Measure (Euc d)) [IsProbabilityMeasure νb]
    (M : ℝ → Ω → KSpace d b.m b.T) (ζ : Ω) (hX : ∀ i, Continuous fun t : ℝ≥0 => X t ζ i)
    (hMc : ContinuousOn (fun τ => M τ ζ) (Set.Icc (0 : ℝ) b.T)) :
    ContinuousOn (fun t => s21Rt S X νb M t ζ) (Set.Icc (0 : ℝ) b.T) := by
  have hT : 0 ≤ b.T := hbv.hT.le
  unfold s21Rt
  refine ContinuousOn.sub (ContinuousOn.sub (s21_Xi_cont b hbv S (by omega) X νb ζ hX).continuousOn
    (HRS.MS.U9.u9_continuousOn_evalA hT _)) ?_
  exact continuousOn_iff_continuous_restrict.2
    (HRS.MS.U9.u9_continuous_recon hT M ζ hMc)

end HRS.MS.S21
