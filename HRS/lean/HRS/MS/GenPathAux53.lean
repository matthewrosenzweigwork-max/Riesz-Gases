import HRS.MS.GenPathAux52

/-!
# S5.6 packet P6h: measurability of `k₀`, `evalA`, `𝒯M` and `R`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS HRS.Whole HRS.MP.RdRem

variable {d : ℕ}

theorem s56_evalA_cont {m T : ℝ} (hT : 0 ≤ T) (t : ℝ) :
    Continuous fun x : KSpace d m T => x.evalA t := by
  let L : KSpace d m T →ₗ[ℝ] OscDual d m :=
    { toFun := fun x => x.evalA t
      map_add' := fun x y => s56_evalA_add x y t
      map_smul' := fun c x => s56_evalA_smul c x t }
  have hL : ∀ x, ‖L x‖ ≤ (1 + Real.sqrt T) * ‖x‖ := by
    intro x
    have h1 := HRS.MS.U9.u9_evalA_norm_le hT x t
    have h2 := HRS.MS.U9.u9_norm_A₀_le x
    have h3 := HRS.MS.U9.u9_norm_A'_le x
    have : Real.sqrt T * ‖x.A'‖ ≤ Real.sqrt T * ‖x‖ :=
      mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _)
    show ‖x.evalA t‖ ≤ _
    nlinarith
  exact (L.mkContinuous (1 + Real.sqrt T) hL).continuous

theorem s56_k0_meas' (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) {N : ℕ} (hN : 1 ≤ N)
    (hC : OscAdjointInput (S.coeff N) b.m b.T) (σ : ℝ) :
    Measurable fun x : EucConfig d N =>
      s56k0 (S.coeff N) b.m b.T σ (HRS.Whole.empirical x) (HRS.Whole.withDensityReal (S.ρ N 0)) := by
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
  have hρ := (S.mf N).density 0 h0
  have := HRS.MS.Thm.cb_withDensityReal_isProb hρ
  have hμint := s56_integrable_norm_withDensity hρ ((S.mf N).second_moment 0 h0)
  exact s56_k0_meas (S.coeff N) b.m b.T σ |Cf| (abs_nonneg _) hmeas hbd (by omega) _ hμint

theorem s56_K0_meas (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) {N : ℕ} (hN : 1 ≤ N)
    (hC : OscAdjointInput (S.coeff N) b.m b.T) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X : ℝ≥0 → Ω → EucConfig d N) (hX0 : Measurable (X 0)) : Measurable (s56K0 S X) :=
  (s56_k0_meas' b hbv S hN hC (S.σ N)).comp hX0

theorem s56_R_meas (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) {N : ℕ} (hN : 1 ≤ N)
    (hC : OscAdjointInput (S.coeff N) b.m b.T) {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (X : ℝ≥0 → Ω → EucConfig d N) (hXm : ∀ t, Measurable (X t)) (M : ℝ → Ω → KSpace d b.m b.T)
    (hMm : ∀ t, Measurable (M t)) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) b.T) :
    Measurable (s56R S X M t) := by
  have hT : 0 ≤ b.T := hbv.hT.le
  unfold s56R
  refine ((s56_xi_meas b hbv S (by omega) X hXm t ht).sub
    ((s56_evalA_cont hT t).measurable.comp (s56_K0_meas b hbv S hN hC X (hXm 0)))).sub ?_
  unfold reconstructPath
  exact (((s56_evalA_cont hT t).measurable.comp (hMm b.T)).sub
    (HRS.MS.U9.u9_continuous_B.measurable.comp (hMm b.T))).add
    (HRS.MS.U9.u9_continuous_B.measurable.comp (hMm t))

end HRS.MS.GenPath
