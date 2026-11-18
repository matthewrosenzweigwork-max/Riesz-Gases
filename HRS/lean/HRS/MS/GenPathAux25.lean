import HRS.MS.GenPathAux24
import HRS.Whole.Q09AAux9
import HRS.MS.ThmCons

/-!
# S5.6 packet P7c: the initial state `k₀` of the particle path reproduces the initial path
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.GenPath

open HRS.Whole HRS.MP.RdRem

variable {d : ℕ}

theorem s56_integrable_norm_withDensity {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ)
    (hmom : Integrable (fun x : Euc d => ‖x‖ ^ 2 * ρ x)) :
    Integrable (fun x : Euc d => ‖x‖) (HRS.Whole.withDensityReal ρ) := by
  have := HRS.MS.Thm.cb_withDensityReal_isProb hρ
  have h2 := HRS.Whole.Q09A.integrable_sq_withDensityReal hρ hmom
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add h2) continuous_norm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  show ‖x‖ ≤ 1 + ‖x‖ ^ 2
  nlinarith [sq_nonneg (‖x‖ - 1)]

theorem s56_k0_eval (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) (N : ℕ) (hN : 1 ≤ N)
    (hC : OscAdjointInput (S.coeff N) b.m b.T) (σ : ℝ) (x : EucConfig d N) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) b.T) (α : MultiIndex d) :
    OscDual.coord ((s56k0 (S.coeff N) b.m b.T σ (HRS.Whole.empirical x) (HRS.Whole.withDensityReal (S.ρ N 0))).evalA t) α =
      σ * (HRS.Whole.pair (HRS.Whole.empirical x) (propagatorW (S.coeff N) 0 t (oscTestFun b.m α)) -
        HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N 0)) (propagatorW (S.coeff N) 0 t (oscTestFun b.m α))) := by
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
  have : IsProbabilityMeasure (HRS.Whole.empirical x) := HRS.Whole.empirical_isProbabilityMeasure (by omega) x
  have hρ := (S.mf N).density 0 h0
  have := HRS.MS.Thm.cb_withDensityReal_isProb hρ
  have hνint : Integrable (fun z : Euc d => ‖z‖) (HRS.Whole.empirical x) := HRS.Whole.Q09A.integrable_empirical (by omega) x _
  have hμint := s56_integrable_norm_withDensity hρ ((S.mf N).second_moment 0 h0)
  have hcl := s56_osc_classical b hbv S N ht α
  obtain ⟨B, hB⟩ := hcl.bdd 0 (Nat.zero_le _)
  have hh : ContDiff ℝ 1 (propagatorW (S.coeff N) 0 t (oscTestFun b.m α)) :=
    (hcl.c2 0 ⟨le_rfl, ht.1⟩).of_le (by norm_num)
  rw [HRS.MS.S52.s52_coord_evalA ht.1 ht.2]
  rw [s56_k0_inner (S.coeff N) b.m b.T σ |Cf| (abs_nonneg _) hmeas hbd (HRS.Whole.empirical x)
    (HRS.Whole.withDensityReal (S.ρ N 0)) hνint hμint (HRS.MS.S52.s52y1 b.m b.T t α)
    (propagatorW (S.coeff N) 0 t (oscTestFun b.m α)) hh B
    (fun z => by
      have := hB 0 ⟨le_rfl, ht.1⟩ z
      rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this)
    (fun a z => by
      rw [HRS.MS.S52.s52_pair_grad_y1 hC ht.2 a h0 z α]
      simp [ht.1])]
  rfl

end HRS.MS.GenPath
