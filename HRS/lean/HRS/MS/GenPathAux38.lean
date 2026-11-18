import HRS.MS.GenPathAux37

/-!
# S5.6 packet P5e: joint measurability of `ρ_N`, the deterministic covariation density `Db`
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.GenPath

open HRS.Whole HRS.MP.RdRem

variable {d : ℕ}

theorem s56_rho_data (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) (N : ℕ) :
    (∀ r ∈ Set.Icc (0 : ℝ) b.T, Differentiable ℝ (S.ρ N r)) ∧
      ∀ y, ContinuousOn (fun r => S.ρ N r y) (Set.Icc (0 : ℝ) b.T) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hk0 : (0 : ℝ) ≤ b.k := Nat.cast_nonneg b.k
  have hL := hbv.hL
  have hs0 := hbv.hs0
  have hdL : (d : ℝ) + 3 ≤ b.L := by linarith
  have hd1 : 1 ≤ d := by have := hbv.hd; omega
  have hn : 3 ≤ b.k + 6 + ⌈(d : ℝ) / 2⌉₊ := by omega
  obtain ⟨Λ', hcoef⟩ := HRS.MS.Go.s55f_coeffHyp b hbv S N
  have hreg3 : ∀ t ∈ Set.Icc (0 : ℝ) b.T, MemCb 3 (S.ρ N t) ∧
      weightedSupE 3 ((d : ℝ) + 3) (S.ρ N t) < ⊤ ∧
      HRS.cbNorm 3 (S.ρ N t) + (weightedSupE 3 ((d : ℝ) + 3) (S.ρ N t)).toReal ≤
        (∑ j ∈ Finset.range 4, (d : ℝ) ^ j + 1) * max b.Λ 0 := fun t ht =>
    HRS.MS.Go.s55_regular_slice hn hdL (S.dens N t ht).1 (S.dens N t ht).2
  have hweak : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ContinuousOn (fun r => ∫ x, ψ x * S.ρ N r x) (Set.Icc (0 : ℝ) b.T) := by
    intro ψ hψ hcs
    obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hψ.continuous
    exact hcoef.cont ψ hψ.continuous ⟨C, fun x => by simpa using hC x⟩
  exact s56_rho_pointwise hd1 _ hreg3 hweak

/-- Measurability in `r` of the entries of the feature form against `ρ_r dx`. -/
theorem s56_featureForm_meas (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) (N : ℕ)
    (hC : OscAdjointInput (S.coeff N) b.m b.T) (q : ℝ) (u v : KSpace d b.m b.T) :
    Measurable fun r : ℝ => featureForm b.m b.T q
      (fun a => gradFeature (S.coeff N) b.m b.T a (mrrClamp b.T r))
      (HRS.Whole.withDensityReal (S.ρ N (mrrClamp b.T r))) u v := by
  have hT : 0 ≤ b.T := hbv.hT.le
  unfold featureForm
  refine (Finset.measurable_sum _ fun a _ => ?_).const_mul _
  have hprob : ∀ r : ℝ, HRS.Whole.IsProbDensity (S.ρ N (mrrClamp b.T r)) := fun r =>
    (S.mf N).density _ (mrrClamp_mem hT r)
  have : (fun r : ℝ => ∫ x, inner ℝ (gradFeature (S.coeff N) b.m b.T a (mrrClamp b.T r) x) u *
        inner ℝ (gradFeature (S.coeff N) b.m b.T a (mrrClamp b.T r) x) v
        ∂(HRS.Whole.withDensityReal (S.ρ N (mrrClamp b.T r)))) =
      fun r : ℝ => ∫ x, S.ρ N (mrrClamp b.T r) x *
        (inner ℝ (gradFeature (S.coeff N) b.m b.T a (mrrClamp b.T r) x) u *
          inner ℝ (gradFeature (S.coeff N) b.m b.T a (mrrClamp b.T r) x) v) := by
    funext r
    exact mrr_integral_withDensityReal _ (hprob r).measurable (hprob r).nonneg _
  rw [this]
  have hG : Measurable fun p : ℝ × Euc d => S.ρ N (mrrClamp b.T p.1) p.2 *
      (inner ℝ (gradFeature (S.coeff N) b.m b.T a (mrrClamp b.T p.1) p.2) u *
        inner ℝ (gradFeature (S.coeff N) b.m b.T a (mrrClamp b.T p.1) p.2) v) :=
    (s56_rho_meas b hbv S N).mul (((s56_feat_meas b hbv S N hC a).inner measurable_const).mul
      ((s56_feat_meas b hbv S N hC a).inner measurable_const))
  exact (hG.stronglyMeasurable.integral_prod_right').measurable

end HRS.MS.GenPath
