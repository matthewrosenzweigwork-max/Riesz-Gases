import HRS.MS.GenPathAux38

/-!
# S5.6 packet P5f: the deterministic covariation density `Db` (an `IsDetCovDensity`)
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.GenPath

open HRS.Whole HRS.MP.RdRem

variable {d : ℕ}

open Classical in
/-- The bounded bilinear form `C̄_r = featureForm(Γ(r), ρ_r dx)` of `OrbitMaximalConclusion` (clause (i)), `0` off `[0,T]`. -/
def s56Db (b : WholeBounds d) (S : WholeSetup b) (N : ℕ) {Ctr Cmax : ℝ}
    (hOM : OrbitMaximalConclusion b.m b.T
      (fun (a : Fin d) (r : ℝ) (x : Euc d) => gradFeature (S.coeff N) b.m b.T a r x) Ctr Cmax)
    (hS : ∀ r ∈ Set.Icc (0 : ℝ) b.T, IsFiniteMeasure (HRS.Whole.withDensityReal (S.ρ N r)))
    (q : ℝ) (hq : 0 ≤ q) (r : ℝ) : KSpace d b.m b.T →L[ℝ] KSpace d b.m b.T →L[ℝ] ℝ :=
  if h : r ∈ Set.Icc (0 : ℝ) b.T then
    Classical.choose (hOM.1 q hq r h (HRS.Whole.withDensityReal (S.ρ N r)) (hS r h))
  else 0

theorem s56Db_spec (b : WholeBounds d) (S : WholeSetup b) (N : ℕ) {Ctr Cmax : ℝ}
    (hOM : OrbitMaximalConclusion b.m b.T
      (fun (a : Fin d) (r : ℝ) (x : Euc d) => gradFeature (S.coeff N) b.m b.T a r x) Ctr Cmax)
    (hS : ∀ r ∈ Set.Icc (0 : ℝ) b.T, IsFiniteMeasure (HRS.Whole.withDensityReal (S.ρ N r)))
    (q : ℝ) (hq : 0 ≤ q) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) b.T) :
    (∀ u v, s56Db b S N hOM hS q hq r u v = featureForm b.m b.T q
        (fun a => gradFeature (S.coeff N) b.m b.T a r) (HRS.Whole.withDensityReal (S.ρ N r)) u v) ∧
      IsTraceClassCov (s56Db b S N hOM hS q hq r) ∧
      traceNormForm (s56Db b S N hOM hS q hq r) ≤
        Ctr * q * ((HRS.Whole.withDensityReal (S.ρ N r)) Set.univ).toReal := by
  unfold s56Db
  rw [dif_pos hr]
  exact Classical.choose_spec (hOM.1 q hq r hr (HRS.Whole.withDensityReal (S.ρ N r)) (hS r hr))

theorem s56Db_zero (b : WholeBounds d) (S : WholeSetup b) (N : ℕ) {Ctr Cmax : ℝ}
    (hOM : OrbitMaximalConclusion b.m b.T
      (fun (a : Fin d) (r : ℝ) (x : Euc d) => gradFeature (S.coeff N) b.m b.T a r x) Ctr Cmax)
    (hS : ∀ r ∈ Set.Icc (0 : ℝ) b.T, IsFiniteMeasure (HRS.Whole.withDensityReal (S.ρ N r)))
    (q : ℝ) (hq : 0 ≤ q) {r : ℝ} (hr : r ∉ Set.Icc (0 : ℝ) b.T) :
    s56Db b S N hOM hS q hq r = 0 := by
  unfold s56Db
  rw [dif_neg hr]

theorem s56Db_isDet (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) (N : ℕ) {Ctr Cmax : ℝ}
    (hC : OscAdjointInput (S.coeff N) b.m b.T)
    (hOM : OrbitMaximalConclusion b.m b.T
      (fun (a : Fin d) (r : ℝ) (x : Euc d) => gradFeature (S.coeff N) b.m b.T a r x) Ctr Cmax)
    (hS : ∀ r ∈ Set.Icc (0 : ℝ) b.T, IsFiniteMeasure (HRS.Whole.withDensityReal (S.ρ N r)))
    (q : ℝ) (hq : 0 ≤ q) :
    IsDetCovDensity b.T (s56Db b S N hOM hS q hq) := by
  have hT : 0 ≤ b.T := hbv.hT.le
  have hm : ∀ u v : KSpace d b.m b.T, Measurable fun r => s56Db b S N hOM hS q hq r u v := by
    intro u v
    have h1 := s56_featureForm_meas b hbv S N hC q u v
    have : (fun r => s56Db b S N hOM hS q hq r u v) = fun r =>
        if r ∈ Set.Icc (0 : ℝ) b.T then featureForm b.m b.T q
          (fun a => gradFeature (S.coeff N) b.m b.T a (mrrClamp b.T r))
          (HRS.Whole.withDensityReal (S.ρ N (mrrClamp b.T r))) u v else 0 := by
      funext r
      by_cases hr : r ∈ Set.Icc (0 : ℝ) b.T
      · rw [if_pos hr, (s56Db_spec b S N hOM hS q hq hr).1, mrrClamp_of_mem hr]
      · rw [if_neg hr, s56Db_zero b S N hOM hS q hq hr]; rfl
    rw [this]
    exact Measurable.ite measurableSet_Icc h1 measurable_const
  refine ⟨hm, fun r hr => (s56Db_spec b S N hOM hS q hq hr).2.1, ?_⟩
  have hmeas : Measurable fun r => traceNormForm (s56Db b S N hOM hS q hq r) :=
    HRS.measurable_traceNormForm _ hm
  refine Measure.integrableOn_of_bounded (M := |Ctr * q|) (by simp) hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall fun r hr => ?_)
  rw [Real.norm_of_nonneg (traceNormForm_nonneg _)]
  have hspec := (s56Db_spec b S N hOM hS q hq hr).2.2
  haveI hfin := hS r hr
  haveI hpr : IsProbabilityMeasure (HRS.Whole.withDensityReal (S.ρ N r)) :=
    HRS.MS.Thm.cb_withDensityReal_isProb ((S.mf N).density r hr)
  rw [measure_univ] at hspec
  simp only [ENNReal.toReal_one, mul_one] at hspec
  exact hspec.trans (le_abs_self _)

end HRS.MS.GenPath
