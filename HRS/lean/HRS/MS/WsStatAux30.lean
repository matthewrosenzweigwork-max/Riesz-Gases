import HRS.MS.WsStatAux29

/-!
# S21 packet L-1: positive semidefiniteness of the noise covariance matrices

`s21_noiseCov_psd`: for every finite family of times and Hermite indices the matrix `noiseCovW C q t_a t_c phi_a phi_c` (`q = S.q N`) is
positive semidefinite.  By `s56_noiseCov_eq` its entries are `int_0^{t_a ^ t_c} Db_sigma (y_a, y_c) d sigma` with `Db_sigma` a
positive semidefinite trace-class form, hence `x^T S x = int_0^T Db_sigma (w_sigma, w_sigma) d sigma >= 0` with
`w_sigma = sum_a x_a 1_{sigma <= t_a} y_a`.
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MS.S21

open HRS.Whole HRS.MS.GenPath HRS.MP.RdRem HRS.GF HRS.Uniform HRS.Whole.AppendixA HRS.Uniform.Q54c
open HRS (Euc)

variable {d : ℕ}

theorem s21_noiseCov_psd (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) (N : ℕ)
    (hC : OscAdjointInput (S.coeff N) b.m b.T) {Ctr Cmax : ℝ}
    (hOM : OrbitMaximalConclusion b.m b.T
      (fun (a : Fin d) (r : ℝ) (x : Euc d) => gradFeature (S.coeff N) b.m b.T a r x) Ctr Cmax)
    (hS : ∀ r ∈ Set.Icc (0 : ℝ) b.T, IsFiniteMeasure (HRS.Whole.withDensityReal (S.ρ N r)))
    (hq : 0 ≤ S.q N) {p : ℕ} (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) b.T)
    (αs : Fin p → MultiIndex d) :
    (Matrix.of fun a c => noiseCovW (S.coeff N) (S.q N) (ts a) (ts c)
      (oscTestFun b.m (αs a)) (oscTestFun b.m (αs c))).PosSemidef := by
  classical
  have hT0 : 0 ≤ b.T := hbv.hT.le
  set Db := s56Db b S N hOM hS (S.q N) hq with hDb
  have hDet : IsDetCovDensity b.T Db := s56Db_isDet b hbv S N hC hOM hS (S.q N) hq
  set y : Fin p → KSpace d b.m b.T := fun a => HRS.MS.S52.s52y1 b.m b.T (ts a) (αs a) with hy
  have hentry : ∀ a c, noiseCovW (S.coeff N) (S.q N) (ts a) (ts c) (oscTestFun b.m (αs a))
      (oscTestFun b.m (αs c)) = ∫ σ in Set.Icc (0 : ℝ) (min (ts a) (ts c)), Db σ (y a) (y c) := fun a c =>
    (s56_noiseCov_eq b hbv S N hC hOM hS (S.q N) hq (hts a) (hts c) (αs a) (αs c)).symm
  have hint : ∀ u v : KSpace d b.m b.T, IntegrableOn (fun σ => Db σ u v) (Set.Icc (0 : ℝ) b.T) := by
    intro u v
    refine Integrable.mono' (g := fun σ => traceNormForm (Db σ) * (‖u‖ * ‖v‖)) (hDet.int.mul_const _)
      (hDet.meas u v).aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Icc]
    exact Filter.Eventually.of_forall fun σ hσ => by
      rw [Real.norm_eq_abs]
      exact abs_apply_le_tn (hDet.traceClass σ hσ) u v
  have hsymm : ∀ a c, ∫ σ in Set.Icc (0 : ℝ) (min (ts a) (ts c)), Db σ (y a) (y c) =
      ∫ σ in Set.Icc (0 : ℝ) (min (ts c) (ts a)), Db σ (y c) (y a) := by
    intro a c
    rw [min_comm]
    refine setIntegral_congr_fun measurableSet_Icc fun σ hσ => ?_
    exact (hDet.traceClass σ ⟨hσ.1, hσ.2.trans ((min_le_left _ _).trans (hts c).2)⟩).symm _ _
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x => ?_⟩
  · ext a c
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_trivial]
    rw [hentry, hentry, hsymm]
  · -- the quadratic form
    set ind : Fin p → ℝ → ℝ := fun a σ => if σ ≤ ts a then x a else 0 with hind
    set w : ℝ → KSpace d b.m b.T := fun σ => ∑ a, ind a σ • y a with hw
    set g : Fin p → Fin p → ℝ → ℝ := fun a c => Set.indicator (Set.Icc (0 : ℝ) (min (ts a) (ts c)))
      (fun σ => Db σ (y a) (y c)) with hg
    have hgint : ∀ a c, IntegrableOn (g a c) (Set.Icc (0 : ℝ) b.T) := fun a c =>
      (hint (y a) (y c)).indicator measurableSet_Icc
    have hgeq : ∀ a c, ∫ σ in Set.Icc (0 : ℝ) b.T, g a c σ =
        ∫ σ in Set.Icc (0 : ℝ) (min (ts a) (ts c)), Db σ (y a) (y c) := by
      intro a c
      rw [hg, setIntegral_indicator measurableSet_Icc]
      have hsub : Set.Icc (0 : ℝ) b.T ∩ Set.Icc (0 : ℝ) (min (ts a) (ts c)) =
          Set.Icc (0 : ℝ) (min (ts a) (ts c)) :=
        Set.inter_eq_right.2 (Set.Icc_subset_Icc_right ((min_le_left _ _).trans (hts a).2))
      rw [hsub]
    have hexp : ∀ σ, Db σ (w σ) (w σ) = ∑ a, ∑ c, ind a σ * ind c σ * Db σ (y a) (y c) := by
      intro σ
      simp only [hw, map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
      ring
    have hpt : ∀ σ ∈ Set.Icc (0 : ℝ) b.T, Db σ (w σ) (w σ) = ∑ a, ∑ c, x a * x c * g a c σ := by
      intro σ hσ
      rw [hexp σ]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
      simp only [hind, hg, Set.indicator, Set.mem_Icc]
      by_cases ha : σ ≤ ts a <;> by_cases hc : σ ≤ ts c
      · have : σ ≤ min (ts a) (ts c) := le_min ha hc
        simp [ha, hc, hσ.1, this]
      · have : ¬ σ ≤ min (ts a) (ts c) := fun h => hc (h.trans (min_le_right _ _))
        simp [ha, hc, this]
      · have : ¬ σ ≤ min (ts a) (ts c) := fun h => ha (h.trans (min_le_left _ _))
        simp [ha, hc, this]
      · have : ¬ σ ≤ min (ts a) (ts c) := fun h => ha (h.trans (min_le_left _ _))
        simp [ha, hc, this]
    have hnn : 0 ≤ ∫ σ in Set.Icc (0 : ℝ) b.T, Db σ (w σ) (w σ) :=
      setIntegral_nonneg measurableSet_Icc fun σ hσ => (hDet.traceClass σ hσ).nonneg _
    have hform : dotProduct x (Matrix.mulVec (Matrix.of fun a c => noiseCovW (S.coeff N) (S.q N) (ts a) (ts c)
        (oscTestFun b.m (αs a)) (oscTestFun b.m (αs c))) x) =
        ∑ a, ∑ c, x a * x c * ∫ σ in Set.Icc (0 : ℝ) b.T, g a c σ := by
      simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
      rw [hgeq, hentry]
      ring
    have hswap : ∫ σ in Set.Icc (0 : ℝ) b.T, ∑ a, ∑ c, x a * x c * g a c σ =
        ∑ a, ∑ c, x a * x c * ∫ σ in Set.Icc (0 : ℝ) b.T, g a c σ := by
      rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun c _ => (hgint a c).const_mul _]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [integral_finsetSum _ fun c _ => (hgint a c).const_mul _]
      exact Finset.sum_congr rfl fun c _ => integral_const_mul _ _
    have hcongr : ∫ σ in Set.Icc (0 : ℝ) b.T, Db σ (w σ) (w σ) =
        ∫ σ in Set.Icc (0 : ℝ) b.T, ∑ a, ∑ c, x a * x c * g a c σ :=
      setIntegral_congr_fun measurableSet_Icc hpt
    have hfin : 0 ≤ dotProduct x (Matrix.mulVec (Matrix.of fun a c => noiseCovW (S.coeff N) (S.q N) (ts a) (ts c)
        (oscTestFun b.m (αs a)) (oscTestFun b.m (αs c))) x) := by
      rw [hform, ← hswap, ← hcongr]; exact hnn
    simpa using hfin

end HRS.MS.S21
