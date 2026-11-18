import HRS.MS.S82P2Grad4

/-!
# S8.2 (S82P2): gradient model of the pair statistic and its second moment (UNCOMPILED DRAFT)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S82P2
open HRS HRS.Whole HRS.MS.Phase2S82

/-- The explicit (measurable) model of the site gradient of the pair statistic. -/
def s82p2_gradModel {d m : ℕ} (Q : Euc d → Euc d → ℝ) (i : Fin (m + 1))
    (X : EucConfig d (m + 1)) : Euc d :=
  (2 * ((m + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) •
    ∑ k : Fin m, s82p2_gt Q (X i) (X (i.succAbove k))

lemma s82p2_gradModel_measurable {d m : ℕ} (Q : Euc d → Euc d → ℝ) (i : Fin (m + 1)) :
    Measurable (s82p2_gradModel (m := m) Q i) := by
  unfold s82p2_gradModel
  have h2 : ∀ k : Fin m, Measurable (fun X : EucConfig d (m + 1) => (X i, X (i.succAbove k))) :=
    fun k => (measurable_pi_apply i).prodMk (measurable_pi_apply _)
  have hs : Measurable (fun X : EucConfig d (m + 1) =>
      ∑ k : Fin m, s82p2_gt Q (X i) (X (i.succAbove k))) :=
    Finset.measurable_sum _ fun k _ => (s82p2_gt_measurable Q).comp (h2 k)
  exact hs.const_smul (2 * ((m + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))

lemma s82p2_gradModel_ae {d : ℕ} (hd : 2 ≤ d) {a beta C0 M A : ℝ} {rho : Euc d → ℝ}
    {q : Euc d → ℝ} {h : ℕ → Euc d → ℝ} [IsProbabilityMeasure (HRS.Whole.withDensityReal rho)]
    (hW : WeakReferenceSetup d a beta rho q h C0) {f : Euc d → ℝ} {Q : Euc d → Euc d → ℝ}
    (hQ : PairCorrector a beta rho M A f Q) {m : ℕ} (hm : 1 ≤ m) :
    ∀ᵐ X ∂referenceLaw q h (HRS.Whole.withDensityReal rho) beta (m + 1) (m + 1)
        (fun i : Fin 0 => i.elim0),
      ∀ i : Fin (m + 1), Phase2S82.configGrad (Phase2S82.pairStatistic (N := m + 1) Q) X i =
        s82p2_gradModel Q i X := by
  rw [ae_all_iff]
  intro i
  rw [ae_iff]
  refine measure_mono_null ?_ (s82p2_noncollision hd hW hm i)
  intro X hX
  by_contra hnb
  have hnb' : ∀ j, j ≠ i → X j ≠ X i := fun j hj hjx => hnb ⟨j, hj, hjx⟩
  apply hX
  rw [s82p2_configGrad_pair hQ i X hnb']
  unfold s82p2_gradModel
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [s82p2_gt_eq hQ _ _ (fun hh => hnb' _ (Fin.succAbove_ne i k) hh.symm)]

end HRS.MS.S82P2
