import HRS.MS.Fp81S21PredMap
import HRS.MS.ProClosureS111WeightedCompletion

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical Filter Topology
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.R2Interp HRS.MS.ProClosureS111

/-- Weighted-continuous functionals agreeing on compact smooth tests agree
on all weighted tests. In particular this applies to propagated orbits. -/
theorem fp81s21_chartAction_eq_of_compact_agreement
    {d r : ℕ} {Pw : ℝ} (hP : (d : ℝ) < 2 * Pw)
    (E : r26t6_WeightedChart d r Pw) (z : r26t6_Coeff)
    (Q : (Euc d → ℝ) → ℝ) (hQ : S102Z r Pw Q)
    (hagree : ∀ f, IsR2Test f → fp81s21_chartAction E z f = Q f)
    (f : Euc d → ℝ) (hf : IsR2WeightedTest r Pw f) :
    fp81s21_chartAction E z f = Q f := by
  obtain ⟨M, hM⟩ := hQ.bdd
  have hM' : ∀ g, IsR2WeightedTest r Pw g →
      |Q g| ≤ |M| * (weightedSobolevE r Pw g).toReal := by
    intro g hg
    exact (hM g hg).trans (mul_le_mul_of_nonneg_right (le_abs_self M) ENNReal.toReal_nonneg)
  let f' : weightedTestSubmodule d r Pw := ⟨f, weightedTestSubmodule_iff.2 hf⟩
  obtain ⟨g, hg, hconv⟩ := weighted_smooth_approximation hP f'
  have hconv' : Tendsto (fun n =>
      (weightedSobolevE r Pw ((g n - f' : weightedTestSubmodule d r Pw) : Euc d → ℝ)).toReal)
      atTop (𝓝 0) := by
    have ht := hconv.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => weightedJetMap d r Pw f') atTop (𝓝 (weightedJetMap d r Pw f')))
    have ht' := ht.norm
    simpa only [sub_self, norm_zero, ← map_sub, weightedJetMap_norm] using ht'
  have hdiff : ∀ n,
      |fp81s21_chartAction E z f - Q f| ≤
        (‖z‖ + |M|) *
          (weightedSobolevE r Pw ((g n - f' : weightedTestSubmodule d r Pw) : Euc d → ℝ)).toReal := by
    intro n
    have hw : IsR2WeightedTest r Pw ((g n - f' : weightedTestSubmodule d r Pw) : Euc d → ℝ) :=
      weightedTestSubmodule_iff.1 (g n - f').property
    have hneg : IsR2WeightedTest r Pw (-f) :=
      weightedTestSubmodule_iff.1 (-f').property
    have hgc : IsR2WeightedTest r Pw (g n : Euc d → ℝ) :=
      weightedTestSubmodule_iff.1 (g n).property
    have hqa : Q ((g n : Euc d → ℝ) - f) = Q (g n) - Q f := by
      have hh := hQ.add (g n : Euc d → ℝ) (-f) hgc hneg
      have hn : Q (-f) = - Q f := by
        simpa only [neg_one_smul, neg_one_mul] using hQ.smul (-1) f hf
      simpa [sub_eq_add_neg] using hh.trans (by rw [hn])
    have hca : fp81s21_chartAction E z ((g n : Euc d → ℝ) - f) =
        fp81s21_chartAction E z (g n) - fp81s21_chartAction E z f := by
      have hh := (fp81s21_chartAction_S102Z E z).add (g n : Euc d → ℝ) (-f) hgc hneg
      have hn : fp81s21_chartAction E z (-f) = - fp81s21_chartAction E z f := by
        simpa only [neg_one_smul, neg_one_mul] using
          (fp81s21_chartAction_S102Z E z).smul (-1) f hf
      simpa [sub_eq_add_neg] using hh.trans (by rw [hn])
    have h1 := fp81s21_chartAction_weighted_bound E z _ hw
    have h2 := hM' _ hw
    have heq := hagree (g n) (hg n)
    change |fp81s21_chartAction E z ((g n : Euc d → ℝ) - f)| ≤ _ at h1
    change |Q ((g n : Euc d → ℝ) - f)| ≤ _ at h2
    rw [hca, heq] at h1
    rw [hqa] at h2
    have := abs_sub (fp81s21_chartAction E z ((g n : Euc d → ℝ) - f))
      (Q ((g n : Euc d → ℝ) - f))
    rw [hca, hqa, heq] at this
    have hs : fp81s21_chartAction E z f - Q f =
        -((Q (g n) - fp81s21_chartAction E z f) - (Q (g n) - Q f)) := by ring
    rw [hs, abs_neg]
    calc
      _ ≤ |Q (g n) - fp81s21_chartAction E z f| + |Q (g n) - Q f| := this
      _ ≤ _ := by nlinarith
  have ht := (tendsto_const_nhds : Tendsto (fun _ : ℕ => ‖z‖ + |M|) atTop (𝓝 (‖z‖ + |M|))).mul hconv'
  have hz : Tendsto (fun n => (‖z‖ + |M|) *
      (weightedSobolevE r Pw ((g n - f' : weightedTestSubmodule d r Pw) : Euc d → ℝ)).toReal)
      atTop (𝓝 0) := by simpa using ht
  have hzero : |fp81s21_chartAction E z f - Q f| ≤ 0 :=
    le_of_tendsto_of_tendsto' tendsto_const_nhds hz hdiff
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hzero (abs_nonneg _)))

#print axioms HRS.Fp81.S21.fp81s21_chartAction_eq_of_compact_agreement

end HRS.Fp81.S21
