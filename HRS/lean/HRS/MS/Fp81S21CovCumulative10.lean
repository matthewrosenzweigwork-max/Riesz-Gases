import HRS.MS.Fp81S21CovCumulative9
import HRS.MS.Fp81S21MovingHeat3
import HRS.MS.Fp81S21MovingAllInputs

/-!
# HRS S2.1(iii), packet 19c-i: assemble the measurable covariance cumulative

The moving standing data contain the full orbit estimates in `S101Data`.
This file reconstructs the orbit-summability predicate required by the
covariance-measure constructor and applies the fixed-horizon measurable
cumulative theorem under the common small-radius and future choices.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MS.CovMeas

private theorem fp81s21_cov_weightedSup_le_of_iteratedFDeriv_bound
    {d k : ℕ} {f : Euc d → ℝ} {B : ℝ}
    (hbound : ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ B) :
    weightedSupE k 0 f ≤ ENNReal.ofReal B := by
  apply HRS.MS.Go.s55_dse_le
  intro j hj idx x
  have hdir := (iteratedFDeriv ℝ j f x).le_opNorm
    (fun l => EuclideanSpace.single (idx l) 1)
  have hpartial : |partialDeriv idx f x| ≤ B := by
    calc
      |partialDeriv idx f x| ≤ ‖iteratedFDeriv ℝ j f x‖ := by
        simpa [partialDeriv, EuclideanSpace.norm_single] using hdir
      _ ≤ B := hbound j hj x
  simpa [Real.rpow_zero] using hpartial

/-- The unpacked moving orbit data imply exactly the orbit hypothesis needed
by the covariance-measure constructor. -/
private theorem fp81s21_R2OrbitSummable_of_S101Data
    {d : ℕ} {C : WholeCoeff d} {m H : ℝ} {r : ℕ}
    {c : MultiIndex d → ℝ}
    (hD : S101Data C m H r c) : R2OrbitSummable C m H r := by
  refine ⟨?_, ?_⟩
  · intro α u hu t ht
    refine ⟨?_, ?_, ?_⟩
    · exact (hD.smoothU α u hu t ht).of_le (by norm_num)
    · intro x
      exact hD.diffT α u hu x t ht
    · simpa [s101Dt] using hD.smoothD α u hu t ht
  · have hsq : Summable (fun α : MultiIndex d => c α ^ 2) := hD.summable
    have hnonneg : ∀ α, 0 ≤ c α := hD.nonneg
    refine lt_of_le_of_lt
      (ENNReal.tsum_le_tsum fun α => ?_)
      (hsq.mul_left 2).tsum_ofReal_lt_top
    refine iSup_le fun u => iSup_le fun hu =>
      iSup_le fun t => iSup_le fun ht => ?_
    have hU := fp81s21_cov_weightedSup_le_of_iteratedFDeriv_bound
      (fun j hj x => hD.bddU α u hu t ht j hj x)
    have hD' := fp81s21_cov_weightedSup_le_of_iteratedFDeriv_bound
      (fun j hj x => hD.bddD α u hu t ht j hj x)
    calc
      weightedSupE (r + 1) 0 (propagatorW C u t (oscTestFun m α)) ^ 2 +
          weightedSupE (r + 1) 0
            (fun x => s101Dt C m H u t α x) ^ 2 ≤
          ENNReal.ofReal (c α) ^ 2 + ENNReal.ofReal (c α) ^ 2 := by
            exact add_le_add (by gcongr) (by gcongr)
      _ = ENNReal.ofReal (2 * c α ^ 2) := by
        rw [← ENNReal.ofReal_pow (hnonneg α)]
        rw [← ENNReal.ofReal_add (sq_nonneg (c α)) (sq_nonneg (c α))]
        congr 1
        ring

/-- One common small radius and one future give the full measurable raw-eta
covariance cumulative packet contract. -/
theorem fp81s21_moving_raw_eta_measurable_cumulative (p : Parameters) :
    fp81s21_rawEtaCovarianceMeasurableCumulativeSpec p := by
  obtain ⟨δi, hδi, hihalf, hinputs⟩ := fp81s21_moving_inputs_all p
  obtain ⟨δh, hδh, hhhalf, hheat⟩ :=
    fp81s21_moving_heat_family_window_derivs p
  refine ⟨min δi δh, lt_min hδi hδh,
    (min_le_left _ _).trans hihalf, ?_⟩
  intro δ hδ hδle R
  have hδi' : δ ≤ δi := hδle.trans (min_le_left _ _)
  have hδh' : δ ≤ δh := hδle.trans (min_le_right _ _)
  obtain ⟨future, hfuture, -⟩ := hheat δ hδ hδh' R
  refine ⟨future, hfuture, ?_⟩
  intro a ha N hN A
  dsimp
  let H : ℝ := a + p.T
  have hH : 0 < H := by dsimp [H]; linarith [p.hT]
  obtain ⟨c, hstd, hphysical⟩ := hinputs δ hδ hδi' R a ha
  have horb : R2OrbitSummable (r26t3_coeff R)
      (wholeSpaceIndex p.d : ℝ) H (2 * p.d + 8) :=
    fp81s21_R2OrbitSummable_of_S101Data hstd.hD
  have hlin : S102Lin (r26t3_coeff R)
      (wholeSpaceIndex p.d : ℝ) H := fp81s21_S102Lin p R H
  have hphysicalH : Fp81MovingPhysicalInputs R hN A H := by
    simpa [H] using hphysical N hN A
  exact fp81s21_moving_raw_eta_measurable_cumulative_fixed p R hδ
    (hδh'.trans hhhalf) hH horb hlin hN A hphysicalH

#print axioms HRS.Fp81.S21.fp81s21_R2OrbitSummable_of_S101Data
#print axioms HRS.Fp81.S21.fp81s21_moving_raw_eta_measurable_cumulative

end HRS.Fp81.S21

end
