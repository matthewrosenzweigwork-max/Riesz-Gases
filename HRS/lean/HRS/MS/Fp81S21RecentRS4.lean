import HRS.MS.Fp81S21RecentRS3
import HRS.MS.Fp81S21WassersteinCoupling

/-!
# S2.1(iii), packet 34a: W2 expectation comparison with positive slack

The law is taken on the joint prediction/variation carrier.  An approximate
W2 coupling of these joint laws controls both the prediction displacement and
the variation displacement.  Marginal transfer supplies the variation L2
bounds, and the staged mixed-coupling theorem then gives the scalar estimate.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.Fp81.S21

/-- The joint RS value as a scalar function on the path/variation carrier. -/
def fp81s21_recentRSJointValue {C V : Type*}
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {C_RS : ℝ}
    (F : fp81s21_RecentRSKernel C V C_RS) (z : C × V) : ℝ :=
  F.kernel z.1 z.2

/-- Joint continuity of a bounded path-Lipschitz dual family. -/
theorem fp81s21_recentRSJointValue_continuous
    {C V : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {C_RS : ℝ}
    (hC : 0 ≤ C_RS) (F : fp81s21_RecentRSKernel C V C_RS) :
    Continuous (fp81s21_recentRSJointValue F) := by
  have hK : Continuous F.kernel :=
    LipschitzWith.continuous (LipschitzWith.of_dist_le_mul
      (K := ⟨C_RS, hC⟩) fun y y' => by
        change dist (F.kernel y) (F.kernel y') ≤ C_RS * dist y y'
        simpa [dist_eq_norm] using F.lipschitz y y')
  have hEval : Continuous fun z : (V →L[ℝ] ℝ) × V => z.1 z.2 :=
    (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := V) (F := ℝ)).continuous
  change Continuous (fun z : C × V => F.kernel z.1 z.2)
  exact hEval.comp ((hK.comp continuous_fst).prodMk continuous_snd)

private theorem fp81s21_recentRS_first_component_norm_le
    {C V : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (z : C × V) :
    ‖z.1‖ ≤ ‖z‖ := by
  simpa using (norm_fst_le z)

private theorem fp81s21_recentRS_second_component_norm_le
    {C V : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup V] [NormedSpace ℝ V] (z : C × V) :
    ‖z.2‖ ≤ ‖z‖ := by
  simpa using (norm_snd_le z)

/-- Joint-law expectation comparison.  `M` is a common second-moment bound for
the variation coordinate; the second marginal suffices in the mixed estimate. -/
theorem fp81s21_recentRS_W2_expectation_comparison
    {C V : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    (μ ν : Measure (C × V)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {C_RS e M : ℝ} (hC : 0 < C_RS) (he : 0 ≤ e) (hM : 0 ≤ M)
    (F : fp81s21_RecentRSKernel C V C_RS)
    (hW : HRS.wassersteinE 2 μ ν ≤ ENNReal.ofReal e)
    (hMomμ : MemLp (fun z : C × V => z.2) 2 μ)
    (hMomν : MemLp (fun z : C × V => z.2) 2 ν)
    (hMomentν : (∫ z : C × V, ‖z.2‖ ^ 2 ∂ν) ≤ M)
    {η : ℝ} (hη : 0 < η) :
    |(∫ z : C × V, F.kernel z.1 z.2 ∂μ) -
      (∫ z : C × V, F.kernel z.1 z.2 ∂ν)| ≤
        C_RS * (1 + Real.sqrt M) * (e + η) := by
  let B := C × V
  obtain ⟨π, hprob, hfst, hsnd, hcost, hcostBound⟩ :=
    fp81s21_exists_coupling_of_W2_le (B := B) μ ν he hW hη
  letI : IsProbabilityMeasure π := hprob
  have hmpFst : MeasurePreserving (fun w : B × B => w.1) π μ :=
    ⟨measurable_fst, hfst⟩
  have hmpSnd : MeasurePreserving (fun w : B × B => w.2) π ν :=
    ⟨measurable_snd, hsnd⟩
  let X : B × B → C := fun w => w.1.1
  let Y : B × B → C := fun w => w.2.1
  let A : B × B → V := fun w => w.1.2
  let A' : B × B → V := fun w => w.2.2
  have hA : MemLp A 2 π := by
    simpa [A, B, Function.comp_def] using hMomμ.comp_measurePreserving hmpFst
  have hA' : MemLp A' 2 π := by
    simpa [A', B, Function.comp_def] using hMomν.comp_measurePreserving hmpSnd
  have hXYmeas : AEStronglyMeasurable (fun w : B × B => X w - Y w) π := by
    change AEStronglyMeasurable (fun w : (C × V) × (C × V) => w.1.1 - w.2.1) π
    fun_prop
  have hXYSqMeas : AEStronglyMeasurable
      (fun w : B × B => ‖X w - Y w‖ ^ 2) π := by
    change AEStronglyMeasurable
      (fun w : (C × V) × (C × V) => ‖w.1.1 - w.2.1‖ ^ 2) π
    fun_prop
  have hXYSq : Integrable (fun w : B × B => ‖X w - Y w‖ ^ 2) π := by
    apply hcost.mono'
    · exact hXYSqMeas
    · filter_upwards with w
      have hle : ‖X w - Y w‖ ≤ ‖w.1 - w.2‖ := by
        change ‖(w.1 - w.2).1‖ ≤ ‖w.1 - w.2‖
        exact fp81s21_recentRS_first_component_norm_le (w.1 - w.2)
      have hleSq : ‖X w - Y w‖ ^ 2 ≤ ‖w.1 - w.2‖ ^ 2 := by
        nlinarith [hle, norm_nonneg (X w - Y w), norm_nonneg (w.1 - w.2),
          sq_nonneg (‖w.1 - w.2‖ - ‖X w - Y w‖)]
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (‖X w - Y w‖))]
      exact hleSq
  have hXY : MemLp (fun w : B × B => X w - Y w) 2 π :=
    (memLp_two_iff_integrable_sq_norm hXYmeas).2 hXYSq
  have hm : AEStronglyMeasurable X π ∧ AEStronglyMeasurable Y π ∧
      AEStronglyMeasurable A π ∧ AEStronglyMeasurable A' π := by
    refine ⟨?_, ?_, hA.aestronglyMeasurable, hA'.aestronglyMeasurable⟩
    · change AEStronglyMeasurable (fun w : (C × V) × (C × V) => w.1.1) π
      fun_prop
    · change AEStronglyMeasurable (fun w : (C × V) × (C × V) => w.2.1) π
      fun_prop
  have h2 : MemLp (fun w : B × B => X w - Y w) 2 π ∧ MemLp A 2 π ∧ MemLp A' 2 π :=
    ⟨hXY, hA, hA'⟩
  have hvarDiff : MemLp (fun w : B × B => A w - A' w) 2 π := hA.sub hA'
  have hvarSqInt : Integrable (fun w : B × B => ‖A w - A' w‖ ^ 2) π :=
    hvarDiff.norm.integrable_sq
  have hvarSqBound : (∫ w : B × B, ‖A w - A' w‖ ^ 2 ∂π) ≤ (e + η) ^ 2 := by
    calc
      (∫ w : B × B, ‖A w - A' w‖ ^ 2 ∂π) ≤
          ∫ w : B × B, ‖w.1 - w.2‖ ^ 2 ∂π := by
            apply integral_mono hvarSqInt hcost
            intro w
            have hle : ‖A w - A' w‖ ≤ ‖w.1 - w.2‖ := by
              change ‖(w.1 - w.2).2‖ ≤ ‖w.1 - w.2‖
              exact fp81s21_recentRS_second_component_norm_le (w.1 - w.2)
            nlinarith [hle, norm_nonneg (A w - A' w), norm_nonneg (w.1 - w.2),
              sq_nonneg (‖w.1 - w.2‖ - ‖A w - A' w‖)]
      _ ≤ (e + η) ^ 2 := hcostBound
  have hpathSqBound : (∫ w : B × B, ‖X w - Y w‖ ^ 2 ∂π) ≤ (e + η) ^ 2 := by
    calc
      (∫ w : B × B, ‖X w - Y w‖ ^ 2 ∂π) ≤
          ∫ w : B × B, ‖w.1 - w.2‖ ^ 2 ∂π := by
            apply integral_mono hXYSq hcost
            intro w
            have hle : ‖X w - Y w‖ ≤ ‖w.1 - w.2‖ := by
              change ‖(w.1 - w.2).1‖ ≤ ‖w.1 - w.2‖
              exact fp81s21_recentRS_first_component_norm_le (w.1 - w.2)
            nlinarith [hle, norm_nonneg (X w - Y w), norm_nonneg (w.1 - w.2),
              sq_nonneg (‖w.1 - w.2‖ - ‖X w - Y w‖)]
      _ ≤ (e + η) ^ 2 := hcostBound
  have hVarL1 : (∫ w : B × B, ‖A w - A' w‖ ∂π) ≤ e + η := by
    have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := π) (p := 2) (q := 2)
      Real.HolderConjugate.two_two
      (Filter.Eventually.of_forall fun _ => (show 0 ≤ (1 : ℝ) by norm_num))
      (Filter.Eventually.of_forall fun w => norm_nonneg (A w - A' w))
      (memLp_const (1 : ℝ) : MemLp (fun _ : B × B => (1 : ℝ)) (ENNReal.ofReal 2) π)
      (show MemLp (fun w : B × B => ‖A w - A' w‖) (ENNReal.ofReal 2) π by
        simpa using hvarDiff.norm)
    have hMean : (∫ w : B × B, ‖A w - A' w‖ ∂π) ≤
        Real.sqrt (∫ w : B × B, ‖A w - A' w‖ ^ 2 ∂π) := by
      simpa [Real.sqrt_eq_rpow, Real.rpow_two, IsProbabilityMeasure.measure_univ] using hHolder
    have hsqrt : Real.sqrt (∫ w : B × B, ‖A w - A' w‖ ^ 2 ∂π) ≤ e + η := by
      calc
        Real.sqrt (∫ w : B × B, ‖A w - A' w‖ ^ 2 ∂π) ≤ Real.sqrt ((e + η) ^ 2) :=
          Real.sqrt_le_sqrt hvarSqBound
        _ = e + η := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by linarith)]
    exact hMean.trans hsqrt
  have hpathL2 : Real.sqrt (∫ w : B × B, ‖X w - Y w‖ ^ 2 ∂π) ≤ e + η := by
    calc
      Real.sqrt (∫ w : B × B, ‖X w - Y w‖ ^ 2 ∂π) ≤ Real.sqrt ((e + η) ^ 2) :=
        Real.sqrt_le_sqrt hpathSqBound
      _ = e + η := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by linarith)]
  have hvarQmoment : (∫ w : B × B, ‖A' w‖ ^ 2 ∂π) ≤ M := by
    have hmeasQ : AEStronglyMeasurable (fun z : B => ‖z.2‖ ^ 2) (π.map Prod.snd) := by
      rw [hsnd]
      fun_prop
    have hmapInt := integral_map measurable_snd.aemeasurable hmeasQ
    have hrewrite : (∫ z : B, ‖z.2‖ ^ 2 ∂ν) =
        ∫ w : B × B, ‖A' w‖ ^ 2 ∂π := by
      rw [← hsnd]
      simpa [A] using hmapInt
    rw [← hrewrite]
    exact hMomentν
  have hvarQL2 : Real.sqrt (∫ w : B × B, ‖A' w‖ ^ 2 ∂π) ≤ Real.sqrt M :=
    Real.sqrt_le_sqrt hvarQmoment
  have hMixed := fp81s21_recentRS_mixed_expectation π hC F X Y A A' hm h2
  have hmeanBound :
      (∫ w : B × B, ‖A w - A' w‖ ∂π) +
        Real.sqrt (∫ w : B × B, ‖A' w‖ ^ 2 ∂π) *
          Real.sqrt (∫ w : B × B, ‖X w - Y w‖ ^ 2 ∂π) ≤
        (1 + Real.sqrt M) * (e + η) := by
    calc
      _ ≤ (e + η) + Real.sqrt M * (e + η) := by
        refine add_le_add hVarL1 ?_
        calc
          Real.sqrt (∫ w : B × B, ‖A' w‖ ^ 2 ∂π) *
              Real.sqrt (∫ w : B × B, ‖X w - Y w‖ ^ 2 ∂π) ≤
              Real.sqrt M * Real.sqrt (∫ w : B × B, ‖X w - Y w‖ ^ 2 ∂π) :=
            mul_le_mul_of_nonneg_right hvarQL2 (Real.sqrt_nonneg _)
          _ ≤ Real.sqrt M * (e + η) :=
            mul_le_mul_of_nonneg_left hpathL2 (Real.sqrt_nonneg _)
      _ = (1 + Real.sqrt M) * (e + η) := by ring
  have hvalP : Integrable (fun z : B => F.kernel z.1 z.2) μ := by
    have hcont := fp81s21_recentRSJointValue_continuous hC.le F
    have hmeas : Measurable (fp81s21_recentRSJointValue F) := hcont.measurable
    have hmaj : Integrable (fun z : B => C_RS * ‖z.2‖) μ :=
      (hMomμ.norm.integrable one_le_two).const_mul C_RS
    exact hmaj.mono' hmeas.aestronglyMeasurable (ae_of_all μ fun z => by
      rw [Real.norm_eq_abs]
      calc
        |F.kernel z.1 z.2| ≤ ‖F.kernel z.1‖ * ‖z.2‖ := by
          rw [← Real.norm_eq_abs]
          exact (F.kernel z.1).le_opNorm _
        _ ≤ C_RS * ‖z.2‖ := mul_le_mul_of_nonneg_right (F.bound z.1) (norm_nonneg _))
  have hvalQ : Integrable (fun z : B => F.kernel z.1 z.2) ν := by
    have hcont := fp81s21_recentRSJointValue_continuous hC.le F
    have hmeas : Measurable (fp81s21_recentRSJointValue F) := hcont.measurable
    have hmaj : Integrable (fun z : B => C_RS * ‖z.2‖) ν :=
      (hMomν.norm.integrable one_le_two).const_mul C_RS
    exact hmaj.mono' hmeas.aestronglyMeasurable (ae_of_all ν fun z => by
      rw [Real.norm_eq_abs]
      calc
        |F.kernel z.1 z.2| ≤ ‖F.kernel z.1‖ * ‖z.2‖ := by
          rw [← Real.norm_eq_abs]
          exact (F.kernel z.1).le_opNorm _
        _ ≤ C_RS * ‖z.2‖ := mul_le_mul_of_nonneg_right (F.bound z.1) (norm_nonneg _))
  have htargetP : AEStronglyMeasurable (fp81s21_recentRSJointValue F) (π.map Prod.fst) := by
    rw [hfst]
    exact hvalP.aestronglyMeasurable
  have htargetQ : AEStronglyMeasurable (fp81s21_recentRSJointValue F) (π.map Prod.snd) := by
    rw [hsnd]
    exact hvalQ.aestronglyMeasurable
  have htransferP :
      (∫ z : B, F.kernel z.1 z.2 ∂μ) =
        ∫ w : B × B, F.kernel (X w) (A w) ∂π := by
    rw [← hfst]
    simpa [X, A, fp81s21_recentRSJointValue] using
      integral_map measurable_fst.aemeasurable htargetP
  have htransferQ :
      (∫ z : B, F.kernel z.1 z.2 ∂ν) =
        ∫ w : B × B, F.kernel (Y w) (A' w) ∂π := by
    rw [← hsnd]
    simpa [Y, A', fp81s21_recentRSJointValue] using
      integral_map measurable_snd.aemeasurable htargetQ
  have hfinal := calc
      |(∫ z : B, F.kernel z.1 z.2 ∂μ) -
          (∫ z : B, F.kernel z.1 z.2 ∂ν)| =
          |(∫ w : B × B, F.kernel (X w) (A w) ∂π) -
            (∫ w : B × B, F.kernel (Y w) (A' w) ∂π)| := by rw [htransferP, htransferQ]
      _ ≤ C_RS * ((∫ w : B × B, ‖A w - A' w‖ ∂π) +
            Real.sqrt (∫ w : B × B, ‖A' w‖ ^ 2 ∂π) *
              Real.sqrt (∫ w : B × B, ‖X w - Y w‖ ^ 2 ∂π)) := hMixed
      _ ≤ C_RS * ((1 + Real.sqrt M) * (e + η)) :=
        mul_le_mul_of_nonneg_left hmeanBound hC.le
  nlinarith [hfinal]

#print axioms fp81s21_recentRSJointValue_continuous
#print axioms fp81s21_recentRS_W2_expectation_comparison

end HRS.Fp81.S21

end
