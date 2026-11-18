import HRS.MS.Fp81S21RecentRS5

/-! The signed recent comparison on the joint prediction/drift/covariance law.
Each kernel is lifted separately; the product norm remains the max norm. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory
namespace HRS.Fp81.S21

private def fp81s21_recentRS_comp_contract
    {C V W : Type*} [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {K : ℝ} (hK : 0 ≤ K)
    (F : fp81s21_RecentRSKernel C V K) (P : W →L[ℝ] V)
    (hP : ∀ w, ‖P w‖ ≤ ‖w‖) : fp81s21_RecentRSKernel C W K where
  kernel y := (F.kernel y).comp P
  bound y := by
    apply ContinuousLinearMap.opNorm_le_bound _ hK
    intro w
    exact ((F.kernel y).le_opNorm (P w)).trans
      ((mul_le_mul_of_nonneg_right (F.bound y) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (hP w) hK))
  lipschitz y z := by
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hK (norm_nonneg _))
    intro w
    change ‖(F.kernel y - F.kernel z) (P w)‖ ≤ _
    exact ((F.kernel y - F.kernel z).le_opNorm (P w)).trans
      ((mul_le_mul_of_nonneg_right (F.lipschitz y z) (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (hP w) (mul_nonneg hK (norm_nonneg _))))

private theorem fp81s21_recentRS_memLp_pair
    {Ω D J : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup D] [NormedAddCommGroup J]
    {μ : Measure Ω} {d : Ω → D} {j : Ω → J}
    (hd : MemLp d 2 μ) (hj : MemLp j 2 μ) :
    MemLp (fun ω => (d ω, j ω)) 2 μ := by
  apply (hd.norm.add hj.norm).mono' (hd.aestronglyMeasurable.prodMk hj.aestronglyMeasurable)
  filter_upwards with ω
  exact max_le_add_of_nonneg (norm_nonneg (d ω)) (norm_nonneg (j ω))

private theorem fp81s21_recentRS_source_comparison
    {Ω Ω' C V : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Ω → C × V) (Y : Ω' → C × V) (hX : Measurable X) (hY : Measurable Y)
    {K e M η : ℝ} (hK : 0 < K) (he : 0 ≤ e) (hM : 0 ≤ M) (hη : 0 < η)
    (F : fp81s21_RecentRSKernel C V K)
    (hW : HRS.wassersteinE 2 (μ.map X) (ν.map Y) ≤ ENNReal.ofReal e)
    (hMX : MemLp (fun ω => (X ω).2) 2 μ)
    (hMY : MemLp (fun ω => (Y ω).2) 2 ν)
    (hMoment : (∫ ω, ‖(Y ω).2‖ ^ 2 ∂ν) ≤ M) :
    |(∫ ω, F.kernel (X ω).1 (X ω).2 ∂μ) -
      (∫ ω, F.kernel (Y ω).1 (Y ω).2 ∂ν)| ≤ K * (1 + Real.sqrt M) * (e + η) := by
  letI : IsProbabilityMeasure (μ.map X) := (Measure.isProbabilityMeasure_map_iff hX.aemeasurable).2 inferInstance
  letI : IsProbabilityMeasure (ν.map Y) := (Measure.isProbabilityMeasure_map_iff hY.aemeasurable).2 inferInstance
  have hfst : AEStronglyMeasurable (fun z : C × V => z.2) (μ.map X) :=
    measurable_snd.aestronglyMeasurable
  have hsnd : AEStronglyMeasurable (fun z : C × V => z.2) (ν.map Y) :=
    measurable_snd.aestronglyMeasurable
  have hmX : MemLp (fun z : C × V => z.2) 2 (μ.map X) :=
    (memLp_map_measure_iff hfst hX.aemeasurable).2 hMX
  have hmY : MemLp (fun z : C × V => z.2) 2 (ν.map Y) :=
    (memLp_map_measure_iff hsnd hY.aemeasurable).2 hMY
  have hm : (∫ z : C × V, ‖z.2‖ ^ 2 ∂ν.map Y) ≤ M := by
    rw [integral_map hY.aemeasurable (by fun_prop)]
    exact hMoment
  have hb := fp81s21_recentRS_W2_expectation_comparison
    (μ.map X) (ν.map Y) hK he hM F hW hmX hmY hm hη
  have hcont := fp81s21_recentRSJointValue_continuous hK.le F
  have htransferX := integral_map hX.aemeasurable
    (hcont.measurable.aestronglyMeasurable (μ := μ.map X))
  have htransferY := integral_map hY.aemeasurable
    (hcont.measurable.aestronglyMeasurable (μ := ν.map Y))
  change (∫ z : C × V, F.kernel z.1 z.2 ∂μ.map X) = _ at htransferX
  change (∫ z : C × V, F.kernel z.1 z.2 ∂ν.map Y) = _ at htransferY
  rw [htransferX, htransferY] at hb
  exact hb

/-- The physical signs and half factor give `KD + KJ/2`, with no product-norm
loss and no particle-scale factor. The supplied maps may be the start-dependent
physical carriers. Their summed square moment bounds the max-norm moment. -/
theorem fp81s21_recentRS_joint_signed_comparison
    {Ω Ω' C D J : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [NormedAddCommGroup C] [NormedSpace ℝ C]
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup J] [NormedSpace ℝ J]
    [MeasurableSpace C] [BorelSpace C] [SecondCountableTopology C]
    [MeasurableSpace D] [BorelSpace D] [SecondCountableTopology D]
    [MeasurableSpace J] [BorelSpace J] [SecondCountableTopology J]
    (μ : Measure Ω) (ν : Measure Ω') [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (yN : Ω → C) (dN : Ω → D) (jN : Ω → J)
    (yG : Ω' → C) (dG : Ω' → D) (jG : Ω' → J)
    (hmN : Measurable (fun ω => (yN ω, (dN ω, jN ω))))
    (hmG : Measurable (fun ω => (yG ω, (dG ω, jG ω))))
    (hdN : MemLp dN 2 μ) (hjN : MemLp jN 2 μ)
    (hdG : MemLp dG 2 ν) (hjG : MemLp jG 2 ν)
    {KD KJ e M η : ℝ} (hKD : 0 < KD) (hKJ : 0 < KJ)
    (he : 0 ≤ e) (hM : 0 ≤ M) (hη : 0 < η)
    (FD : fp81s21_RecentRSKernel C D KD) (FJ : fp81s21_RecentRSKernel C J KJ)
    (hW : HRS.wassersteinE 2 (μ.map (fun ω => (yN ω, (dN ω, jN ω))))
      (ν.map (fun ω => (yG ω, (dG ω, jG ω)))) ≤ ENNReal.ofReal e)
    (hMoment : (∫ ω, (‖dG ω‖ ^ 2 + ‖jG ω‖ ^ 2) ∂ν) ≤ M) :
    |fp81s21_recentRSCorrection (∫ ω, FD.kernel (yN ω) (dN ω) ∂μ)
        (∫ ω, FJ.kernel (yN ω) (jN ω) ∂μ) -
      fp81s21_recentRSCorrection (∫ ω, FD.kernel (yG ω) (dG ω) ∂ν)
        (∫ ω, FJ.kernel (yG ω) (jG ω) ∂ν)| ≤
      (KD + KJ / 2) * (1 + Real.sqrt M) * (e + η) := by
  let FD' := fp81s21_recentRS_comp_contract hKD.le FD
    (ContinuousLinearMap.fst ℝ D J) norm_fst_le
  let FJ' := fp81s21_recentRS_comp_contract hKJ.le FJ
    (ContinuousLinearMap.snd ℝ D J) norm_snd_le
  have hpairN := fp81s21_recentRS_memLp_pair hdN hjN
  have hpairG := fp81s21_recentRS_memLp_pair hdG hjG
  have hMoment' : (∫ ω, ‖(dG ω, jG ω)‖ ^ 2 ∂ν) ≤ M := by
    apply le_trans (integral_mono
      (hpairG.integrable_norm_pow (by norm_num))
      ((hdG.integrable_norm_pow (by norm_num)).add
        (hjG.integrable_norm_pow (by norm_num))) ?_) hMoment
    intro ω
    change (max ‖dG ω‖ ‖jG ω‖) ^ 2 ≤ ‖dG ω‖ ^ 2 + ‖jG ω‖ ^ 2
    rcases le_total ‖dG ω‖ ‖jG ω‖ with h | h
    · rw [max_eq_right h]
      nlinarith [sq_nonneg ‖dG ω‖]
    · rw [max_eq_left h]
      nlinarith [sq_nonneg ‖jG ω‖]
  have hD := fp81s21_recentRS_source_comparison μ ν _ _ hmN hmG
    hKD he hM hη FD' hW hpairN hpairG hMoment'
  have hJ := fp81s21_recentRS_source_comparison μ ν _ _ hmN hmG
    hKJ he hM hη FJ' hW hpairN hpairG hMoment'
  change |(∫ ω, FD.kernel (yN ω) (dN ω) ∂μ) -
    (∫ ω, FD.kernel (yG ω) (dG ω) ∂ν)| ≤ _ at hD
  change |(∫ ω, FJ.kernel (yN ω) (jN ω) ∂μ) -
    (∫ ω, FJ.kernel (yG ω) (jG ω) ∂ν)| ≤ _ at hJ
  have hsign := fp81s21_recentRS_correction_difference
    (∫ ω, FD.kernel (yN ω) (dN ω) ∂μ) (∫ ω, FD.kernel (yG ω) (dG ω) ∂ν)
    (∫ ω, FJ.kernel (yN ω) (jN ω) ∂μ) (∫ ω, FJ.kernel (yG ω) (jG ω) ∂ν)
  nlinarith [hsign, hD, hJ]

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_recentRS_joint_signed_comparison
end
