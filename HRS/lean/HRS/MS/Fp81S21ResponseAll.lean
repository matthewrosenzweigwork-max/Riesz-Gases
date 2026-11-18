import HRS.MS.Fp81S21ResponseWindowBound
import HRS.MS.Fp81S21RespIid2
import HRS.MS.Fp81S21QwinUniform
import HRS.MS.Fp81S21GaussFeature

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.S21 HRS.MS.S21E

private theorem fp81s21_responseWindow_kappa_of_bound
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    [IsProbabilityMeasure (r26t3_mu R 0)]
    (b K : ℝ)
    (hbound : ∀ x : Euc p.d, ‖responseWindow R b x‖ ≤ K)
    (hmeas : AEStronglyMeasurable (responseWindow R b)
      (r26t3_mu R 0))
    (hcube : Integrable (fun x : Euc p.d => ‖responseWindow R b x‖ ^ 3)
      (r26t3_mu R 0)) :
    initialKappa R b ∈ projTensor (Window p) 3 ∧
      ‖initialKappa R b‖ ≤ K ^ 3 := by
  have hproduct : Integrable
      (fun x : Euc p.d => ‖responseWindow R b x‖ *
        ‖responseWindow R b x‖ * ‖responseWindow R b x‖)
      (r26t3_mu R 0) := by
    apply hcube.congr
    filter_upwards with x
    ring
  have hmem : initialKappa R b ∈ projTensor (Window p) 3 := by
    change s21eKappa0 (r26t3_mu R 0) (responseWindow R b) ∈ _
    exact s21e_kappa0_mem (r26t3_mu R 0) hmeas hproduct
  have hnorm : ‖initialKappa R b‖ ≤
      ∫ x, ‖responseWindow R b x‖ * ‖responseWindow R b x‖ *
        ‖responseWindow R b x‖ ∂(r26t3_mu R 0) := by
    change ‖s21eKappa0 (r26t3_mu R 0) (responseWindow R b)‖ ≤ _
    exact s21e_kappa0_norm_le (r26t3_mu R 0) hmeas hproduct
  have hpoint : ∀ x : Euc p.d,
      ‖responseWindow R b x‖ * ‖responseWindow R b x‖ *
        ‖responseWindow R b x‖ ≤ K ^ 3 := by
    intro x
    calc
      ‖responseWindow R b x‖ * ‖responseWindow R b x‖ *
          ‖responseWindow R b x‖ = ‖responseWindow R b x‖ ^ 3 := by ring
      _ ≤ K ^ 3 := pow_le_pow_left₀ (norm_nonneg _) (hbound x) 3
  have hint :
      (∫ x, ‖responseWindow R b x‖ * ‖responseWindow R b x‖ *
        ‖responseWindow R b x‖ ∂(r26t3_mu R 0)) ≤ K ^ 3 := by
    calc
      (∫ x, ‖responseWindow R b x‖ * ‖responseWindow R b x‖ *
          ‖responseWindow R b x‖ ∂(r26t3_mu R 0)) ≤
          ∫ _x : Euc p.d, K ^ 3 ∂(r26t3_mu R 0) :=
        integral_mono hproduct (integrable_const _) hpoint
      _ = K ^ 3 := by simp
  exact ⟨hmem, hnorm.trans hint⟩

private theorem fp81s21_responseWindow_positive_data (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        0 < p.γ → ∃ K : ℝ, 0 ≤ K ∧ ∀ b : ℝ, 0 ≤ b →
          AEStronglyMeasurable (responseWindow R b) (r26t3_mu R 0) ∧
          Integrable (fun x => ‖responseWindow R b x‖ ^ 3)
            (r26t3_mu R 0) ∧
          (∀ x, ‖responseWindow R b x‖ ≤ K) := by
  obtain ⟨δb, hb0, hbhalf, hbound⟩ :=
    fp81s21_responseWindow_uniform_bound p
  obtain ⟨δi, hi0, -, hintegrable⟩ :=
    fp81s21_responseWindow_cubic_integrable p
  refine ⟨min δb δi, lt_min hb0 hi0, (min_le_left _ _).trans hbhalf,
    fun δ hδ hδle R hγ => ?_⟩
  have hδb : δ ≤ δb := hδle.trans (min_le_left _ _)
  have hδi : δ ≤ δi := hδle.trans (min_le_right _ _)
  obtain ⟨K, hK, hKbound⟩ := hbound δ hδ hδb R hγ
  refine ⟨K, hK, fun b hb => ?_⟩
  obtain ⟨hmeas, hcube⟩ := hintegrable δ hδ hδi R hγ b hb
  exact ⟨hmeas, hcube, fun x => hKbound b hb x⟩

private theorem fp81s21_responseWindow_zero_data (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        p.γ = 0 → ∃ K : ℝ, 0 ≤ K ∧ ∀ b : ℝ, 0 ≤ b →
          AEStronglyMeasurable (responseWindow R b) (r26t3_mu R 0) ∧
          Integrable (fun x => ‖responseWindow R b x‖ ^ 3)
            (r26t3_mu R 0) ∧
          (∀ x, ‖responseWindow R b x‖ ≤ K) := by
  obtain ⟨δf, hf0, hffull, hfeature⟩ :=
    fp81s21_qwin_featureSum_uniform p
  obtain ⟨δq, hq0, hqhalf, hqwin⟩ := fp81s21_qwin_uniform p
  obtain ⟨δp, hp0, hphalf, hpath⟩ := fp81s21_respIid_path p
  obtain ⟨δc, hc0, -, hcontinuous⟩ :=
    fp81s21_respIid_responseWindow_continuous p
  let δ0 := min δf (min δq (min δp δc))
  have hδ0 : 0 < δ0 := by
    dsimp [δ0]
    exact lt_min hf0 (lt_min hq0 (lt_min hp0 hc0))
  have hδhalf : δ0 ≤ 1 / 2 := by
    dsimp [δ0]
    exact (min_le_left _ _).trans hffull
  refine ⟨δ0, hδ0, hδhalf, fun δ hδ hδle R hγ0 => ?_⟩
  have hδf : δ ≤ δf := hδle.trans (min_le_left _ _)
  have hδq : δ ≤ δq := hδle.trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have hδp : δ ≤ δp := hδle.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδc : δ ≤ δc := hδle.trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hδhalf' : δ ≤ 1 / 2 := hδle.trans hδhalf
  letI : IsProbabilityMeasure (r26t3_mu R 0) :=
    fp81s21_initialMeasure_isProbability p R
  obtain ⟨Cf, hCf, hfeatureBound⟩ := hfeature δ hδ hδf R
  obtain ⟨_, _, hqFamily⟩ := hqwin δ hδ hδq R
  let Φ := s21gPhi (r26t3_feature_enum p.d) p.hT
    ((wholeSpaceIndex p.d : ℕ) : ℝ)
  let B := Cf * (∑' j : ℕ, r26t3_feature_weight p.d j)
  let K := ‖Φ‖ * (2 * B)
  have hweight : ∀ j : ℕ, 0 ≤ r26t3_feature_weight p.d j := by
    intro j
    rw [fp81s21_qwin_feature_weight_eq p j]
    exact mul_nonneg (by positivity)
      (HRS.MS.R2WinOrb.s103_b_nonneg (r26t3_feature_enum p.d j).2)
  have hweightSum : 0 ≤ ∑' j : ℕ, r26t3_feature_weight p.d j :=
    tsum_nonneg hweight
  have hB : 0 ≤ B := mul_nonneg hCf hweightSum
  have hK : 0 ≤ K := mul_nonneg (norm_nonneg Φ)
    (mul_nonneg (by norm_num) hB)
  have hwindowBound : ∀ b : ℝ, 0 ≤ b → ∀ x : Euc p.d,
      ‖responseWindow R b x‖ ≤ K := by
    intro b hb x
    let v := fp81s21_initial_ellv R (r26t3_qwin R b) x
    have hvec := fp81s21_respIid_vector_bounds hδ hδhalf' R hγ0 b hb x
      (hq := (hqFamily b hb).1)
    have hsyn : Φ v = responseWindow R b x := by
      simpa [Φ, v] using hpath δ hδ hδp R hγ0 b hb x
    calc
      ‖responseWindow R b x‖ = ‖Φ v‖ := congrArg norm hsyn.symm
      _ ≤ ‖Φ‖ * ‖v‖ := Φ.le_opNorm v
      _ ≤ ‖Φ‖ * (2 * featureSum (r26t3_J p.d) (r26t3_qwin R b)) :=
        mul_le_mul_of_nonneg_left hvec.2.2 (norm_nonneg Φ)
      _ ≤ ‖Φ‖ * (2 * B) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_left (hfeatureBound b hb) (by norm_num)
        · exact norm_nonneg Φ
      _ = K := rfl
  have hcontinuous' : ∀ b : ℝ, 0 ≤ b →
      Continuous (fun x : Euc p.d => responseWindow R b x) :=
    hcontinuous δ hδ hδc R hγ0
  have hcube : ∀ b : ℝ, 0 ≤ b →
      Integrable (fun x : Euc p.d => ‖responseWindow R b x‖ ^ 3)
        (r26t3_mu R 0) := by
    intro b hb
    have hcubeMeas : AEStronglyMeasurable
        (fun x : Euc p.d => ‖responseWindow R b x‖ ^ 3) (r26t3_mu R 0) :=
      ((hcontinuous' b hb).norm.pow 3).aestronglyMeasurable
    refine Integrable.of_bound hcubeMeas (K ^ 3)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) 3)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hwindowBound b hb x) 3
  refine ⟨K, hK, fun b hb => ?_⟩
  exact ⟨(hcontinuous' b hb).aestronglyMeasurable, hcube b hb,
    hwindowBound b hb⟩

theorem fp81s21_responseWindow_all_strengths (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        letI := fp81s21_initialMeasure_isProbability p R
        ∃ K : ℝ, 0 ≤ K ∧ ∀ b : ℝ, 0 ≤ b →
          AEStronglyMeasurable (responseWindow R b) (r26t3_mu R 0) ∧
          Integrable (fun x => ‖responseWindow R b x‖ ^ 3)
            (r26t3_mu R 0) ∧
          (∀ x, ‖responseWindow R b x‖ ≤ K) ∧
          initialKappa R b ∈ projTensor (Window p) 3 ∧
          ‖initialKappa R b‖ ≤ K ^ 3 := by
  obtain ⟨δp, hp0, hphalf, hpositive⟩ :=
    fp81s21_responseWindow_positive_data p
  obtain ⟨δz, hz0, hzhHalf, hzero⟩ :=
    fp81s21_responseWindow_zero_data p
  refine ⟨min δp δz, lt_min hp0 hz0,
    (min_le_left _ _).trans hphalf, fun δ hδ hδle R => ?_⟩
  have hδp : δ ≤ δp := hδle.trans (min_le_left _ _)
  have hδz : δ ≤ δz := hδle.trans (min_le_right _ _)
  letI : IsProbabilityMeasure (r26t3_mu R 0) :=
    fp81s21_initialMeasure_isProbability p R
  change ∃ K : ℝ, 0 ≤ K ∧ ∀ b : ℝ, 0 ≤ b →
    AEStronglyMeasurable (responseWindow R b) (r26t3_mu R 0) ∧
    Integrable (fun x => ‖responseWindow R b x‖ ^ 3) (r26t3_mu R 0) ∧
    (∀ x, ‖responseWindow R b x‖ ≤ K) ∧
    initialKappa R b ∈ projTensor (Window p) 3 ∧
    ‖initialKappa R b‖ ≤ K ^ 3
  by_cases hγ : 0 < p.γ
  · obtain ⟨K, hK, hdata⟩ := hpositive δ hδ hδp R hγ
    refine ⟨K, hK, fun b hb => ?_⟩
    obtain ⟨hmeas, hcube, hbound⟩ := hdata b hb
    have hk := fp81s21_responseWindow_kappa_of_bound p R b K
      hbound hmeas hcube
    exact ⟨hmeas, hcube, hbound, hk.1, hk.2⟩
  · have hγ0 : p.γ = 0 := le_antisymm (le_of_not_gt hγ) p.hγ
    obtain ⟨K, hK, hdata⟩ := hzero δ hδ hδz R hγ0
    refine ⟨K, hK, fun b hb => ?_⟩
    obtain ⟨hmeas, hcube, hbound⟩ := hdata b hb
    have hk := fp81s21_responseWindow_kappa_of_bound p R b K
      hbound hmeas hcube
    exact ⟨hmeas, hcube, hbound, hk.1, hk.2⟩

#print axioms HRS.Fp81.S21.fp81s21_responseWindow_all_strengths

end HRS.Fp81.S21

end
