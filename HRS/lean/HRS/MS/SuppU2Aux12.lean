import HRS.MS.SuppU2Aux11

/-!
# U2 auxiliary 12: part (a) of `far_derivatives`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace HRS.Whole

variable {d : ℕ}

lemma u2_K_measurable (s : ℝ) : Measurable (rieszKernelGrad d s) := by
  unfold rieszKernelGrad gradient
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.measurable.comp
    (measurable_fderiv ℝ _)

lemma u2_integrable_of_coord {f : Euc d → Euc d} (hm : AEStronglyMeasurable f volume)
    (hc : ∀ i, Integrable (fun y => f y i) volume) : Integrable f volume := by
  have hb : Integrable (fun y => ∑ i, |f y i|) volume :=
    integrable_finset_sum _ (fun i _ => (hc i).abs)
  refine hb.mono' hm (Filter.Eventually.of_forall fun y => ?_)
  have hv : f y = ∑ i : Fin d, (f y i) • (EuclideanSpace.single i (1 : ℝ) : Euc d) := by
    have := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr (f y)
    simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using this.symm
  calc ‖f y‖ = ‖∑ i : Fin d, (f y i) • (EuclideanSpace.single i (1 : ℝ) : Euc d)‖ := by
        rw [← hv]
    _ ≤ ∑ i : Fin d, ‖(f y i) • (EuclideanSpace.single i (1 : ℝ) : Euc d)‖ := norm_sum_le _ _
    _ = ∑ i, |f y i| := by simp [norm_smul]

lemma u2_grad_comp (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s ≤ (d : ℝ) - 2) {k : ℕ} {L A : ℝ}
    (hL : (d : ℝ) < L) (hA : 0 ≤ A) {h : Euc d → ℝ} (hdec : U2Dec k L A h) (i : Fin d)
    (x : Euc d) : gradGConvPlain d s h x i = u2Conv (u2_kap d s i) h x := by
  have hh0 : ∀ y, ‖h y‖ ≤ A * u2Wt L y := fun y => by
    simpa using hdec.2 0 (Nat.zero_le _) y
  have hcomp : ∀ i' : Fin d, Integrable (fun y => (h y • rieszKernelGrad d s (x - y)) i') volume := by
    intro i'
    have h1 := u2_conv_integrable (u2_kerFull hd hs0 hsd i').ker hL hdec.1.continuous hA hh0 x
    have h2 := h1.comp_sub_left x
    refine h2.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [sub_sub_cancel, u2_kap, PiLp.smul_apply, smul_eq_mul]
    ring
  have hF : Integrable (fun y => h y • rieszKernelGrad d s (x - y)) volume := by
    refine u2_integrable_of_coord ?_ hcomp
    exact (hdec.1.continuous.aestronglyMeasurable).smul
      ((u2_K_measurable (d := d) s).comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  have := ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) hF
  unfold gradGConvPlain
  have e1 : (∫ y, h y • rieszKernelGrad d s (x - y)) i =
      ∫ y, (h y • rieszKernelGrad d s (x - y)) i := by
    simpa using this.symm
  rw [e1, u2_conv_eq_y]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [u2_kap]

theorem u2_partA (hd : 2 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s ≤ (d : ℝ) - 2) (k : ℕ) (L : ℝ)
    (hL : (d : ℝ) + k + s + 3 < L) :
    ∃ C : ℝ, ∀ h : Euc d → ℝ, ContDiff ℝ k h → weightedSupE k L h < ⊤ →
      ContDiff ℝ k (gradGConvPlain d s h) ∧
        decayNormVecE k (s + 1) (gradGConvPlain d s h) ≤ ENNReal.ofReal C * weightedSupE k L h := by
  have hL' : (d : ℝ) + k + (s + 1) + 2 < L := by linarith
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hdL : (d : ℝ) < L := by linarith
  have hL0 : 0 ≤ L := by linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  choose Ci hCi0 hCi using fun i : Fin d => u2_core (u2_kerFull hd hs0 hsd i) k hL'
  have hC0 : 0 ≤ (∑ i, Ci i) * ((d : ℝ) ^ k * 2 ^ L) :=
    mul_nonneg (Finset.sum_nonneg fun i _ => hCi0 i) (by positivity)
  refine ⟨(∑ i, Ci i) * ((d : ℝ) ^ k * 2 ^ L), fun h hcd hfin => ?_⟩
  set Ar : ℝ := (weightedSupE k L h).toReal with hAr
  have hAr0 : 0 ≤ Ar := ENNReal.toReal_nonneg
  have hwse : weightedSupE k L h = ENNReal.ofReal Ar := (ENNReal.ofReal_toReal hfin.ne).symm
  have hΛ : ∀ j ≤ k, ∀ (I : Fin j → Fin d) (x : Euc d),
      jbracket x ^ L * |partialDeriv I h x| ≤ Ar := by
    intro j hj I x
    have := u2_wse_bound (k := k) (L := L) (h := h) (Λ := Ar) hwse.le j hj I x
    rwa [max_eq_left hAr0] at this
  have hA' : 0 ≤ (d : ℝ) ^ k * 2 ^ L * Ar := by positivity
  have hdec : U2Dec k L ((d : ℝ) ^ k * 2 ^ L * Ar) h :=
    ⟨hcd, fun m hm y => u2_norm_le_of_partial (by omega) hL0 hAr0 hΛ m hm y⟩
  have hfun : ∀ i : Fin d, (fun x => gradGConvPlain d s h x i) = u2Conv (u2_kap d s i) h :=
    fun i => funext (u2_grad_comp hd hs0 hsd hdL hA' hdec i)
  refine ⟨contDiff_euclidean.2 fun i => ?_, ?_⟩
  · rw [hfun i]; exact (hCi i _ h hA' hdec).1
  · unfold decayNormVecE
    refine iSup_le fun i => ?_
    rw [hfun i]
    have hb : (0 : ℝ) ≤ s + 1 := by linarith
    have h1 := u2_decayNormE_le (k := k) hb (F := u2Conv (u2_kap d s i) h)
      (B := Ci i * ((d : ℝ) ^ k * 2 ^ L * Ar)) (mul_nonneg (hCi0 i) hA')
      (fun j hj x => (hCi i _ h hA' hdec).2 j hj x)
    refine h1.trans ?_
    rw [hwse, ← ENNReal.ofReal_mul hC0]
    refine ENNReal.ofReal_le_ofReal ?_
    have hle : Ci i ≤ ∑ i, Ci i :=
      Finset.single_le_sum (f := Ci) (fun i _ => hCi0 i) (Finset.mem_univ i)
    have : (0 : ℝ) ≤ (d : ℝ) ^ k * 2 ^ L * Ar := hA'
    calc Ci i * ((d : ℝ) ^ k * 2 ^ L * Ar) ≤ (∑ i, Ci i) * ((d : ℝ) ^ k * 2 ^ L * Ar) :=
          mul_le_mul_of_nonneg_right hle this
      _ = (∑ i, Ci i) * ((d : ℝ) ^ k * 2 ^ L) * Ar := by ring

end HRS.Whole
