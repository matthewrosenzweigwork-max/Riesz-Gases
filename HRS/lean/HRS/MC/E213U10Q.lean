import HRS.MC.E213U10P

/-!
# Packet e213u10, part Q: law-level bounds

* `u10_eps_coupling`: from a coupling bound `≤ K s + K0` valid for every probability coupling with `L²` cost `≤ s`, the
  Wasserstein bound `≤ K W_2 + K0`;
* `u10_FD_law`, `u10_GJ_law`: `|∫ FD dμ₁ - ∫ FD dμ₂| ≤ CD √L ((CY Mq + 1) W_2)` and the covariance analogue;
* `u10_FD_crude`, `u10_GJ_crude`: the absolute bounds `|∫ FD dμ| ≤ CD √L Mq`, `|∫ GJ dμ| ≤ CJ L Mf`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213U10

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ} {S : PreparedData d} {β₀ m : ℝ}

section Eps

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B]
  [SecondCountableTopology B]

theorem u10_eps_coupling (μ₁ μ₂ : Measure B) [IsProbabilityMeasure μ₁] (F G : B → ℝ) (K K0 : ℝ) (hK : 0 ≤ K)
    (hW : HRS.wassersteinE 2 μ₁ μ₂ ≠ ⊤)
    (h : ∀ π : Measure (B × B), IsProbabilityMeasure π → HRS.IsCoupling π μ₁ μ₂ → ∀ s : ℝ, 0 ≤ s →
      MemLp (fun z : B × B => ‖z.1 - z.2‖) 2 π → ∫ z, ‖z.1 - z.2‖ ^ 2 ∂π ≤ s ^ 2 →
      |∫ x, F x ∂μ₁ - ∫ y, G y ∂μ₂| ≤ K * s + K0) :
    |∫ x, F x ∂μ₁ - ∫ y, G y ∂μ₂| ≤ K * (HRS.wassersteinE 2 μ₁ μ₂).toReal + K0 := by
  set Wd := HRS.wassersteinE 2 μ₁ μ₂ with hWd
  have hW0 : 0 ≤ Wd.toReal := ENNReal.toReal_nonneg
  refine le_of_forall_pos_le_add fun ε hε => ?_
  set δ := ε / (K + 1) with hδ
  have hδ0 : 0 < δ := by rw [hδ]; positivity
  have hlt : Wd < ENNReal.ofReal (Wd.toReal + δ) := by
    rw [ENNReal.ofReal_add hW0 hδ0.le, ENNReal.ofReal_toReal hW]
    exact ENNReal.lt_add_right hW (ENNReal.ofReal_pos.2 hδ0).ne'
  obtain ⟨π, hπ, hcost⟩ := u10_exists_coupling μ₁ μ₂ _ hlt
  have hprob : IsProbabilityMeasure π := by
    refine ⟨?_⟩
    have := congrArg (fun μ => μ Set.univ) hπ.1
    simp only [Measure.map_apply measurable_fst MeasurableSet.univ, Set.preimage_univ, measure_univ] at this
    exact this
  obtain ⟨hm, hI⟩ := u10_cost_memLp π (Wd.toReal + δ) (add_nonneg hW0 hδ0.le) hcost.le
  have h1 := h π hprob hπ _ (add_nonneg hW0 hδ0.le) hm hI
  have e : K * δ ≤ ε := by
    rw [hδ, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith

end Eps

section Bounds

variable (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ)
  (hΦ : MemCb 5 Φ) (hcb : cbNorm 5 Φ ≤ 1) (b L : ℝ) (hb : 0 ≤ b) (hL : 0 ≤ L) (hH : a + T ≤ b + L)

include hT hΦ hcb hb in
theorem u10_FD_law (CD CY : ℝ) (hCD0 : 0 ≤ CD) (hCY0 : 0 ≤ CY) (hCD : U10_DriftNear hE T a ha b CD)
    (hCY : U10_PredBound hE T a ha CY) (μ₁ μ₂ : Measure (U10B d L)) [IsProbabilityMeasure μ₁]
    [IsProbabilityMeasure μ₂] (Mq : ℝ) (hMq : 0 ≤ Mq)
    (hν : MemLp (fun x : U10B d L => ‖x.2‖) 2 μ₁) (hνM : ∫ x, ‖x.2‖ ^ 2 ∂μ₁ ≤ Mq ^ 2)
    (hW : HRS.wassersteinE 2 μ₁ μ₂ ≠ ⊤) :
    |∫ x, u10_FD hE T a ha Φ b L hL hH x ∂μ₁ - ∫ y, u10_FD hE T a ha Φ b L hL hH y ∂μ₂| ≤
      CD * Real.sqrt L * ((CY * Mq + 1) * (HRS.wassersteinE 2 μ₁ μ₂).toReal) := by
  have hK : 0 ≤ CD * Real.sqrt L * (CY * Mq + 1) := by positivity
  have key := u10_eps_coupling μ₁ μ₂ (u10_FD hE T a ha Φ b L hL hH) (u10_FD hE T a ha Φ b L hL hH)
    (CD * Real.sqrt L * (CY * Mq + 1)) 0 hK hW (fun π hprob hcoup s hs hm hI => by
      haveI := hprob
      have hν' : MemLp (fun z : U10B d L × U10B d L => ‖z.1.2‖) 2 π := by
        have h0 : MemLp (fun x : U10B d L => ‖x.2‖) 2 (π.map Prod.fst) := by rw [hcoup.1]; exact hν
        exact (memLp_map_measure_iff continuous_snd.norm.aestronglyMeasurable
          measurable_fst.aemeasurable).1 h0
      have hνM' : ∫ z, ‖z.1.2‖ ^ 2 ∂π ≤ Mq ^ 2 := by
        have := integral_map (μ := π) measurable_fst.aemeasurable
          (f := fun x : U10B d L => ‖x.2‖ ^ 2) (continuous_snd.norm.pow 2).aestronglyMeasurable
        rw [hcoup.1] at this
        exact (le_of_eq this.symm).trans hνM
      have h1 := u10_FD_coupling hE T hT a ha Φ hΦ hcb b L hb hL hH CD CY hCD0 hCY0 hCD hCY π s Mq hs hMq
        hm hI hν' hνM'
      rw [hcoup.1, hcoup.2] at h1
      have e : CD * Real.sqrt L * ((CY * Mq + 1) * s) = CD * Real.sqrt L * (CY * Mq + 1) * s + 0 := by ring
      rw [e] at h1
      exact h1)
  have e2 : CD * Real.sqrt L * (CY * Mq + 1) * (HRS.wassersteinE 2 μ₁ μ₂).toReal + 0 =
      CD * Real.sqrt L * ((CY * Mq + 1) * (HRS.wassersteinE 2 μ₁ μ₂).toReal) := by ring
  rw [e2] at key
  exact key

include hT hΦ hcb hb in
theorem u10_GJ_law (CJ CY : ℝ) (hCJ0 : 0 ≤ CJ) (hCY0 : 0 ≤ CY) (hJ : U10_JNear hE T a ha b CJ)
    (hCY : U10_PredBound hE T a ha CY) (mm : PathSpace d (rLvl d) L) (μ₁ μ₂ : Measure (U10B d L))
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] (Mf : ℝ) (hMf : 0 ≤ Mf)
    (hν : MemLp (fun x : U10B d L => ‖x.1 + mm‖) 2 μ₁) (hνM : ∫ x, ‖x.1 + mm‖ ^ 2 ∂μ₁ ≤ Mf ^ 2)
    (hW : HRS.wassersteinE 2 μ₁ μ₂ ≠ ⊤) :
    |∫ x, u10_GJ hE T a ha Φ b L hL hH mm x ∂μ₁ - ∫ y, u10_GJ hE T a ha Φ b L hL hH 0 y ∂μ₂| ≤
      CJ * L * ((CY * Mf + 1) * (HRS.wassersteinE 2 μ₁ μ₂).toReal + ‖mm‖) := by
  have hK : 0 ≤ CJ * L * (CY * Mf + 1) := by positivity
  have key := u10_eps_coupling μ₁ μ₂ (u10_GJ hE T a ha Φ b L hL hH mm) (u10_GJ hE T a ha Φ b L hL hH 0)
    (CJ * L * (CY * Mf + 1)) (CJ * L * ‖mm‖) hK hW (fun π hprob hcoup s hs hm hI => by
      haveI := hprob
      have hcm : Continuous fun x : U10B d L => ‖x.1 + mm‖ := (continuous_fst.add continuous_const).norm
      have hν' : MemLp (fun z : U10B d L × U10B d L => ‖z.1.1 + mm‖) 2 π := by
        have h0 : MemLp (fun x : U10B d L => ‖x.1 + mm‖) 2 (π.map Prod.fst) := by rw [hcoup.1]; exact hν
        exact (memLp_map_measure_iff hcm.aestronglyMeasurable measurable_fst.aemeasurable).1 h0
      have hνM' : ∫ z, ‖z.1.1 + mm‖ ^ 2 ∂π ≤ Mf ^ 2 := by
        have := integral_map (μ := π) measurable_fst.aemeasurable
          (f := fun x : U10B d L => ‖x.1 + mm‖ ^ 2) (hcm.pow 2).aestronglyMeasurable
        rw [hcoup.1] at this
        exact (le_of_eq this.symm).trans hνM
      have h1 := u10_GJ_coupling hE T hT a ha Φ hΦ hcb b L hb hL hH CJ CY hCJ0 hCY0 hJ hCY mm π s Mf hs hMf
        hm hI hν' hνM'
      rw [hcoup.1, hcoup.2] at h1
      have e : CJ * L * ((CY * Mf + 1) * s + ‖mm‖) = CJ * L * (CY * Mf + 1) * s + CJ * L * ‖mm‖ := by ring
      rw [e] at h1
      exact h1)
  have e2 : CJ * L * (CY * Mf + 1) * (HRS.wassersteinE 2 μ₁ μ₂).toReal + CJ * L * ‖mm‖ =
      CJ * L * ((CY * Mf + 1) * (HRS.wassersteinE 2 μ₁ μ₂).toReal + ‖mm‖) := by ring
  rw [e2] at key
  exact key

include hT hΦ hcb in
theorem u10_FD_crude (CD : ℝ) (hCD0 : 0 ≤ CD) (hCD : U10_DriftNear hE T a ha b CD) (CY : ℝ) (hCY0 : 0 ≤ CY)
    (hCY : U10_PredBound hE T a ha CY) (hb : 0 ≤ b) (μ : Measure (U10B d L)) [IsProbabilityMeasure μ]
    (Mq : ℝ) (hMq : 0 ≤ Mq) (hν : MemLp (fun x : U10B d L => ‖x.2‖) 2 μ) (hνM : ∫ x, ‖x.2‖ ^ 2 ∂μ ≤ Mq ^ 2) :
    |∫ x, u10_FD hE T a ha Φ b L hL hH x ∂μ| ≤ CD * Real.sqrt L * Mq :=
  u10_abs_integral_le μ _ (fun x : U10B d L => ‖x.2‖)
    (u10_FD_cont hE T hT a ha Φ hΦ hcb b L hb hL hH CD CY hCD0 hCY0 hCD hCY).measurable
    continuous_snd.norm.measurable (fun x => norm_nonneg _) (CD * Real.sqrt L) Mq (by positivity) hMq
    (fun x => u10_FD_abs_le hE T hT a ha Φ hΦ hcb b L hL hH CD hCD0 hCD x) hν hνM

include hT hΦ hcb in
theorem u10_GJ_crude (CJ : ℝ) (hCJ0 : 0 ≤ CJ) (hJ : U10_JNear hE T a ha b CJ) (CY : ℝ) (hCY0 : 0 ≤ CY)
    (hCY : U10_PredBound hE T a ha CY) (hb : 0 ≤ b) (mm : PathSpace d (rLvl d) L) (μ : Measure (U10B d L))
    [IsProbabilityMeasure μ] (Mf : ℝ) (hMf : 0 ≤ Mf) (hν : MemLp (fun x : U10B d L => ‖x.1 + mm‖) 2 μ)
    (hνM : ∫ x, ‖x.1 + mm‖ ^ 2 ∂μ ≤ Mf ^ 2) :
    |∫ x, u10_GJ hE T a ha Φ b L hL hH mm x ∂μ| ≤ CJ * L * Mf :=
  u10_abs_integral_le μ _ (fun x : U10B d L => ‖x.1 + mm‖)
    (u10_GJ_cont hE T hT a ha Φ hΦ hcb b L hb hL hH CJ CY hCJ0 hCY0 hJ hCY mm).measurable
    (continuous_fst.add continuous_const).norm.measurable (fun x => norm_nonneg _) (CJ * L) Mf
    (mul_nonneg hCJ0 hL) hMf
    (fun x => u10_FJ_abs_le hE T hT a ha Φ hΦ hcb b L hb hL hH CJ hCJ0 hJ (x.1, x.1 + mm)) hν hνM

end Bounds

end HRS.MC.E213U10

end
