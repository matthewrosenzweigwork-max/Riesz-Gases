import HRS.MC.E213U10L

/-!
# Packet e213u10, part M: the coupling bounds for the drift and covariance functionals

`U10B d L = 𝒳_{r,L} × L²([0,L];E_r)`.  For a probability coupling `π` of two laws on `U10B d L` with `L²` control of the cost
`ξ = ‖x - y‖` (`∫ξ² ≤ s²`) and of `ν = ‖x.2‖` (resp. `‖x.1.1 + mm‖`), the integrals of the drift functional (resp. of the
covariance functionals `x ↦ FJ(x.1, x.1 + mm)` and `y ↦ FJ(y.1,y.1)`) differ by at most the stated multiple of `s`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213U10

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ} {S : PreparedData d} {β₀ m : ℝ}

/-- The pair space `𝒳_{r,L} × L²([0,L];E_r)`. -/
abbrev U10B (d : ℕ) (L : ℝ) : Type := PathSpace d (rLvl d) L × L2Path d (rLvl d) L

/-- The covariance functional composed with the mean shift: `x ↦ FJ (x.1, x.1 + mm)`. -/
def u10_GJ (hE : EdgeworthHyp S β₀ m) (T a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ) (b L : ℝ) (hL : 0 ≤ L)
    (hH : a + T ≤ b + L) (mm : PathSpace d (rLvl d) L) (x : U10B d L) : ℝ :=
  u10_FJ hE T a ha Φ b L hL hH (x.1, x.1 + mm)

section Bounds

variable (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ)
  (hΦ : MemCb 5 Φ) (hcb : cbNorm 5 Φ ≤ 1) (b L : ℝ) (hb : 0 ≤ b) (hL : 0 ≤ L) (hH : a + T ≤ b + L)

include hT hΦ hcb hb in
theorem u10_FD_coupling (CD CY : ℝ) (hCD0 : 0 ≤ CD) (hCY0 : 0 ≤ CY) (hCD : U10_DriftNear hE T a ha b CD)
    (hCY : U10_PredBound hE T a ha CY) (π : Measure (U10B d L × U10B d L)) [IsProbabilityMeasure π]
    (s Mq : ℝ) (hs : 0 ≤ s) (hMq : 0 ≤ Mq)
    (hξ : MemLp (fun z : U10B d L × U10B d L => ‖z.1 - z.2‖) 2 π) (hξs : ∫ z, ‖z.1 - z.2‖ ^ 2 ∂π ≤ s ^ 2)
    (hν : MemLp (fun z : U10B d L × U10B d L => ‖z.1.2‖) 2 π) (hνM : ∫ z, ‖z.1.2‖ ^ 2 ∂π ≤ Mq ^ 2) :
    |∫ x, u10_FD hE T a ha Φ b L hL hH x ∂(π.map Prod.fst) -
        ∫ y, u10_FD hE T a ha Φ b L hL hH y ∂(π.map Prod.snd)| ≤
      CD * Real.sqrt L * ((CY * Mq + 1) * s) := by
  have hcont := u10_FD_cont hE T hT a ha Φ hΦ hcb b L hb hL hH CD CY hCD0 hCY0 hCD hCY
  have hmeas := hcont.measurable
  set κ := CD * Real.sqrt L with hκ
  have hκ0 : 0 ≤ κ := mul_nonneg hCD0 (Real.sqrt_nonneg _)
  have habs : ∀ x : U10B d L, |u10_FD hE T a ha Φ b L hL hH x| ≤ κ * ‖x.2‖ := fun x => by
    have := u10_FD_abs_le hE T hT a ha Φ hΦ hcb b L hL hH CD hCD0 hCD x
    rw [hκ]; linarith
  have hξ0 : ∀ z : U10B d L × U10B d L, 0 ≤ ‖z.1 - z.2‖ := fun z => norm_nonneg _
  have hν0 : ∀ z : U10B d L × U10B d L, 0 ≤ ‖z.1.2‖ := fun z => norm_nonneg _
  have hint1 : Integrable (fun z : U10B d L × U10B d L => ‖z.1.2‖) π := hν.integrable (by norm_num)
  have hintξ : Integrable (fun z : U10B d L × U10B d L => ‖z.1 - z.2‖) π := hξ.integrable (by norm_num)
  have hFi : Integrable (fun z : U10B d L × U10B d L => u10_FD hE T a ha Φ b L hL hH z.1) π := by
    refine Integrable.mono' (hint1.const_mul κ) ((hmeas.comp measurable_fst).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => ?_)
    simpa [Real.norm_eq_abs] using habs z.1
  have hGi : Integrable (fun z : U10B d L × U10B d L => u10_FD hE T a ha Φ b L hL hH z.2) π := by
    refine Integrable.mono' ((hint1.add hintξ).const_mul κ) ((hmeas.comp measurable_snd).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => ?_)
    have h2 : ‖z.2.2‖ ≤ ‖z.1.2‖ + ‖z.1 - z.2‖ := by
      have h3 : ‖z.2.2‖ ≤ ‖z.1.2‖ + ‖z.1.2 - z.2.2‖ := by
        calc ‖z.2.2‖ = ‖z.1.2 - (z.1.2 - z.2.2)‖ := by congr 1; abel
          _ ≤ ‖z.1.2‖ + ‖z.1.2 - z.2.2‖ := norm_sub_le _ _
      have h4 : ‖z.1.2 - z.2.2‖ ≤ ‖z.1 - z.2‖ := by simpa using norm_snd_le (z.1 - z.2)
      linarith
    calc ‖u10_FD hE T a ha Φ b L hL hH z.2‖ = |u10_FD hE T a ha Φ b L hL hH z.2| := Real.norm_eq_abs _
      _ ≤ κ * ‖z.2.2‖ := habs z.2
      _ ≤ κ * (‖z.1.2‖ + ‖z.1 - z.2‖) := mul_le_mul_of_nonneg_left h2 hκ0
  set H : U10B d L × U10B d L → ℝ := fun z => κ * CY * (‖z.1 - z.2‖ * ‖z.1.2‖) + κ * ‖z.1 - z.2‖ with hHdef
  have hprod : Integrable (fun z : U10B d L × U10B d L => ‖z.1 - z.2‖ * ‖z.1.2‖) π := hξ.integrable_mul hν
  have hHi : Integrable H π := (hprod.const_mul (κ * CY)).add (hintξ.const_mul κ)
  have hle : ∀ z : U10B d L × U10B d L, |u10_FD hE T a ha Φ b L hL hH z.1 - u10_FD hE T a ha Φ b L hL hH z.2| ≤ H z := by
    intro z
    refine (u10_FD_lip_core hE T hT a ha Φ hΦ hcb b L hL hH CD CY hCD0 hCY0 hCD hCY z.1 z.2).trans ?_
    have h1 : ‖z.1.1 - z.2.1‖ ≤ ‖z.1 - z.2‖ := by simpa using norm_fst_le (z.1 - z.2)
    have h2 : ‖z.1.2 - z.2.2‖ ≤ ‖z.1 - z.2‖ := by simpa using norm_snd_le (z.1 - z.2)
    have e : CD * CY * Real.sqrt L * ‖z.1.1 - z.2.1‖ * ‖z.1.2‖ = κ * CY * (‖z.1.1 - z.2.1‖ * ‖z.1.2‖) := by
      rw [hκ]; ring
    rw [e, hHdef]
    simp only []
    have hκCY : 0 ≤ κ * CY := mul_nonneg hκ0 hCY0
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (norm_nonneg z.1.2)) hκCY
    have h4 := mul_le_mul_of_nonneg_left h2 hκ0
    have e2 : CD * Real.sqrt L * ‖z.1.2 - z.2.2‖ = κ * ‖z.1.2 - z.2.2‖ := by rw [hκ]
    rw [e2]
    linarith
  refine (u10_coupling_diff π _ _ hmeas hmeas H hFi hGi hHi hle).trans ?_
  have hcs : ∫ z, ‖z.1 - z.2‖ * ‖z.1.2‖ ∂π ≤ s * Mq :=
    u10_cs π _ _ hξ0 hν0 hξ hν s Mq hs hMq hξs hνM
  have hc1 : ∫ z, ‖z.1 - z.2‖ ∂π ≤ s := by
    have := u10_cs π (fun z : U10B d L × U10B d L => ‖z.1 - z.2‖) (fun _ => 1) hξ0 (fun _ => zero_le_one) hξ
      (memLp_const 1) s 1 hs zero_le_one hξs (by simp)
    simpa using this
  show ∫ z, H z ∂π ≤ _
  rw [hHdef]
  simp only []
  rw [integral_add (hprod.const_mul (κ * CY)) (hintξ.const_mul κ), integral_const_mul, integral_const_mul]
  have hκCY : 0 ≤ κ * CY := mul_nonneg hκ0 hCY0
  have := mul_le_mul_of_nonneg_left hcs hκCY
  have h5 := mul_le_mul_of_nonneg_left hc1 hκ0
  calc κ * CY * ∫ z, ‖z.1 - z.2‖ * ‖z.1.2‖ ∂π + κ * ∫ z, ‖z.1 - z.2‖ ∂π ≤ κ * CY * (s * Mq) + κ * s := add_le_add this h5
    _ = κ * ((CY * Mq + 1) * s) := by ring

include hT hΦ hcb hb in
theorem u10_GJ_cont (CJ CY : ℝ) (hCJ0 : 0 ≤ CJ) (hCY0 : 0 ≤ CY) (hJ : U10_JNear hE T a ha b CJ)
    (hCY : U10_PredBound hE T a ha CY) (mm : PathSpace d (rLvl d) L) :
    Continuous (u10_GJ hE T a ha Φ b L hL hH mm) := by
  have h := u10_FJ_cont hE T hT a ha Φ hΦ hcb b L hb hL hH CJ CY hCJ0 hCY0 hJ hCY
  exact h.comp (continuous_fst.prodMk (continuous_fst.add continuous_const))

include hT hΦ hcb hb in
theorem u10_GJ_coupling (CJ CY : ℝ) (hCJ0 : 0 ≤ CJ) (hCY0 : 0 ≤ CY) (hJ : U10_JNear hE T a ha b CJ)
    (hCY : U10_PredBound hE T a ha CY) (mm : PathSpace d (rLvl d) L)
    (π : Measure (U10B d L × U10B d L)) [IsProbabilityMeasure π]
    (s Mf : ℝ) (hs : 0 ≤ s) (hMf : 0 ≤ Mf)
    (hξ : MemLp (fun z : U10B d L × U10B d L => ‖z.1 - z.2‖) 2 π) (hξs : ∫ z, ‖z.1 - z.2‖ ^ 2 ∂π ≤ s ^ 2)
    (hν : MemLp (fun z : U10B d L × U10B d L => ‖z.1.1 + mm‖) 2 π)
    (hνM : ∫ z, ‖z.1.1 + mm‖ ^ 2 ∂π ≤ Mf ^ 2) :
    |∫ x, u10_GJ hE T a ha Φ b L hL hH mm x ∂(π.map Prod.fst) -
        ∫ y, u10_GJ hE T a ha Φ b L hL hH 0 y ∂(π.map Prod.snd)| ≤
      CJ * L * ((CY * Mf + 1) * s + ‖mm‖) := by
  have hmeas1 := (u10_GJ_cont hE T hT a ha Φ hΦ hcb b L hb hL hH CJ CY hCJ0 hCY0 hJ hCY mm).measurable
  have hmeas2 := (u10_GJ_cont hE T hT a ha Φ hΦ hcb b L hb hL hH CJ CY hCJ0 hCY0 hJ hCY 0).measurable
  set lam := CJ * L with hlam
  have hlam0 : 0 ≤ lam := mul_nonneg hCJ0 hL
  have habs : ∀ (mm' : PathSpace d (rLvl d) L) (x : U10B d L),
      |u10_GJ hE T a ha Φ b L hL hH mm' x| ≤ lam * ‖x.1 + mm'‖ := fun mm' x =>
    u10_FJ_abs_le hE T hT a ha Φ hΦ hcb b L hb hL hH CJ hCJ0 hJ (x.1, x.1 + mm')
  have hξ0 : ∀ z : U10B d L × U10B d L, 0 ≤ ‖z.1 - z.2‖ := fun z => norm_nonneg _
  have hν0 : ∀ z : U10B d L × U10B d L, 0 ≤ ‖z.1.1 + mm‖ := fun z => norm_nonneg _
  have hint1 : Integrable (fun z : U10B d L × U10B d L => ‖z.1.1 + mm‖) π := hν.integrable (by norm_num)
  have hintξ : Integrable (fun z : U10B d L × U10B d L => ‖z.1 - z.2‖) π := hξ.integrable (by norm_num)
  have hFi : Integrable (fun z : U10B d L × U10B d L => u10_GJ hE T a ha Φ b L hL hH mm z.1) π := by
    refine Integrable.mono' (hint1.const_mul lam) ((hmeas1.comp measurable_fst).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => ?_)
    simpa [Real.norm_eq_abs] using habs mm z.1
  have hGi : Integrable (fun z : U10B d L × U10B d L => u10_GJ hE T a ha Φ b L hL hH 0 z.2) π := by
    refine Integrable.mono' (((hint1.add hintξ).add (integrable_const ‖mm‖)).const_mul lam)
      ((hmeas2.comp measurable_snd).aestronglyMeasurable) (Filter.Eventually.of_forall fun z => ?_)
    have h2 : ‖z.2.1 + 0‖ ≤ ‖z.1.1 + mm‖ + ‖z.1 - z.2‖ + ‖mm‖ := by
      have h4 : ‖z.1.1 - z.2.1‖ ≤ ‖z.1 - z.2‖ := by simpa using norm_fst_le (z.1 - z.2)
      have h3 : ‖z.2.1 + 0‖ ≤ ‖z.1.1 + mm‖ + ‖z.1.1 - z.2.1‖ + ‖mm‖ := by
        calc ‖z.2.1 + 0‖ = ‖(z.1.1 + mm) - (z.1.1 - z.2.1) - mm‖ := by congr 1; abel
          _ ≤ ‖(z.1.1 + mm) - (z.1.1 - z.2.1)‖ + ‖mm‖ := norm_sub_le _ _
          _ ≤ ‖z.1.1 + mm‖ + ‖z.1.1 - z.2.1‖ + ‖mm‖ := by
              have := norm_sub_le (z.1.1 + mm) (z.1.1 - z.2.1)
              linarith
      linarith
    calc ‖u10_GJ hE T a ha Φ b L hL hH 0 z.2‖ = |u10_GJ hE T a ha Φ b L hL hH 0 z.2| := Real.norm_eq_abs _
      _ ≤ lam * ‖z.2.1 + 0‖ := habs 0 z.2
      _ ≤ lam * (‖z.1.1 + mm‖ + ‖z.1 - z.2‖ + ‖mm‖) := mul_le_mul_of_nonneg_left h2 hlam0
  have hprod : Integrable (fun z : U10B d L × U10B d L => ‖z.1 - z.2‖ * ‖z.1.1 + mm‖) π :=
    hξ.integrable_mul hν
  have hHi : Integrable (fun z : U10B d L × U10B d L =>
      lam * (CY * (‖z.1 - z.2‖ * ‖z.1.1 + mm‖) + ‖z.1 - z.2‖ + ‖mm‖)) π :=
    ((((hprod.const_mul CY).add hintξ).add (integrable_const ‖mm‖))).const_mul lam
  have hle : ∀ z : U10B d L × U10B d L, |u10_GJ hE T a ha Φ b L hL hH mm z.1 -
      u10_GJ hE T a ha Φ b L hL hH 0 z.2| ≤
      lam * (CY * (‖z.1 - z.2‖ * ‖z.1.1 + mm‖) + ‖z.1 - z.2‖ + ‖mm‖) := by
    intro z
    have hlip := u10_FJ_lip_core hE T hT a ha Φ hΦ hcb b L hb hL hH CJ CY hCJ0 hCY0 hJ hCY
      (z.1.1, z.1.1 + mm) (z.2.1, z.2.1 + 0)
    have h1 : ‖z.1.1 - z.2.1‖ ≤ ‖z.1 - z.2‖ := by simpa using norm_fst_le (z.1 - z.2)
    have h2 : ‖z.1.1 + mm - (z.2.1 + 0)‖ ≤ ‖z.1 - z.2‖ + ‖mm‖ := by
      calc ‖z.1.1 + mm - (z.2.1 + 0)‖ = ‖(z.1.1 - z.2.1) + mm‖ := by congr 1; abel
        _ ≤ ‖z.1.1 - z.2.1‖ + ‖mm‖ := norm_add_le _ _
        _ ≤ ‖z.1 - z.2‖ + ‖mm‖ := by linarith
    have h3 : CY * ‖z.1.1 - z.2.1‖ * ‖z.1.1 + mm‖ ≤ CY * (‖z.1 - z.2‖ * ‖z.1.1 + mm‖) := by
      calc CY * ‖z.1.1 - z.2.1‖ * ‖z.1.1 + mm‖ = CY * (‖z.1.1 - z.2.1‖ * ‖z.1.1 + mm‖) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)) hCY0
    have h4 : CJ * L * (CY * ‖z.1.1 - z.2.1‖ * ‖z.1.1 + mm‖ + ‖z.1.1 + mm - (z.2.1 + 0)‖) ≤
        lam * (CY * (‖z.1 - z.2‖ * ‖z.1.1 + mm‖) + ‖z.1 - z.2‖ + ‖mm‖) := by
      rw [hlam]
      refine mul_le_mul_of_nonneg_left ?_ hlam0
      linarith
    exact le_trans hlip h4
  refine (u10_coupling_diff π _ _ hmeas1 hmeas2 _ hFi hGi hHi hle).trans ?_
  have hcs : ∫ z, ‖z.1 - z.2‖ * ‖z.1.1 + mm‖ ∂π ≤ s * Mf :=
    u10_cs π _ _ hξ0 hν0 hξ hν s Mf hs hMf hξs hνM
  have hc1 : ∫ z, ‖z.1 - z.2‖ ∂π ≤ s := by
    have := u10_cs π (fun z : U10B d L × U10B d L => ‖z.1 - z.2‖) (fun _ => 1) hξ0 (fun _ => zero_le_one) hξ
      (memLp_const 1) s 1 hs zero_le_one hξs (by simp)
    simpa using this
  have hA : Integrable (fun z : U10B d L × U10B d L => CY * (‖z.1 - z.2‖ * ‖z.1.1 + mm‖)) π :=
    hprod.const_mul CY
  have hB : Integrable (fun z : U10B d L × U10B d L => CY * (‖z.1 - z.2‖ * ‖z.1.1 + mm‖) + ‖z.1 - z.2‖) π :=
    hA.add hintξ
  have hI : ∫ z : U10B d L × U10B d L, (CY * (‖z.1 - z.2‖ * ‖z.1.1 + mm‖) + ‖z.1 - z.2‖ + ‖mm‖) ∂π =
      CY * ∫ z : U10B d L × U10B d L, ‖z.1 - z.2‖ * ‖z.1.1 + mm‖ ∂π + ∫ z : U10B d L × U10B d L, ‖z.1 - z.2‖ ∂π +
        ‖mm‖ := by
    rw [integral_add hB (integrable_const ‖mm‖), integral_add hA hintξ, integral_const_mul]
    simp
  rw [integral_const_mul, hI]
  have := mul_le_mul_of_nonneg_left hcs hCY0
  rw [hlam]
  refine mul_le_mul_of_nonneg_left ?_ hlam0
  nlinarith

end Bounds

end HRS.MC.E213U10

end
