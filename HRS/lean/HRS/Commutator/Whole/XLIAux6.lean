import HRS.Commutator.Whole.XLIAux5

/-!
# X-LI part 6: weighted Littlewood–Paley inequality and the square function bound for `p > 2`
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- Peetre-type shift for the majorant kernel -/
lemma Phi_shift (j : ℤ) {x y : 𝔼} (hxy : ‖x - y‖ < (2 : ℝ) ^ (-j)) (u : 𝔼) :
    Phi j (x - u) ≤ 2 ^ (d + 1) * Phi j (y - u) := by
  set s : ℝ := (2 : ℝ) ^ j with hs
  have hs0 : 0 < s := zpow_pos (by norm_num) j
  have hsxy : s * ‖x - y‖ < 1 := by
    have h := mul_lt_mul_of_pos_left hxy hs0
    rwa [show (2 : ℝ) ^ (-j) = s⁻¹ by rw [hs, zpow_neg], mul_inv_cancel₀ hs0.ne'] at h
  have h1 : 1 + s * ‖y - u‖ ≤ 2 * (1 + s * ‖x - u‖) := by
    have : ‖y - u‖ ≤ ‖x - u‖ + ‖x - y‖ := by
      calc ‖y - u‖ = ‖(x - u) - (x - y)‖ := by congr 1; abel
        _ ≤ ‖x - u‖ + ‖x - y‖ := norm_sub_le _ _
    nlinarith [norm_nonneg (x - u), mul_nonneg hs0.le (norm_nonneg (x - u))]
  have h2 : (1 + s * ‖y - u‖) ^ (d + 1) ≤ 2 ^ (d + 1) * (1 + s * ‖x - u‖) ^ (d + 1) := by
    calc (1 + s * ‖y - u‖) ^ (d + 1) ≤ (2 * (1 + s * ‖x - u‖)) ^ (d + 1) :=
          pow_le_pow_left₀ (by positivity) h1 _
      _ = _ := mul_pow _ _ _
  have hp : 0 < (1 + s * ‖x - u‖) ^ (d + 1) := by positivity
  have hq : 0 < (1 + s * ‖y - u‖) ^ (d + 1) := by positivity
  have h3 : ((1 + s * ‖x - u‖) ^ (d + 1))⁻¹ ≤ 2 ^ (d + 1) * ((1 + s * ‖y - u‖) ^ (d + 1))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hq, inv_mul_le_iff₀ hp]
    linarith
  unfold Phi
  have e2 : (2 : ℝ≥0∞) ^ (d + 1) = ENNReal.ofReal ((2 : ℝ) ^ (d + 1)) := by
    rw [ENNReal.ofReal_pow (by norm_num)]; simp
  rw [e2, ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc s ^ d * ((1 + s * ‖x - u‖) ^ (d + 1))⁻¹ ≤ s ^ d * (2 ^ (d + 1) * ((1 + s * ‖y - u‖) ^ (d + 1))⁻¹) := by
        gcongr
    _ = _ := by ring

lemma CvP_eq_shift (j : ℤ) (w : 𝔼 → ℝ≥0∞) (z : 𝔼) :
    CvP j w z = ∫⁻ u, Phi j (z - u) * w u := by
  unfold CvP
  have := lintegral_sub_left_eq_self (μ := (volume : Measure 𝔼))
    (fun u => Phi j (z - u) * w u) z
  rw [← this]
  refine lintegral_congr fun y => ?_
  simp

lemma CvP_shift (j : ℤ) {w : 𝔼 → ℝ≥0∞} (hw : Measurable w) {x y : 𝔼}
    (hxy : ‖x - y‖ < (2 : ℝ) ^ (-j)) : CvP j w x ≤ 2 ^ (d + 1) * CvP j w y := by
  have hm : Measurable (fun u : 𝔼 => Phi j (y - u) * w u) :=
    ((Phi_measurable j).comp (measurable_const.sub measurable_id)).mul hw
  rw [CvP_eq_shift, CvP_eq_shift, ← lintegral_const_mul _ hm]
  refine lintegral_mono fun u => ?_
  rw [← mul_assoc]
  exact mul_le_mul_left (Phi_shift j hxy u) _

/-- A Littlewood–Paley family with a reproducing kernel (`K_j = L_j ⋆ K_j`). -/
structure IsLPRep (K : ℤ → 𝔼 → ℂ) : Prop where
  lp : IsLP K
  rep : ∃ (L : ℤ → 𝔼 → ℂ) (A' : ℝ≥0∞), A' ≠ ⊤ ∧ (∀ j, DecK A' j (L j)) ∧
    (∀ j, Measurable (L j)) ∧ ∀ (F : 𝔼 → ℂ), Measurable F → ∀ B : ℝ≥0∞, B ≠ ⊤ →
      (∀ x, ‖F x‖ₑ ≤ B) → ∀ j x, cv (K j) F x = cv (L j) (cv (K j) F) x

/-- **Weighted Littlewood–Paley inequality**: `∑_j ∫ |K_j ⋆ F|² w ≲ ∫ (M F)² M w`. -/
lemma weighted_LP (hd : 1 ≤ d) {K : ℤ → 𝔼 → ℂ} (hK : IsLPRep K) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (F : 𝔼 → ℂ), Measurable F → Integrable F → ∀ B : ℝ≥0∞, B ≠ ⊤ →
      (∀ x, ‖F x‖ₑ ≤ B) → ∀ w : 𝔼 → ℝ≥0∞, Measurable w →
      ∑' j, ∫⁻ x, ‖cv (K j) F x‖ₑ ^ 2 * w x ≤
        C * ∫⁻ x, (cmxHLS_Md (fun y => ‖F y‖ₑ) x) ^ 2 * cmxHLS_Md w x := by
  obtain ⟨L, A', hA', hL, hLm, hrep⟩ := hK.rep
  obtain ⟨Ct, hCt, htent⟩ := tent_bound hd hK.lp
  refine ⟨(A' * KP d * A') * Ct * (2 ^ (d + 1) * KP d), ?_, fun F hF hFi B hB hFB w hw => ?_⟩
  · refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top hA' KP_ne_top) hA')
      hCt) (ENNReal.mul_ne_top (by simp) KP_ne_top)
  set Md : 𝔼 → ℝ≥0∞ := cmxHLS_Md (fun y => ‖F y‖ₑ) with hMd
  have hMdm : Measurable Md := cmxHLS_Md_measurable hF.enorm
  have hMdw : Measurable (cmxHLS_Md w) := cmxHLS_Md_measurable hw
  set a : ℤ → 𝔼 → ℂ := fun j => cv (K j) F with ha
  have ham : ∀ j, Measurable (a j) := fun j => measurable_cv (hK.lp.meas j) hF
  set G : 𝔼 → ℝ≥0∞ := fun y => 2 ^ (d + 1) * KP d * cmxHLS_Md w y with hG
  have hGm : Measurable G := measurable_const.mul hMdw
  set Et : ℝ → Set 𝔼 := fun t => {y | ENNReal.ofReal t < G y} with hEt
  have hEtm : ∀ t, MeasurableSet (Et t) := fun t => measurableSet_lt measurable_const hGm
  have hVm : ∀ j, Measurable (CvP j w) := fun j => CvP_measurable j hw
  -- Step A and B
  have hstepB : ∀ j, ∫⁻ x, ‖a j x‖ₑ ^ 2 * w x ≤
      (A' * KP d * A') * ∫⁻ x, ‖a j x‖ₑ ^ 2 * CvP j w x := by
    intro j
    have hH : Measurable (fun y => ‖a j y‖ₑ ^ 2) := (ham j).enorm.pow_const 2
    have hA : ∀ x, ‖a j x‖ₑ ^ 2 ≤ (A' * KP d) * (A' * CvP j (fun y => ‖a j y‖ₑ ^ 2) x) := by
      intro x
      have := enorm_cv_sq_le (hL j) (hLm j) (ham j) x
      have e : a j x = cv (L j) (a j) x := hrep F hF B hB hFB j x
      rw [e]
      exact this
    calc ∫⁻ x, ‖a j x‖ₑ ^ 2 * w x ≤ ∫⁻ x, ((A' * KP d) * (A' * CvP j (fun y => ‖a j y‖ₑ ^ 2) x)) * w x :=
          lintegral_mono fun x => mul_le_mul_left (hA x) _
      _ = (A' * KP d * A') * ∫⁻ x, CvP j (fun y => ‖a j y‖ₑ ^ 2) x * w x := by
          have hm1 : Measurable (fun x => CvP j (fun y => ‖a j y‖ₑ ^ 2) x * w x) :=
            (CvP_measurable j hH).mul hw
          rw [← lintegral_const_mul _ hm1]
          refine lintegral_congr fun x => ?_
          ring
      _ = (A' * KP d * A') * ∫⁻ x, ‖a j x‖ₑ ^ 2 * CvP j w x := by
          rw [lintegral_CvP_mul j hH hw]
  -- Step C: layer cake and tents
  have hlayer : ∀ j, ∫⁻ x, ‖a j x‖ₑ ^ 2 * CvP j w x ≤
      ∫⁻ t in Set.Ioi (0 : ℝ), ∫⁻ x in tent (Et t) j, ‖a j x‖ₑ ^ 2 := by
    intro j
    rw [lintegral_mul_layer ((ham j).enorm.pow_const 2) (hVm j)]
    refine lintegral_mono fun t => ?_
    refine lintegral_mono_set ?_
    intro x hx
    simp only [Set.mem_setOf_eq] at hx
    intro y hy
    simp only [hEt, Set.mem_setOf_eq]
    have hxy : ‖x - y‖ < (2 : ℝ) ^ (-j) := by rwa [norm_sub_rev]
    calc ENNReal.ofReal t < CvP j w x := hx
      _ ≤ 2 ^ (d + 1) * CvP j w y := CvP_shift j hw hxy
      _ ≤ 2 ^ (d + 1) * (KP d * cmxHLS_Md w y) := mul_le_mul_right (CvP_le j hw y) _
      _ = G y := by simp only [hG]; ring
  have hψanti : ∀ j, Antitone (fun t : ℝ => ∫⁻ x in tent (Et t) j, ‖a j x‖ₑ ^ 2) := by
    intro j t t' htt'
    refine lintegral_mono_set ?_
    intro x hx y hy
    have := hx y hy
    simp only [hEt, Set.mem_setOf_eq] at this ⊢
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal htt') this
  have hsumt : ∑' j, ∫⁻ t in Set.Ioi (0 : ℝ), ∫⁻ x in tent (Et t) j, ‖a j x‖ₑ ^ 2 ≤
      Ct * ∫⁻ x, Md x ^ 2 * G x := by
    rw [← lintegral_tsum fun j => (hψanti j).measurable.aemeasurable]
    calc ∫⁻ t in Set.Ioi (0 : ℝ), ∑' j, ∫⁻ x in tent (Et t) j, ‖a j x‖ₑ ^ 2
        ≤ ∫⁻ t in Set.Ioi (0 : ℝ), Ct * ∫⁻ x in Et t, Md x ^ 2 :=
          lintegral_mono fun t => htent F hF hFi B hB hFB (Et t) (hEtm t)
      _ = Ct * ∫⁻ t in Set.Ioi (0 : ℝ), ∫⁻ x in Et t, Md x ^ 2 := by
          rw [lintegral_const_mul']
          exact hCt
      _ = Ct * ∫⁻ x, Md x ^ 2 * G x := by
          rw [lintegral_mul_layer (hMdm.pow_const 2) hGm]
  calc ∑' j, ∫⁻ x, ‖cv (K j) F x‖ₑ ^ 2 * w x
      ≤ ∑' j, (A' * KP d * A') * ∫⁻ x, ‖a j x‖ₑ ^ 2 * CvP j w x :=
        ENNReal.tsum_le_tsum hstepB
    _ = (A' * KP d * A') * ∑' j, ∫⁻ x, ‖a j x‖ₑ ^ 2 * CvP j w x := ENNReal.tsum_mul_left
    _ ≤ (A' * KP d * A') * ∑' j, ∫⁻ t in Set.Ioi (0 : ℝ), ∫⁻ x in tent (Et t) j, ‖a j x‖ₑ ^ 2 :=
        mul_le_mul_right (ENNReal.tsum_le_tsum hlayer) _
    _ ≤ (A' * KP d * A') * (Ct * ∫⁻ x, Md x ^ 2 * G x) := mul_le_mul_right hsumt _
    _ = _ := by
        have : ∫⁻ x, Md x ^ 2 * G x = (2 ^ (d + 1) * KP d) * ∫⁻ x, Md x ^ 2 * cmxHLS_Md w x := by
          have hm2 : Measurable (fun x => Md x ^ 2 * cmxHLS_Md w x) :=
            (hMdm.pow_const 2).mul hMdw
          rw [← lintegral_const_mul _ hm2]
          refine lintegral_congr fun x => ?_
          simp only [hG]; ring
        rw [this]; ring

lemma enorm_rpow_two_mul_le {F : 𝔼 → ℂ} {B : ℝ≥0∞} {s : ℝ} (hs : 1 < s) (hFB : ∀ x, ‖F x‖ₑ ≤ B)
    (x : 𝔼) : ‖F x‖ₑ ^ (2 * s) ≤ B ^ (2 * s - 1) * ‖F x‖ₑ := by
  have h := ENNReal.rpow_add_of_nonneg (x := ‖F x‖ₑ) (2 * s - 1) 1 (by linarith) (by norm_num)
  rw [ENNReal.rpow_one, show (2 * s - 1) + 1 = 2 * s by ring] at h
  rw [h]
  exact mul_le_mul_left (ENNReal.rpow_le_rpow (hFB x) (by linarith)) _

lemma lintegral_enorm_rpow_ne_top {F : 𝔼 → ℂ} (hFi : Integrable F) {B : ℝ≥0∞} (hB : B ≠ ⊤) {s : ℝ}
    (hs : 1 < s) (hFB : ∀ x, ‖F x‖ₑ ≤ B) : ∫⁻ x, ‖F x‖ₑ ^ (2 * s) ≠ ⊤ := by
  refine ne_top_of_le_ne_top (b := B ^ (2 * s - 1) * ∫⁻ x, ‖F x‖ₑ) ?_ ?_
  · exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) hB) hFi.2.ne
  · calc ∫⁻ x, ‖F x‖ₑ ^ (2 * s) ≤ ∫⁻ x, B ^ (2 * s - 1) * ‖F x‖ₑ :=
          lintegral_mono fun x => enorm_rpow_two_mul_le hs hFB x
      _ = _ := lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by linarith) hB)

/-- **Littlewood–Paley square function bound for `p = 2s > 2`.** -/
lemma E1_gt (hd : 1 ≤ d) {K : ℤ → 𝔼 → ℂ} (hK : IsLPRep K) {s : ℝ} (hs : 1 < s) :
    ∃ C : ℝ≥0, ∀ F : 𝔼 → ℂ, Measurable F → Integrable F → ∀ B : ℝ≥0∞, B ≠ ⊤ →
      (∀ x, ‖F x‖ₑ ≤ B) →
      ∫⁻ x, sqS (fun j => cv (K j) F) x ^ s ≤ C * ∫⁻ x, ‖F x‖ₑ ^ (2 * s) := by
  have hs0 : 0 < s := by linarith
  obtain ⟨Cw, hCw, hW⟩ := weighted_LP hd hK
  obtain ⟨Cd, hCd⟩ := dual_Lp_bound hd hs
  obtain ⟨CM, hCM⟩ := Mx_strong hd (p := 2 * s) (by linarith)
  obtain ⟨A, hA, hdec⟩ := hK.lp.dec
  have hbig : ((Cd : ℝ≥0∞) * Cw) ^ s * CM ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hs0.le
      (ENNReal.mul_ne_top ENNReal.coe_ne_top hCw)) ENNReal.coe_ne_top
  refine ⟨(((Cd : ℝ≥0∞) * Cw) ^ s * CM).toNNReal, fun F hF hFi B hB hFB => ?_⟩
  rw [ENNReal.coe_toNNReal hbig]
  set a : ℤ → 𝔼 → ℂ := fun j => cv (K j) F with ha
  have ham : ∀ j, Measurable (a j) := fun j => measurable_cv (hK.lp.meas j) hF
  set Md : 𝔼 → ℝ≥0∞ := cmxHLS_Md (fun y => ‖F y‖ₑ) with hMd
  have hMdm : Measurable Md := cmxHLS_Md_measurable hF.enorm
  have hfinF : ∫⁻ x, ‖F x‖ₑ ^ (2 * s) ≠ ⊤ := lintegral_enorm_rpow_ne_top hFi hB hs hFB
  by_cases hfin : ∫⁻ x, ‖F x‖ₑ ^ (2 * s) = ⊤
  · exact absurd hfin hfinF
  have hMdint : ∫⁻ x, Md x ^ (2 * s) ≤ CM * ∫⁻ x, ‖F x‖ₑ ^ (2 * s) :=
    hCM (fun y => ‖F y‖ₑ) hF.enorm
  -- the truncated square functions
  set T : ℕ → 𝔼 → ℝ≥0∞ := fun n x => ∑ j ∈ Fn n, ‖a j x‖ₑ ^ 2 with hT
  have hTm : ∀ n, Measurable (T n) := fun n =>
    Finset.measurable_sum _ fun j _ => (ham j).enorm.pow_const 2
  have hTmono : Monotone T := fun m n hmn x => Finset.sum_le_sum_of_subset (Fn_mono hmn)
  have hsup : ∀ x, sqS (fun j => cv (K j) F) x = ⨆ n, T n x := fun x => tsum_eq_iSup_Fn _
  have hjfin : ∀ j, ∫⁻ x, (‖a j x‖ₑ ^ 2) ^ s ≠ ⊤ := by
    intro j
    have hAKP : (A * KP d) ^ (2 * s) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by linarith) (ENNReal.mul_ne_top hA KP_ne_top)
    refine ne_top_of_le_ne_top (b := (A * KP d) ^ (2 * s) * (CM * ∫⁻ x, ‖F x‖ₑ ^ (2 * s)))
      (ENNReal.mul_ne_top hAKP (ENNReal.mul_ne_top ENNReal.coe_ne_top hfinF)) ?_
    calc ∫⁻ x, (‖a j x‖ₑ ^ 2) ^ s ≤ ∫⁻ x, ((A * KP d) * Md x) ^ (2 * s) := by
          refine lintegral_mono fun x => ?_
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, Nat.cast_ofNat]
          refine ENNReal.rpow_le_rpow ?_ (by linarith)
          calc ‖a j x‖ₑ ≤ A * CvP j (fun y => ‖F y‖ₑ) x := enorm_cv_le_CvP (hdec j) hF x
            _ ≤ A * (KP d * Md x) := mul_le_mul_right (CvP_le j hF.enorm x) _
            _ = _ := by ring
      _ = (A * KP d) ^ (2 * s) * ∫⁻ x, Md x ^ (2 * s) := by
          rw [← lintegral_const_mul' _ _ hAKP]
          exact lintegral_congr fun x => ENNReal.mul_rpow_of_nonneg _ _ (by linarith)
      _ ≤ _ := mul_le_mul_right hMdint _
  have key : ∀ n, ∫⁻ x, T n x ^ s ≤ ((Cd : ℝ≥0∞) * Cw) ^ s * ∫⁻ x, Md x ^ (2 * s) := by
    intro n
    have hTfin : ∫⁻ x, T n x ^ s ≠ ⊤ :=
      lintegral_finsum_rpow_ne_top hs.le (Fn n) (fun j => (ham j).enorm.pow_const 2)
        (fun j _ => hjfin j)
    have hdual : ∀ w : 𝔼 → ℝ≥0∞, Measurable w →
        ∫⁻ x, T n x * w x ≤ Cw * ∫⁻ x, (Md x) ^ 2 * cmxHLS_Md w x := by
      intro w hw
      calc ∫⁻ x, T n x * w x = ∑ j ∈ Fn n, ∫⁻ x, ‖a j x‖ₑ ^ 2 * w x := by
            simp_rw [hT, Finset.sum_mul]
            rw [lintegral_finsetSum]
            intro j _
            exact ((ham j).enorm.pow_const 2).mul hw
        _ ≤ ∑' j, ∫⁻ x, ‖a j x‖ₑ ^ 2 * w x := ENNReal.sum_le_tsum _
        _ ≤ Cw * ∫⁻ x, (Md x) ^ 2 * cmxHLS_Md w x := hW F hF hFi B hB hFB w hw
    have h1 := hCd (T n) (fun x => Md x ^ 2) Cw (hTm n) (hMdm.pow_const 2) hTfin hdual
    calc ∫⁻ x, T n x ^ s ≤ ((Cd : ℝ≥0∞) * Cw) ^ s * ∫⁻ x, (Md x ^ 2) ^ s := h1
      _ = _ := by
          congr 1
          refine lintegral_congr fun x => ?_
          rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul, Nat.cast_ofNat]
  calc ∫⁻ x, sqS (fun j => cv (K j) F) x ^ s = ∫⁻ x, (⨆ n, T n x) ^ s := by
        refine lintegral_congr fun x => ?_
        rw [hsup]
    _ = ⨆ n, ∫⁻ x, T n x ^ s := lintegral_rpow_iSup hTm hTmono hs0
    _ ≤ ((Cd : ℝ≥0∞) * Cw) ^ s * ∫⁻ x, Md x ^ (2 * s) := iSup_le key
    _ ≤ ((Cd : ℝ≥0∞) * Cw) ^ s * (CM * ∫⁻ x, ‖F x‖ₑ ^ (2 * s)) := mul_le_mul_right hMdint _
    _ = _ := by rw [← mul_assoc]

end HRS.Commutator.Whole.XLI
