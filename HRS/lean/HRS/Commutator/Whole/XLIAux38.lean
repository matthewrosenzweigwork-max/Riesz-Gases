import HRS.Commutator.Whole.XLIAux37

/-!
# X-LI part 38: the weighted tent bound
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology SchwartzMap

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma Md_mono {f g : 𝔼 → ℝ≥0∞} (h : ∀ y, f y ≤ g y) (x : 𝔼) :
    cmxHLS_Md f x ≤ cmxHLS_Md g x := by
  unfold cmxHLS_Md
  refine iSup_mono fun j => ?_
  exact mul_le_mul_right (lintegral_mono fun y => h y) _

lemma Md_le_mul {f g : 𝔼 → ℝ≥0∞} {c : ℝ≥0∞} (hc : c ≠ ⊤) (h : ∀ y, g y ≤ c * f y) (x : 𝔼) :
    cmxHLS_Md g x ≤ c * cmxHLS_Md f x := by
  unfold cmxHLS_Md
  rw [ENNReal.mul_iSup]
  refine iSup_mono fun j => ?_
  calc (volume (closedBall x ((2 : ℝ) ^ j)))⁻¹ * ∫⁻ y in closedBall x ((2 : ℝ) ^ j), g y
      ≤ (volume (closedBall x ((2 : ℝ) ^ j)))⁻¹ * ∫⁻ y in closedBall x ((2 : ℝ) ^ j), c * f y :=
        mul_le_mul_right (lintegral_mono fun y => h y) _
    _ = c * ((volume (closedBall x ((2 : ℝ) ^ j)))⁻¹ * ∫⁻ y in closedBall x ((2 : ℝ) ^ j), f y) := by
        rw [lintegral_const_mul' _ _ hc]; ring

/-- **weighted tent bound** -/
lemma tent_weighted (hd : 1 ≤ d) {K : ℤ → 𝔼 → ℂ} (hK : IsLPRep K) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ (F : 𝔼 → ℂ), Measurable F → Integrable F → ∀ B : ℝ≥0∞, B ≠ ⊤ →
      (∀ x, ‖F x‖ₑ ≤ B) → ∀ E : Set 𝔼, MeasurableSet E → volume E ≠ ⊤ →
      ∀ w : 𝔼 → ℝ≥0∞, Measurable w →
      ∑' j, ∫⁻ x in tent E j, ‖cv (K j) F x‖ₑ ^ 2 * w x ≤
        C * B ^ 2 * ∫⁻ x in E, (w x + cmxHLS_Md (cmxHLS_Md w) x) := by
  obtain ⟨A, hA, hdec⟩ := hK.lp.dec
  obtain ⟨Cw, hCw, hW⟩ := weighted_LP hd hK
  refine ⟨4 * 10 ^ d * Cw + 4 * (A * KT d) ^ 2, ?_, fun F hF hFi B hB hFB E hE hEfin w hw => ?_⟩
  · exact ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp)
      (ENNReal.pow_ne_top (by simp))) hCw,
      ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top (ENNReal.mul_ne_top hA KT_ne_top))⟩
  set F1 : 𝔼 → ℂ := E.indicator F with hF1
  set F2 : 𝔼 → ℂ := Eᶜ.indicator F with hF2
  have hF1m : Measurable F1 := hF.indicator hE
  have hF2m : Measurable F2 := hF.indicator hE.compl
  have hFsplit : F = fun y => F1 y + F2 y := by
    ext y; simp only [hF1, hF2]; exact (congrFun (Set.indicator_self_add_compl E F) y).symm
  have hBr : ∀ x, ‖F x‖ ≤ B.toReal := fun x => by
    have := hFB x
    rw [← ofReal_norm] at this
    exact (ENNReal.ofReal_le_iff_le_toReal hB).1 this
  have hF1b : ∀ x, ‖F1 x‖ ≤ B.toReal := fun x => by
    simp only [hF1]; by_cases h : x ∈ E
    · rw [Set.indicator_of_mem h]; exact hBr x
    · rw [Set.indicator_of_notMem h]; simp
  have hF2b : ∀ x, ‖F2 x‖ ≤ B.toReal := fun x => by
    simp only [hF2]; by_cases h : x ∈ Eᶜ
    · rw [Set.indicator_of_mem h]; exact hBr x
    · rw [Set.indicator_of_notMem h]; simp
  have hF1i : Integrable F1 := hFi.indicator hE
  have hF1B : ∀ x, ‖F1 x‖ₑ ≤ B := fun x => by
    simp only [hF1]; by_cases h : x ∈ E
    · rw [Set.indicator_of_mem h]; exact hFB x
    · rw [Set.indicator_of_notMem h]; simp
  have hMdB : ∀ x, cmxHLS_Md (fun y => ‖F y‖ₑ) x ≤ B := fun x => Md_le_of_le hFB x
  set Md : 𝔼 → ℝ≥0∞ := cmxHLS_Md (fun y => ‖F y‖ₑ) with hMd
  -- the tail function
  set ψ : ℤ → 𝔼 → ℝ≥0∞ := fun j x =>
    (A * KT d) ^ 2 * ENNReal.ofReal (((2 : ℝ) ^ j * Metric.infDist x Eᶜ)⁻¹) ^ 2 * B ^ 2 with hψ
  have hψm : ∀ j, Measurable (ψ j) := fun j => by
    refine (measurable_const.mul ?_).mul measurable_const
    exact ((ENNReal.measurable_ofReal.comp (measurable_const.mul
      (Metric.continuous_infDist_pt _).measurable).inv)).pow_const 2
  have hpt : ∀ j, ∀ x ∈ tent E j, ‖cv (K j) F2 x‖ₑ ^ 2 ≤ ψ j x := by
    intro j x hx
    by_cases hEc : Eᶜ.Nonempty
    · have hdd : (2 : ℝ) ^ (-j) ≤ Metric.infDist x Eᶜ := by
        rw [Metric.le_infDist hEc]
        intro y hy
        by_contra hlt
        rw [not_le] at hlt
        have := hx y (by rw [dist_eq_norm] at hlt; rwa [norm_sub_rev] at hlt)
        exact hy this
      have hddpos : 0 < Metric.infDist x Eᶜ :=
        lt_of_lt_of_le (zpow_pos (by norm_num) _) hdd
      have h1 := tail_pointwise (hdec j) hF E hE x hddpos
      calc ‖cv (K j) F2 x‖ₑ ^ 2 ≤ (A * KT d * ENNReal.ofReal (((2 : ℝ) ^ j * Metric.infDist x Eᶜ)⁻¹) *
            Md x) ^ 2 := by gcongr
        _ ≤ (A * KT d * ENNReal.ofReal (((2 : ℝ) ^ j * Metric.infDist x Eᶜ)⁻¹) * B) ^ 2 := by
            gcongr; exact hMdB x
        _ = ψ j x := by simp only [hψ]; ring
    · rw [Set.not_nonempty_iff_eq_empty] at hEc
      have : F2 = fun _ => 0 := by
        ext y
        simp only [hF2, hEc, Set.indicator_empty]
      have h0 : cv (K j) F2 x = 0 := by rw [cv_apply, this]; simp
      rw [h0]; simp
  have hind : ∀ x j, (tent E j).indicator (ψ j) x ≤ (A * KT d) ^ 2 * B ^ 2 *
      (if 1 ≤ (2 : ℝ) ^ j * Metric.infDist x Eᶜ then
        ENNReal.ofReal (((2 : ℝ) ^ j * Metric.infDist x Eᶜ)⁻¹) ^ 2 else 0) := by
    intro x j
    by_cases hx : x ∈ tent E j
    · rw [Set.indicator_of_mem hx]
      by_cases hEc : Eᶜ.Nonempty
      · have hdd : (2 : ℝ) ^ (-j) ≤ Metric.infDist x Eᶜ := by
          rw [Metric.le_infDist hEc]
          intro y hy
          by_contra hlt
          rw [not_le] at hlt
          have := hx y (by rw [dist_eq_norm] at hlt; rwa [norm_sub_rev] at hlt)
          exact hy this
        have h1 : 1 ≤ (2 : ℝ) ^ j * Metric.infDist x Eᶜ := by
          calc (1 : ℝ) = (2 : ℝ) ^ j * (2 : ℝ) ^ (-j) := by
                rw [← zpow_add₀ (by norm_num)]; simp
            _ ≤ _ := by gcongr
        rw [if_pos h1]
        simp only [hψ]
        refine le_of_eq ?_
        ring
      · rw [Set.not_nonempty_iff_eq_empty] at hEc
        simp only [hψ, hEc, Metric.infDist_empty, mul_zero, inv_zero, ENNReal.ofReal_zero]
        simp
    · rw [Set.indicator_of_notMem hx]; exact zero_le
  have hsumψ : ∑' j, ∫⁻ x in tent E j, ψ j x * w x ≤ 2 * (A * KT d) ^ 2 * B ^ 2 * ∫⁻ x in E, w x := by
    calc ∑' j, ∫⁻ x in tent E j, ψ j x * w x
        = ∑' j, ∫⁻ x, (tent E j).indicator (fun x => ψ j x * w x) x := by
          refine tsum_congr fun j => ?_
          rw [lintegral_indicator (measurableSet_tent E j)]
      _ = ∫⁻ x, ∑' j, (tent E j).indicator (fun x => ψ j x * w x) x := by
          rw [lintegral_tsum]
          intro j; exact (((hψm j).mul hw).indicator (measurableSet_tent E j)).aemeasurable
      _ ≤ ∫⁻ x, E.indicator (fun x => 2 * (A * KT d) ^ 2 * B ^ 2 * w x) x := by
          refine lintegral_mono fun x => ?_
          by_cases hxE : x ∈ E
          · rw [Set.indicator_of_mem hxE]
            calc ∑' j, (tent E j).indicator (fun x => ψ j x * w x) x
                = ∑' j, (tent E j).indicator (ψ j) x * w x := by
                  refine tsum_congr fun j => ?_
                  by_cases hxj : x ∈ tent E j
                  · simp [Set.indicator_of_mem hxj]
                  · simp [Set.indicator_of_notMem hxj]
              _ ≤ ∑' j, ((A * KT d) ^ 2 * B ^ 2 *
                  (if 1 ≤ (2 : ℝ) ^ j * Metric.infDist x Eᶜ then
                    ENNReal.ofReal (((2 : ℝ) ^ j * Metric.infDist x Eᶜ)⁻¹) ^ 2 else 0)) * w x :=
                  ENNReal.tsum_le_tsum fun j => mul_le_mul_left (hind x j) _
              _ = ((A * KT d) ^ 2 * B ^ 2 * ∑' j : ℤ,
                  (if 1 ≤ (2 : ℝ) ^ j * Metric.infDist x Eᶜ then
                    ENNReal.ofReal (((2 : ℝ) ^ j * Metric.infDist x Eᶜ)⁻¹) ^ 2 else 0)) * w x := by
                  rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_left]
              _ ≤ ((A * KT d) ^ 2 * B ^ 2 * 2) * w x := by
                  refine mul_le_mul_left ?_ _
                  refine mul_le_mul_right ?_ _
                  by_cases hpos : 0 < Metric.infDist x Eᶜ
                  · exact tail_geom_sum hpos
                  · have h0 : Metric.infDist x Eᶜ = 0 :=
                      le_antisymm (not_lt.1 hpos) Metric.infDist_nonneg
                    simp [h0]
              _ = 2 * (A * KT d) ^ 2 * B ^ 2 * w x := by ring
          · have : ∀ j, x ∉ tent E j := fun j hx => hxE (tent_subset E j hx)
            simp [Set.indicator_of_notMem hxE, Set.indicator_of_notMem (this _)]
      _ = 2 * (A * KT d) ^ 2 * B ^ 2 * ∫⁻ x in E, w x := by
          rw [lintegral_indicator hE, lintegral_const_mul _ hw]
  -- the local part
  set wE : 𝔼 → ℝ≥0∞ := E.indicator w with hwE
  have hwEm : Measurable wE := hw.indicator hE
  have hint1 : ∀ j, ∫⁻ x in tent E j, ‖cv (K j) F x‖ₑ ^ 2 * w x ≤
      2 * ((∫⁻ x, ‖cv (K j) F1 x‖ₑ ^ 2 * wE x) + ∫⁻ x in tent E j, ψ j x * w x) := by
    intro j
    have hKi := integrable_of_dec hA (hdec j) (hK.lp.meas j)
    have hpt2 : ∀ x ∈ tent E j, ‖cv (K j) F x‖ₑ ^ 2 * w x ≤
        2 * (‖cv (K j) F1 x‖ₑ ^ 2 * wE x + ψ j x * w x) := by
      intro x hx
      have hxE : x ∈ E := tent_subset E j hx
      have e : cv (K j) F x = cv (K j) F1 x + cv (K j) F2 x := by
        have := cv_add_of_bdd hKi hF1m hF2m hF1b hF2b x
        rw [← hFsplit] at this
        exact this
      have hwx : wE x = w x := by simp [hwE, Set.indicator_of_mem hxE]
      rw [e, hwx]
      calc ‖cv (K j) F1 x + cv (K j) F2 x‖ₑ ^ 2 * w x
          ≤ (2 * (‖cv (K j) F1 x‖ₑ ^ 2 + ‖cv (K j) F2 x‖ₑ ^ 2)) * w x := by
            refine mul_le_mul_left ?_ _
            calc ‖cv (K j) F1 x + cv (K j) F2 x‖ₑ ^ 2
                ≤ (‖cv (K j) F1 x‖ₑ + ‖cv (K j) F2 x‖ₑ) ^ 2 := by gcongr; exact enorm_add_le _ _
              _ ≤ _ := add_sq_le_two _ _
        _ ≤ (2 * (‖cv (K j) F1 x‖ₑ ^ 2 + ψ j x)) * w x := by
            gcongr; exact hpt j x hx
        _ = 2 * (‖cv (K j) F1 x‖ₑ ^ 2 * w x + ψ j x * w x) := by ring
    have hcv1m : Measurable (fun x => ‖cv (K j) F1 x‖ₑ ^ 2 * wE x) :=
      (((measurable_cv (hK.lp.meas j) hF1m).enorm).pow_const 2).mul hwEm
    have hsm : Measurable (fun x => ‖cv (K j) F1 x‖ₑ ^ 2 * wE x + ψ j x * w x) :=
      hcv1m.add ((hψm j).mul hw)
    calc ∫⁻ x in tent E j, ‖cv (K j) F x‖ₑ ^ 2 * w x
        ≤ ∫⁻ x in tent E j, 2 * (‖cv (K j) F1 x‖ₑ ^ 2 * wE x + ψ j x * w x) :=
          setLIntegral_mono' (measurableSet_tent E j) hpt2
      _ = 2 * ((∫⁻ x in tent E j, ‖cv (K j) F1 x‖ₑ ^ 2 * wE x) +
            ∫⁻ x in tent E j, ψ j x * w x) := by
          rw [lintegral_const_mul _ hsm, lintegral_add_left hcv1m]
      _ ≤ _ := mul_le_mul_right (add_le_add (setLIntegral_le_lintegral _ _) le_rfl) _
  -- the Fefferman–Stein step
  have hMd1E : Measurable (cmxHLS_Md (E.indicator (fun _ => (1 : ℝ≥0∞)))) :=
    cmxHLS_Md_measurable (measurable_const.indicator hE)
  have hlocal : ∑' j, ∫⁻ x, ‖cv (K j) F1 x‖ₑ ^ 2 * wE x ≤
      Cw * (B ^ 2 * (2 * 10 ^ d * ∫⁻ x in E, cmxHLS_Md (cmxHLS_Md w) x)) := by
    refine (hW F1 hF1m hF1i B hB hF1B wE hwEm).trans (mul_le_mul_right ?_ _)
    have hpt3 : ∀ x, cmxHLS_Md (fun y => ‖F1 y‖ₑ) x ≤
        B * cmxHLS_Md (E.indicator (fun _ => (1 : ℝ≥0∞))) x := fun x =>
      Md_le_mul hB (fun y => by
        by_cases hy : y ∈ E
        · simp [hF1, Set.indicator_of_mem hy]; exact hFB y
        · simp [hF1, Set.indicator_of_notMem hy]) x
    have hMdwE : Measurable (cmxHLS_Md wE) := cmxHLS_Md_measurable hwEm
    calc ∫⁻ x, cmxHLS_Md (fun y => ‖F1 y‖ₑ) x ^ 2 * cmxHLS_Md wE x
        ≤ ∫⁻ x, (B ^ 2 * (cmxHLS_Md (E.indicator (fun _ => (1 : ℝ≥0∞))) x ^ 2 *
            cmxHLS_Md wE x)) := by
          refine lintegral_mono fun x => ?_
          calc cmxHLS_Md (fun y => ‖F1 y‖ₑ) x ^ 2 * cmxHLS_Md wE x
              ≤ (B * cmxHLS_Md (E.indicator (fun _ => (1 : ℝ≥0∞))) x) ^ 2 * cmxHLS_Md wE x := by
                gcongr; exact hpt3 x
            _ = _ := by ring
      _ = B ^ 2 * ∫⁻ x, cmxHLS_Md (E.indicator (fun _ => (1 : ℝ≥0∞))) x ^ 2 * cmxHLS_Md wE x := by
          have hm : Measurable (fun x => cmxHLS_Md (E.indicator (fun _ => (1 : ℝ≥0∞))) x ^ 2 *
              cmxHLS_Md wE x) := (hMd1E.pow_const 2).mul hMdwE
          rw [lintegral_const_mul _ hm]
      _ ≤ B ^ 2 * (2 * 10 ^ d * ∫⁻ x in E, cmxHLS_Md (cmxHLS_Md wE) x) :=
          mul_le_mul_right (FS_sq hd hE hEfin hMdwE) _
      _ ≤ B ^ 2 * (2 * 10 ^ d * ∫⁻ x in E, cmxHLS_Md (cmxHLS_Md w) x) := by
          refine mul_le_mul_right (mul_le_mul_right (lintegral_mono fun x => ?_) _) _
          refine Md_mono (fun y => Md_mono (fun z => ?_) y) x
          by_cases hz : z ∈ E
          · simp [hwE, Set.indicator_of_mem hz]
          · simp [hwE, Set.indicator_of_notMem hz]
  -- assemble
  have hadd : ∫⁻ x in E, (w x + cmxHLS_Md (cmxHLS_Md w) x) =
      (∫⁻ x in E, w x) + ∫⁻ x in E, cmxHLS_Md (cmxHLS_Md w) x :=
    lintegral_add_left hw _
  rw [hadd]
  calc ∑' j, ∫⁻ x in tent E j, ‖cv (K j) F x‖ₑ ^ 2 * w x
      ≤ ∑' j, 2 * ((∫⁻ x, ‖cv (K j) F1 x‖ₑ ^ 2 * wE x) + ∫⁻ x in tent E j, ψ j x * w x) :=
        ENNReal.tsum_le_tsum hint1
    _ = 2 * ((∑' j, ∫⁻ x, ‖cv (K j) F1 x‖ₑ ^ 2 * wE x) +
          ∑' j, ∫⁻ x in tent E j, ψ j x * w x) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]
    _ ≤ 2 * (Cw * (B ^ 2 * (2 * 10 ^ d * ∫⁻ x in E, cmxHLS_Md (cmxHLS_Md w) x)) +
          2 * (A * KT d) ^ 2 * B ^ 2 * ∫⁻ x in E, w x) :=
        mul_le_mul_right (add_le_add hlocal hsumψ) _
    _ ≤ (4 * 10 ^ d * Cw + 4 * (A * KT d) ^ 2) * B ^ 2 *
          ((∫⁻ x in E, w x) + ∫⁻ x in E, cmxHLS_Md (cmxHLS_Md w) x) := by
        set X1 := ∫⁻ x in E, w x
        set X2 := ∫⁻ x in E, cmxHLS_Md (cmxHLS_Md w) x
        calc 2 * (Cw * (B ^ 2 * (2 * 10 ^ d * X2)) + 2 * (A * KT d) ^ 2 * B ^ 2 * X1)
            = (4 * 10 ^ d * Cw) * B ^ 2 * X2 + (4 * (A * KT d) ^ 2) * B ^ 2 * X1 := by ring
          _ ≤ (4 * 10 ^ d * Cw) * B ^ 2 * (X1 + X2) + (4 * (A * KT d) ^ 2) * B ^ 2 * (X1 + X2) :=
              add_le_add (mul_le_mul_right le_add_self _) (mul_le_mul_right le_self_add _)
          _ = _ := by ring

end HRS.Commutator.Whole.XLI
