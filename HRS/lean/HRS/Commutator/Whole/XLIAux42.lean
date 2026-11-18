import HRS.Commutator.Whole.XLIAux41

/-!
# X-LI part 42: the Carleson endpoint estimate `E4At` for `r > 2`
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology SchwartzMap

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma eLpNorm_top_sch_ne_top (F : SchwartzMap 𝔼 ℂ) : eLpNorm (⇑F) ⊤ volume ≠ ⊤ := by
  obtain ⟨B, hB, hBd⟩ := sch_enorm_bdd F
  refine ne_top_of_le_ne_top hB ?_
  rw [eLpNorm_exponent_top F.continuous.aestronglyMeasurable]
  exact essSup_le_of_ae_le _ (Eventually.of_forall hBd)

/-- the operator `w ↦ w + M(M w)` is bounded on `L^t` -/
lemma V_bound (hd : 1 ≤ d) {t : ℝ} (ht : 1 < t) :
    ∃ CV : ℝ≥0∞, CV ≠ ⊤ ∧ ∀ w : 𝔼 → ℝ≥0∞, Measurable w →
      ∫⁻ x, (w x + cmxHLS_Md (cmxHLS_Md w) x) ^ t ≤ CV * ∫⁻ x, w x ^ t := by
  obtain ⟨CM, hCM⟩ := Mx_strong hd ht
  have ht0 : 0 < t := by linarith
  refine ⟨2 ^ t * (1 + CM * CM), ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg ht0.le (by simp))
    (ENNReal.add_ne_top.2 ⟨by simp, ENNReal.mul_ne_top (by simp) (by simp)⟩), fun w hw => ?_⟩
  have hMw : Measurable (cmxHLS_Md w) := cmxHLS_Md_measurable hw
  have hMMw : Measurable (cmxHLS_Md (cmxHLS_Md w)) := cmxHLS_Md_measurable hMw
  have h1 : ∫⁻ x, cmxHLS_Md w x ^ t ≤ CM * ∫⁻ x, w x ^ t := hCM w hw
  have h2 : ∫⁻ x, cmxHLS_Md (cmxHLS_Md w) x ^ t ≤ CM * ∫⁻ x, cmxHLS_Md w x ^ t := hCM _ hMw
  calc ∫⁻ x, (w x + cmxHLS_Md (cmxHLS_Md w) x) ^ t
      ≤ ∫⁻ x, 2 ^ t * (w x ^ t + cmxHLS_Md (cmxHLS_Md w) x ^ t) :=
        lintegral_mono fun x => rpow_add_le_two ht0.le _ _
    _ = 2 ^ t * ((∫⁻ x, w x ^ t) + ∫⁻ x, cmxHLS_Md (cmxHLS_Md w) x ^ t) := by
        have hm : Measurable (fun x => w x ^ t + cmxHLS_Md (cmxHLS_Md w) x ^ t) :=
          (hw.pow_const t).add (hMMw.pow_const t)
        have hm2 : Measurable (fun x => w x ^ t) := hw.pow_const t
        rw [lintegral_const_mul _ hm, lintegral_add_left hm2]
    _ ≤ 2 ^ t * ((∫⁻ x, w x ^ t) + CM * (CM * ∫⁻ x, w x ^ t)) := by
        gcongr
        exact h2.trans (mul_le_mul_right h1 _)
    _ = _ := by ring

lemma lintegral_enorm_rpow_sch_ne_top (ψ : SchwartzMap 𝔼 ℂ) {a : ℝ} (ha : 0 < a) :
    ∫⁻ z, ‖ψ z‖ₑ ^ a ≠ ⊤ := by
  have h := (schwartz_rpow_integrable ψ ha).lintegral_lt_top
  have : ∫⁻ z, ‖ψ z‖ₑ ^ a = ∫⁻ z, ENNReal.ofReal (‖ψ z‖ ^ a) := by
    refine lintegral_congr fun z => ?_
    rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ha.le, ofReal_norm]
  rw [this]; exact h.ne

section E4

variable (α : ℝ)

lemma Fj_enorm_le (hd : 1 ≤ d) : ∃ A1 : ℝ≥0∞, A1 ≠ ⊤ ∧ ∀ (φ : SchwartzMap 𝔼 ℂ) (B : ℝ≥0∞),
    (∀ x, ‖Fm α φ x‖ₑ ≤ B) → ∀ j x, ‖Fj α φ j x‖ₑ ≤ A1 * B := by
  obtain ⟨A, hA, hdec⟩ := dK_dec (symFam_Ths (d := d) (-α))
  refine ⟨A * KP d, ENNReal.mul_ne_top hA KP_ne_top, fun φ B hB j x => ?_⟩
  have h1 := enorm_cv_le (dK (Ths (-α) : ℤ → 𝔼 → ℂ) j) ⇑(Fm α φ) x
  refine h1.trans ?_
  calc ∫⁻ y, ‖dK (Ths (-α) : ℤ → 𝔼 → ℂ) j y‖ₑ * ‖Fm α φ (x - y)‖ₑ
      ≤ ∫⁻ y, ‖dK (Ths (-α) : ℤ → 𝔼 → ℂ) j y‖ₑ * B :=
        lintegral_mono fun y => mul_le_mul_right (hB _) _
    _ = (∫⁻ y, ‖dK (Ths (-α) : ℤ → 𝔼 → ℂ) j y‖ₑ) * B :=
        lintegral_mul_const'' _ (dK_continuous (symFam_Ths (d := d) (-α)) j).measurable.enorm.aemeasurable
    _ ≤ A * KP d * B := mul_le_mul_left (lintegral_enorm_le_of_dec (hdec j)) _

lemma Tn_fin (hd : 1 ≤ d) {r : ℝ} (hr : 1 < r) (φ ψ : SchwartzMap 𝔼 ℂ) (n : ℕ) :
    ∫⁻ x, (∑ j ∈ Fn n, hh α φ ψ j x ^ 2) ^ (r / 2) ≠ ⊤ := by
  obtain ⟨A1, hA1, hFj⟩ := Fj_enorm_le α hd (d := d)
  obtain ⟨CM, hCM⟩ := Mx_strong hd hr
  obtain ⟨B, hB, hBd⟩ := sch_enorm_bdd (Fm α φ)
  have hr0 : 0 < r := by linarith
  set cst : ℝ≥0∞ := ((Fn n).card : ℝ≥0∞) * ((A1 * B) * (4 * KP d)) ^ 2 with hcst
  have hcstne : cst ≠ ⊤ := ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top hA1 hB) (ENNReal.mul_ne_top (by simp) KP_ne_top)))
  have hpt : ∀ x, ∑ j ∈ Fn n, hh α φ ψ j x ^ 2 ≤ cst * Mx ψ x ^ 2 := by
    intro x
    calc ∑ j ∈ Fn n, hh α φ ψ j x ^ 2
        ≤ ∑ j ∈ Fn n, ((A1 * B) * (4 * (KP d * Mx ψ x))) ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          unfold hh
          exact pow_le_pow_left' (mul_le_mul' (hFj φ B hBd j x) (Gs_le ψ j x)) 2
      _ = cst * Mx ψ x ^ 2 := by
          rw [Finset.sum_const, nsmul_eq_mul, hcst]; ring
  have hMx : Measurable (Mx ψ) := Mx_meas ψ
  have hfin : cst ^ (r / 2) * (CM * ∫⁻ x, ‖ψ x‖ₑ ^ r) ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) hcstne)
      (ENNReal.mul_ne_top (by simp) (lintegral_enorm_rpow_sch_ne_top ψ hr0))
  refine ne_top_of_le_ne_top hfin ?_
  calc ∫⁻ x, (∑ j ∈ Fn n, hh α φ ψ j x ^ 2) ^ (r / 2)
      ≤ ∫⁻ x, cst ^ (r / 2) * Mx ψ x ^ r := by
        refine lintegral_mono fun x => ?_
        calc (∑ j ∈ Fn n, hh α φ ψ j x ^ 2) ^ (r / 2) ≤ (cst * Mx ψ x ^ 2) ^ (r / 2) :=
              ENNReal.rpow_le_rpow (hpt x) (by positivity)
          _ = cst ^ (r / 2) * Mx ψ x ^ r := by
              rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_natCast,
                ← ENNReal.rpow_mul]
              congr 2
              push_cast; ring
    _ = cst ^ (r / 2) * ∫⁻ x, Mx ψ x ^ r :=
        lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by positivity) hcstne)
    _ ≤ cst ^ (r / 2) * (CM * ∫⁻ x, ‖ψ x‖ₑ ^ r) :=
        mul_le_mul_right (hCM _ ψ.continuous.measurable.enorm) _

/-- **the Carleson endpoint estimate for `r > 2`** -/
theorem E4_gt (hd : 1 ≤ d) {r : ℝ} (hr : 2 < r) : E4At (d := d) α r := by
  set q : ℝ := r / 2 with hq
  have hq1 : 1 < q := by rw [hq]; linarith
  have hq0 : 0 < q := by linarith
  have hr0 : 0 < r := by linarith
  set t : ℝ := q.conjExponent with ht
  have hconj : q.HolderConjugate t := Real.HolderConjugate.conjExponent hq1
  have ht1 : 1 < t := (Real.holderConjugate_iff.1 hconj.symm).1
  obtain ⟨A0, hA0, hQw⟩ := Qw_bound α hd
  obtain ⟨CV, hCV, hV⟩ := V_bound hd ht1
  obtain ⟨CM, hCM⟩ := Mx_strong hd hq1
  refine ⟨(CV ^ (1 / t) * A0) ^ q * CM, ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hq0.le
    (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by positivity) hCV) hA0))
    (by simp), fun φ ψ => ?_⟩
  set Bn : ℝ≥0∞ := eLpNorm (⇑(Fm α φ)) ⊤ volume with hBn
  have hBnt : Bn ≠ ⊤ := eLpNorm_top_sch_ne_top _
  have hFB : ∀ x, ‖Fm α φ x‖ₑ ≤ Bn := fun x => enorm_le_eLpNorm_top _ x
  set g : 𝔼 → ℝ≥0∞ := fun z => ‖ψ z‖ₑ ^ 2 with hg
  have hgm : Measurable g := ψ.continuous.measurable.enorm.pow_const 2
  have hMg : Measurable (cmxHLS_Md g) := cmxHLS_Md_measurable hgm
  have hTm : ∀ n : ℕ, Measurable (fun x => ∑ j ∈ Fn n, hh α φ ψ j x ^ 2) := fun n =>
    Finset.measurable_sum _ fun j _ => (hh_meas α φ ψ j).pow_const 2
  have key : ∀ n : ℕ, ∫⁻ x, (∑ j ∈ Fn n, hh α φ ψ j x ^ 2) ^ q ≤
      (CV ^ (1 / t) * (A0 * Bn ^ 2)) ^ q * ∫⁻ x, cmxHLS_Md g x ^ q := by
    intro n
    have hfin : ∫⁻ x, (∑ j ∈ Fn n, hh α φ ψ j x ^ 2) ^ q ≠ ⊤ := Tn_fin α hd (by linarith) φ ψ n
    refine dual_gen (s := q) hq1 (fun w x => w x + cmxHLS_Md (cmxHLS_Md w) x)
      (fun w hw => hw.add (cmxHLS_Md_measurable (cmxHLS_Md_measurable hw))) hCV hV _ _ _ (hTm n)
      hMg hfin ?_
    intro w hw
    calc ∫⁻ x, (∑ j ∈ Fn n, hh α φ ψ j x ^ 2) * w x ≤ ∫⁻ x, QQ α φ ψ x * w x :=
          lintegral_mono fun x => mul_le_mul_left (by
            unfold QQ; exact ENNReal.sum_le_tsum _) _
      _ ≤ A0 * Bn ^ 2 * ∫⁻ x, (w x + cmxHLS_Md (cmxHLS_Md w) x) * cmxHLS_Md g x :=
          hQw φ ψ Bn hBnt hFB w hw
      _ = (A0 * Bn ^ 2) * ∫⁻ x, cmxHLS_Md g x * (w x + cmxHLS_Md (cmxHLS_Md w) x) := by
          congr 1
          exact lintegral_congr fun x => mul_comm _ _
  have hmono : Monotone (fun n : ℕ => fun x : 𝔼 => ∑ j ∈ Fn n, hh α φ ψ j x ^ 2) := by
    intro m n hmn x
    exact Finset.sum_le_sum_of_subset (Fn_mono hmn)
  have hsup : ∫⁻ x, QQ α φ ψ x ^ q =
      ⨆ n : ℕ, ∫⁻ x, (∑ j ∈ Fn n, hh α φ ψ j x ^ 2) ^ q := by
    rw [← lintegral_rpow_iSup hTm hmono hq0]
    refine lintegral_congr fun x => ?_
    unfold QQ
    rw [tsum_eq_iSup_Fn]
  have hq2 : r / 2 = q := rfl
  rw [hq2, hsup]
  refine iSup_le fun n => (key n).trans ?_
  have hgq : ∫⁻ x, g x ^ q = ∫⁻ x, ‖ψ x‖ₑ ^ r := by
    refine lintegral_congr fun x => ?_
    simp only [hg]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1; rw [hq]; push_cast; ring
  have hBq : (Bn ^ 2) ^ q = Bn ^ r := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    congr 1; rw [hq]; push_cast; ring
  calc (CV ^ (1 / t) * (A0 * Bn ^ 2)) ^ q * ∫⁻ x, cmxHLS_Md g x ^ q
      ≤ (CV ^ (1 / t) * (A0 * Bn ^ 2)) ^ q * (CM * ∫⁻ x, g x ^ q) :=
        mul_le_mul_right (hCM g hgm) _
    _ = ((CV ^ (1 / t) * A0) ^ q * CM) * (Bn ^ r * ∫⁻ x, ‖ψ x‖ₑ ^ r) := by
        rw [hgq, show CV ^ (1 / t) * (A0 * Bn ^ 2) = (CV ^ (1 / t) * A0) * Bn ^ 2 by ring,
          ENNReal.mul_rpow_of_nonneg _ _ hq0.le, hBq]
        ring

end E4

end HRS.Commutator.Whole.XLI
