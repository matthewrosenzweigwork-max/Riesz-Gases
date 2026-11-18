import HRS.Commutator.Whole.XLIAux32

/-!
# X-LI part 33: the weak type `(1,1)` estimate for square functions of Hörmander kernel families
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology SchwartzMap

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma vol_closedBall_mul8 (x : 𝔼) {r : ℝ} (hr : 0 ≤ r) :
    volume (closedBall x (8 * r)) = 8 ^ d * volume (closedBall x r) := by
  rw [cmxHLS_vol_closedBall x hr, cmxHLS_vol_closedBall x (by positivity), ← mul_assoc,
    mul_pow, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num)]
  simp

/-- the `L⁴`-estimate for the good part -/
lemma good_L2 {K : ℤ → 𝔼 → ℂ} (hKm : ∀ j, Measurable (K j)) {C4 : ℝ≥0}
    (hC4 : ∀ F : 𝔼 → ℂ, Measurable F → Integrable F → ∀ B : ℝ≥0∞, B ≠ ⊤ →
      (∀ x, ‖F x‖ₑ ≤ B) →
      ∫⁻ x, sqS (fun j => cv (K j) F) x ^ (2 : ℝ) ≤ C4 * ∫⁻ x, ‖F x‖ₑ ^ (2 * (2 : ℝ)))
    {g : 𝔼 → ℂ} (hgm : Measurable g) (hgi : Integrable g) {M : ℝ≥0∞} (hM : M ≠ ⊤)
    (hgb : ∀ x, ‖g x‖ₑ ≤ M) {t : ℝ≥0∞} (ht0 : t ≠ 0) (htt : t ≠ ⊤) :
    t ^ 2 * volume {x | t < sqS (fun j => cv (K j) g) x} ≤ C4 * (M ^ 3 * ∫⁻ x, ‖g x‖ₑ) := by
  have h1 := hC4 g hgm hgi M hM hgb
  have h2 : ∫⁻ x, ‖g x‖ₑ ^ (2 * (2 : ℝ)) ≤ M ^ 3 * ∫⁻ x, ‖g x‖ₑ := by
    rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top hM)]
    refine lintegral_mono fun x => ?_
    rw [show (2 * (2 : ℝ)) = ((4 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]
    calc ‖g x‖ₑ ^ 4 = ‖g x‖ₑ ^ 3 * ‖g x‖ₑ := by ring
      _ ≤ M ^ 3 * ‖g x‖ₑ := by gcongr; exact hgb x
  have hmeas : Measurable (fun x => sqS (fun j => cv (K j) g) x ^ (2 : ℝ)) :=
    (sqS_measurable (fun j => measurable_cv (hKm j) hgm)).pow_const _
  have hcheb := mul_meas_ge_le_lintegral₀ (μ := (volume : Measure 𝔼)) hmeas.aemeasurable (t ^ 2)
  have hsub : {x | t < sqS (fun j => cv (K j) g) x} ⊆
      {x | t ^ 2 ≤ sqS (fun j => cv (K j) g) x ^ (2 : ℝ)} := by
    intro x hx
    have : t ≤ sqS (fun j => cv (K j) g) x := hx.le
    show t ^ 2 ≤ _
    rw [ENNReal.rpow_two]; gcongr
  calc t ^ 2 * volume {x | t < sqS (fun j => cv (K j) g) x}
      ≤ t ^ 2 * volume {x | t ^ 2 ≤ sqS (fun j => cv (K j) g) x ^ (2 : ℝ)} :=
        mul_le_mul_right (measure_mono hsub) _
    _ ≤ ∫⁻ x, sqS (fun j => cv (K j) g) x ^ (2 : ℝ) := hcheb
    _ ≤ C4 * ∫⁻ x, ‖g x‖ₑ ^ (2 * (2 : ℝ)) := h1
    _ ≤ C4 * (M ^ 3 * ∫⁻ x, ‖g x‖ₑ) := mul_le_mul_right h2 _

lemma cheb_restrict {A : Set 𝔼} (hA : MeasurableSet A) {L : 𝔼 → ℝ≥0∞} (hL : Measurable L)
    (ε : ℝ≥0∞) : ε * volume (A ∩ {x | ε < L x}) ≤ ∫⁻ x in A, L x := by
  have h := mul_meas_ge_le_lintegral₀ (μ := (volume : Measure 𝔼).restrict A) hL.aemeasurable ε
  refine le_trans (mul_le_mul_right ?_ _) h
  rw [Measure.restrict_apply (measurableSet_le measurable_const hL)]
  exact measure_mono fun x hx => ⟨le_of_lt (show ε < L x from hx.2), hx.1⟩

/-- **weak type `(1,1)`** for the square function of a family satisfying Hörmander's condition
and an `L⁴`-bound -/
lemma cz_weak (hd : 1 ≤ d) {K : ℤ → 𝔼 → ℂ} (hKm : ∀ j, Measurable (K j))
    (hKi : ∀ j, Integrable (K j)) (h4 : E1At K 2) {H : ℝ≥0∞} (hH : H ≠ ⊤) (hHorm : HormK K H) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ F : 𝔼 → ℂ, Measurable F → Integrable F → ∀ B : ℝ≥0∞, B ≠ ⊤ →
      (∀ x, ‖F x‖ₑ ≤ B) → ∀ l : ℝ≥0∞, l ≠ 0 → l ≠ ⊤ →
        l * volume {x | l ^ 2 < sqS (fun j => cv (K j) F) x} ≤ C * ∫⁻ x, ‖F x‖ₑ := by
  obtain ⟨C4, hC4⟩ := h4
  refine ⟨16 * (4 ^ d) ^ 3 * (C4 : ℝ≥0∞) + 8 ^ d + 4 * H, ?_, fun F hF hFi B hB hFB l hl0 hlt => ?_⟩
  · refine ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨?_, ?_⟩, ?_⟩
    · exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp)
        (ENNReal.pow_ne_top (ENNReal.pow_ne_top (by simp)))) (by simp)
    · exact ENNReal.pow_ne_top (by simp)
    · exact ENNReal.mul_ne_top (by simp) hH
  set I : ℝ≥0∞ := ∫⁻ x, ‖F x‖ₑ with hI
  have hIt : I ≠ ⊤ := hFi.hasFiniteIntegral.ne
  obtain ⟨u, r, hucount, hrpos, hdisj, hsel, hnot, hcov⟩ := exists_balls hd hF.enorm hIt hl0 hlt
  obtain ⟨E, hEm, hEd, hBE, hEB, hcovE⟩ := exists_pieces hucount hrpos hdisj
  have hcu : Countable u := hucount.to_subtype
  set M : ℝ≥0∞ := 4 ^ d * l with hM
  have hMt : M ≠ ⊤ := ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp)) hlt
  have h4d : (1 : ℝ≥0∞) ≤ 4 ^ d := one_le_pow₀ (by norm_num)
  have hlM : l ≤ M := by
    rw [hM]; calc l = 1 * l := (one_mul l).symm
      _ ≤ 4 ^ d * l := mul_le_mul_left h4d _
  -- ball volumes
  have hvB0 : ∀ i : u, volume (closedBall (i : 𝔼) (r i)) ≠ 0 := fun i =>
    cmxHLS_vol_closedBall_ne_zero _ (hrpos i i.2)
  have hvBt : ∀ i : u, volume (closedBall (i : 𝔼) (r i)) ≠ ⊤ := fun i =>
    cmxHLS_vol_closedBall_ne_top _ _
  have hE0 : ∀ i : u, volume (E i) ≠ 0 := fun i =>
    (lt_of_lt_of_le (pos_iff_ne_zero.2 (hvB0 i)) (measure_mono (hBE i))).ne'
  have hEt : ∀ i : u, volume (E i) ≠ ⊤ := fun i =>
    ne_top_of_le_ne_top (cmxHLS_vol_closedBall_ne_top _ (4 * r i)) (measure_mono (hEB i))
  have hav : ∀ i : u, (volume (E i))⁻¹ * ∫⁻ y in E i, ‖F y‖ₑ ≤ M := by
    intro i
    have h1 : (volume (E i))⁻¹ ≤ (volume (closedBall (i : 𝔼) (r i)))⁻¹ :=
      ENNReal.inv_le_inv.2 (measure_mono (hBE i))
    have h2 : ∫⁻ y in E i, ‖F y‖ₑ ≤ l * (4 ^ d * volume (closedBall (i : 𝔼) (r i))) := by
      calc ∫⁻ y in E i, ‖F y‖ₑ ≤ ∫⁻ y in closedBall (i : 𝔼) (4 * r i), ‖F y‖ₑ :=
            lintegral_mono_set (hEB i)
        _ ≤ l * volume (closedBall (i : 𝔼) (4 * r i)) := hnot i i.2
        _ = _ := by rw [cmxHLS_vol_closedBall_mul4 _ (hrpos i i.2).le]
    calc (volume (E i))⁻¹ * ∫⁻ y in E i, ‖F y‖ₑ
        ≤ (volume (closedBall (i : 𝔼) (r i)))⁻¹ * (l * (4 ^ d * volume (closedBall (i : 𝔼) (r i)))) :=
          mul_le_mul' h1 h2
      _ = 4 ^ d * l := by
          rw [show l * (4 ^ d * volume (closedBall (i : 𝔼) (r i))) =
              (4 ^ d * l) * volume (closedBall (i : 𝔼) (r i)) by ring, ← mul_assoc,
            mul_comm _ (4 ^ d * l), mul_assoc, ENNReal.inv_mul_cancel (hvB0 i) (hvBt i), mul_one]
  obtain ⟨g, hgm, hgb, hgint, hmean, hgood⟩ :=
    good_function F hF hFi E hEm hEd hE0 hEt hlM hav
  set b : 𝔼 → ℂ := fun x => F x - g x with hb
  have hbm : Measurable b := hF.sub hgm
  have hgi : Integrable g := ⟨hgm.aestronglyMeasurable, by
    rw [hasFiniteIntegral_iff_enorm]; exact lt_of_le_of_lt hgint hIt.lt_top⟩
  have hbi : Integrable b := hFi.sub hgi
  have hnorm_le : ∀ (z : ℂ) (C : ℝ≥0∞), C ≠ ⊤ → ‖z‖ₑ ≤ C → ‖z‖ ≤ C.toReal := fun z C hC h => by
    rw [← ofReal_norm] at h; exact (ENNReal.ofReal_le_iff_le_toReal hC).1 h
  set Bb : ℝ := B.toReal + M.toReal with hBb
  have hBn : 0 ≤ B.toReal := ENNReal.toReal_nonneg
  have hMn : 0 ≤ M.toReal := ENNReal.toReal_nonneg
  have hFn : ∀ x, ‖F x‖ ≤ B.toReal := fun x => hnorm_le _ _ hB (hFB x)
  have hgn : ∀ x, ‖g x‖ ≤ M.toReal := fun x => hnorm_le _ _ hMt (hgb x)
  have hFB' : ∀ x, ‖F x‖ ≤ Bb := fun x => (hFn x).trans (by rw [hBb]; linarith)
  have hgB' : ∀ x, ‖g x‖ ≤ Bb := fun x => (hgn x).trans (by rw [hBb]; linarith)
  have hbB : ∀ x, ‖b x‖ ≤ Bb := fun x => (norm_sub_le _ _).trans (by
    have := hFn x; have := hgn x; rw [hBb]; linarith)
  have hb0 : ∀ᵐ y, y ∉ ⋃ i, E i → b y = 0 := by
    filter_upwards [ae_enorm_le_of_Md_le hFi hlt] with y hy hyΩ
    have hMd : cmxHLS_Md (fun x => ‖F x‖ₑ) y ≤ l := by
      by_contra h
      exact hyΩ (hcovE (hcov (not_le.1 h)))
    have := hgood y hyΩ (hy hMd)
    simp [hb, this]
  have hcvF : ∀ j x, cv (K j) F x = cv (K j) g x + cv (K j) b x := by
    intro j x
    have hFe : F = fun y => g y + b y := by funext y; simp [hb]
    rw [hFe]
    exact cv_add_of_bdd (hKi j) hgm hbm hgB' hbB x
  -- the half height
  obtain ⟨q, hq⟩ : ∃ q : ℝ≥0∞, l = 2 * q := ⟨l / 2, by
    rw [mul_comm]; exact (ENNReal.div_mul_cancel (by norm_num) (by simp)).symm⟩
  have hq0 : q ≠ 0 := by
    intro h; rw [h, mul_zero] at hq; exact hl0 hq
  have hqt : q ≠ ⊤ := by
    intro h; rw [h] at hq; simp at hq; exact hlt hq
  set Lb : 𝔼 → ℝ≥0∞ := fun x => ∑' j, ‖cv (K j) b x‖ₑ with hLb
  have hLbm : Measurable Lb := Measurable.tsum fun j => (measurable_cv (hKm j) hbm).enorm
  set A : Set 𝔼 := {x : 𝔼 | ∀ i : u, 2 * (4 * r i) ≤ ‖x - (i : 𝔼)‖} with hA
  have hAm : MeasurableSet A := by
    have : A = ⋂ i : u, {x : 𝔼 | 2 * (4 * r i) ≤ ‖x - (i : 𝔼)‖} := by
      ext x; simp [hA]
    rw [this]
    exact MeasurableSet.iInter fun i =>
      measurableSet_le measurable_const (measurable_norm.comp (measurable_id.sub_const _))
  set Ωs : Set 𝔼 := ⋃ i : u, closedBall (i : 𝔼) (8 * r i) with hΩs
  set G : Set 𝔼 := {x | q ^ 2 < sqS (fun j => cv (K j) g) x} with hG
  set Bd : Set 𝔼 := A ∩ {x | q < Lb x} with hBd
  have hsub : {x | l ^ 2 < sqS (fun j => cv (K j) F) x} ⊆ G ∪ Ωs ∪ Bd := by
    intro x hx
    by_contra hcon
    simp only [mem_union, not_or] at hcon
    obtain ⟨⟨hxG, hxΩ⟩, hxBd⟩ := hcon
    have hxA : x ∈ A := by
      intro i
      by_contra h
      apply hxΩ
      refine mem_iUnion.2 ⟨i, ?_⟩
      rw [mem_closedBall, dist_eq_norm]
      have := not_le.1 h
      linarith
    have hL : Lb x ≤ q := by
      by_contra h
      exact hxBd ⟨hxA, not_le.1 h⟩
    have hg1 : sqS (fun j => cv (K j) g) x ≤ q ^ 2 := not_lt.1 hxG
    have h1 := sqS_add_le (fun j => cv (K j) F) (fun j => cv (K j) g) (fun j => cv (K j) b)
      hcvF x
    have h2 := sqS_le_sq_tsum (fun j => cv (K j) b) x
    have h3 : sqS (fun j => cv (K j) b) x ≤ q ^ 2 :=
      h2.trans (by gcongr)
    have h4 : sqS (fun j => cv (K j) F) x ≤ l ^ 2 := by
      calc sqS (fun j => cv (K j) F) x ≤ 2 * sqS (fun j => cv (K j) g) x +
            2 * sqS (fun j => cv (K j) b) x := h1
        _ ≤ 2 * q ^ 2 + 2 * q ^ 2 := by gcongr
        _ = l ^ 2 := by rw [hq]; ring
    exact absurd hx (not_lt.2 h4)
  -- the good part
  have hVG : l * volume G ≤ 16 * (4 ^ d) ^ 3 * (C4 : ℝ≥0∞) * I := by
    have h1 := good_L2 hKm hC4 hgm hgi hMt hgb (t := q ^ 2) (pow_ne_zero 2 hq0)
      (ENNReal.pow_ne_top hqt)
    have h2 : (q ^ 2) ^ 2 * volume G ≤ (C4 : ℝ≥0∞) * (M ^ 3 * I) :=
      h1.trans (mul_le_mul_right (mul_le_mul_right hgint _) _)
    have hq3 : q ^ 3 ≠ 0 := pow_ne_zero 3 hq0
    have hq3t : q ^ 3 ≠ ⊤ := ENNReal.pow_ne_top hqt
    have h3 : q ^ 3 * (q * volume G) ≤ q ^ 3 * (8 * (C4 : ℝ≥0∞) * (4 ^ d) ^ 3 * I) := by
      calc q ^ 3 * (q * volume G) = (q ^ 2) ^ 2 * volume G := by ring
        _ ≤ (C4 : ℝ≥0∞) * (M ^ 3 * I) := h2
        _ = q ^ 3 * (8 * (C4 : ℝ≥0∞) * (4 ^ d) ^ 3 * I) := by rw [hM, hq]; ring
    have h4 : q * volume G ≤ 8 * (C4 : ℝ≥0∞) * (4 ^ d) ^ 3 * I :=
      (ENNReal.mul_le_mul_iff_right hq3 hq3t).1 h3
    calc l * volume G = 2 * (q * volume G) := by rw [hq]; ring
      _ ≤ 2 * (8 * (C4 : ℝ≥0∞) * (4 ^ d) ^ 3 * I) := mul_le_mul_right h4 _
      _ = 16 * (4 ^ d) ^ 3 * (C4 : ℝ≥0∞) * I := by ring
  -- the enlarged balls
  have hBdisj : Pairwise (Function.onFun Disjoint fun i : u => closedBall (i : 𝔼) (r i)) :=
    fun i j hij => hdisj i.2 j.2 (fun h => hij (Subtype.ext h))
  have hVΩ : l * volume Ωs ≤ 8 ^ d * I := by
    calc l * volume Ωs ≤ l * ∑' i : u, volume (closedBall (i : 𝔼) (8 * r i)) :=
          mul_le_mul_right (measure_iUnion_le _) _
      _ = 8 ^ d * ∑' i : u, l * volume (closedBall (i : 𝔼) (r i)) := by
          rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
          refine tsum_congr fun i => ?_
          rw [vol_closedBall_mul8 _ (hrpos i i.2).le]; ring
      _ ≤ 8 ^ d * ∑' i : u, ∫⁻ y in closedBall (i : 𝔼) (r i), ‖F y‖ₑ :=
          mul_le_mul_right (ENNReal.tsum_le_tsum fun i : u => hsel (i : 𝔼) i.2) _
      _ = 8 ^ d * ∫⁻ y in ⋃ i : u, closedBall (i : 𝔼) (r i), ‖F y‖ₑ := by
          rw [lintegral_iUnion (fun i => measurableSet_closedBall) hBdisj]
      _ ≤ 8 ^ d * I := mul_le_mul_right (setLIntegral_le_lintegral _ _) _
  -- the bad part
  have hbI : ∫⁻ y in ⋃ i, E i, ‖b y‖ₑ ≤ 2 * I := by
    calc ∫⁻ y in ⋃ i, E i, ‖b y‖ₑ ≤ ∫⁻ y, ‖b y‖ₑ := setLIntegral_le_lintegral _ _
      _ ≤ ∫⁻ y, (‖F y‖ₑ + ‖g y‖ₑ) := lintegral_mono fun y => enorm_sub_le
      _ = I + ∫⁻ y, ‖g y‖ₑ := lintegral_add_left hF.enorm _
      _ ≤ I + I := add_le_add le_rfl hgint
      _ = 2 * I := by ring
  have hVBd : l * volume Bd ≤ 4 * H * I := by
    have h1 := cheb_restrict hAm hLbm q
    have h2 := bad_integral hKm hKi hHorm E hEm hEd (fun i : u => (i : 𝔼)) (fun i : u => 4 * r i)
      (fun i y hy => by
        have := hEB i hy
        rw [mem_closedBall, dist_eq_norm] at this
        exact this) hbm hbi hbB hb0 hmean
    have h3 : q * volume Bd ≤ H * (2 * I) := by
      refine h1.trans (h2.trans ?_)
      exact mul_le_mul_right hbI _
    calc l * volume Bd = 2 * (q * volume Bd) := by rw [hq]; ring
      _ ≤ 2 * (H * (2 * I)) := mul_le_mul_right h3 _
      _ = 4 * H * I := by ring
  calc l * volume {x | l ^ 2 < sqS (fun j => cv (K j) F) x}
      ≤ l * volume (G ∪ Ωs ∪ Bd) := mul_le_mul_right (measure_mono hsub) _
    _ ≤ l * (volume G + volume Ωs + volume Bd) :=
        mul_le_mul_right ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)) _
    _ = l * volume G + l * volume Ωs + l * volume Bd := by ring
    _ ≤ 16 * (4 ^ d) ^ 3 * (C4 : ℝ≥0∞) * I + 8 ^ d * I + 4 * H * I :=
        add_le_add (add_le_add hVG hVΩ) hVBd
    _ = (16 * (4 ^ d) ^ 3 * (C4 : ℝ≥0∞) + 8 ^ d + 4 * H) * I := by ring

end HRS.Commutator.Whole.XLI
