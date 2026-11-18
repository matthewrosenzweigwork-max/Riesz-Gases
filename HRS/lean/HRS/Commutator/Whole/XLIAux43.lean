import HRS.Commutator.Whole.XLIAux42

/-!
# X-LI part 43: the Carleson endpoint estimate `E4At` for `1 < r ≤ 2`
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution Topology SchwartzMap

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma real_pt_ineq {a n K : ℝ} (ha : 0 < a) (hn : 0 < n) (hK : 0 < K) (h : a ≤ K * n) {r : ℝ}
    (hr2 : r ≤ 2) : a ^ 2 * n ^ (r - 2) ≤ K ^ (2 - r) * a ^ r := by
  have haK : a / K ≤ n := by rw [div_le_iff₀ hK]; linarith
  have h1 : n ^ (r - 2) ≤ (a / K) ^ (r - 2) :=
    Real.rpow_le_rpow_of_nonpos (div_pos ha hK) haK (by linarith)
  have h2 : (a / K) ^ (r - 2) = a ^ (r - 2) * K ^ (2 - r) := by
    rw [Real.div_rpow ha.le hK.le, div_eq_mul_inv, ← Real.rpow_neg hK.le]
    congr 2; ring
  have h3 : a ^ 2 * a ^ (r - 2) = a ^ r := by
    rw [← Real.rpow_natCast, ← Real.rpow_add ha]
    congr 1; push_cast; ring
  calc a ^ 2 * n ^ (r - 2) ≤ a ^ 2 * (a ^ (r - 2) * K ^ (2 - r)) := by
        rw [← h2]; gcongr
    _ = K ^ (2 - r) * a ^ r := by rw [← h3]; ring

lemma enn_pt_ineq {a n K : ℝ≥0∞} (hK0 : K ≠ 0) (hKt : K ≠ ⊤) (hn : n ≠ ⊤) (h : a ≤ K * n)
    {r : ℝ} (hr2 : r ≤ 2) (hr1 : 0 < r) : a ^ 2 * n ^ (r - 2) ≤ K ^ (2 - r) * a ^ r := by
  by_cases ha0 : a = 0
  · subst ha0; simp
  have hat : a ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top hKt hn) h
  by_cases hn0 : n = 0
  · subst hn0
    simp at h
    exact absurd h ha0
  have ha' : 0 < a.toReal := ENNReal.toReal_pos ha0 hat
  have hn' : 0 < n.toReal := ENNReal.toReal_pos hn0 hn
  have hK' : 0 < K.toReal := ENNReal.toReal_pos hK0 hKt
  have h' : a.toReal ≤ K.toReal * n.toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top hKt hn) h
    rwa [ENNReal.toReal_mul] at this
  have hr := real_pt_ineq ha' hn' hK' h' hr2
  have e : a = ENNReal.ofReal a.toReal := (ENNReal.ofReal_toReal hat).symm
  have e2 : n = ENNReal.ofReal n.toReal := (ENNReal.ofReal_toReal hn).symm
  have e3 : K = ENNReal.ofReal K.toReal := (ENNReal.ofReal_toReal hKt).symm
  have hle := ENNReal.ofReal_le_ofReal hr
  rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_rpow_of_pos hn', ← ENNReal.ofReal_rpow_of_pos hK', ← ENNReal.ofReal_rpow_of_pos ha',
    ENNReal.ofReal_pow ha'.le] at hle
  rw [ENNReal.ofReal_toReal hat, ENNReal.ofReal_toReal hn, ENNReal.ofReal_toReal hKt] at hle
  exact hle

section E4le

variable (α : ℝ)

lemma Mx_ne_top (ψ : SchwartzMap 𝔼 ℂ) (y : 𝔼) : Mx ψ y ≠ ⊤ := by
  obtain ⟨B, hB, hBd⟩ := sch_enorm_bdd ψ
  exact ne_top_of_le_ne_top hB (Md_le_of_le (f := fun z => ‖ψ z‖ₑ) hBd y)

lemma Gs_rpow_le (ψ : SchwartzMap 𝔼 ℂ) {r : ℝ} (hr : 0 ≤ r) (j : ℤ) (y : 𝔼) :
    Gs ψ j y ^ r ≤ 4 ^ r * (Gc ψ (j + -3) y ^ r + Gc ψ (j + -2) y ^ r + Gc ψ (j + -1) y ^ r +
      Gc ψ j y ^ r) := by
  unfold Gs
  set a := Gc ψ (j + -3) y
  set b := Gc ψ (j + -2) y
  set c := Gc ψ (j + -1) y
  set e := Gc ψ j y
  have h2 : (2 : ℝ≥0∞) ^ r * 2 ^ r = 4 ^ r := by
    rw [← ENNReal.mul_rpow_of_nonneg _ _ hr]; norm_num
  calc (a + b + c + e) ^ r = ((a + b) + (c + e)) ^ r := by ring_nf
    _ ≤ 2 ^ r * ((a + b) ^ r + (c + e) ^ r) := rpow_add_le_two hr _ _
    _ ≤ 2 ^ r * (2 ^ r * (a ^ r + b ^ r) + 2 ^ r * (c ^ r + e ^ r)) := by
        gcongr
        · exact rpow_add_le_two hr _ _
        · exact rpow_add_le_two hr _ _
    _ = 4 ^ r * (a ^ r + b ^ r + c ^ r + e ^ r) := by
        rw [← h2]; ring

lemma QN_bound (hd : 1 ≤ d) {r : ℝ} (hr1 : 1 < r) (hr2 : r ≤ 2) :
    ∃ A2 : ℝ≥0∞, A2 ≠ ⊤ ∧ ∀ (φ ψ : SchwartzMap 𝔼 ℂ) (B : ℝ≥0∞), B ≠ ⊤ →
      (∀ x, ‖Fm α φ x‖ₑ ≤ B) →
      ∫⁻ x, QQ α φ ψ x * Mx ψ x ^ (r - 2) ≤ A2 * B ^ 2 * ∫⁻ x, Mx ψ x ^ r := by
  obtain ⟨Cc, hCc, hcar⟩ := carleson_embed hd (isLPRep_Ths (d := d) (-α))
  have hr0 : 0 < r := by linarith
  set K4 : ℝ≥0∞ := 4 * KP d with hK4
  have hK40 : K4 ≠ 0 := mul_ne_zero (by simp) (by
    unfold KP
    exact (ENNReal.mul_pos (by simp) (measure_closedBall_pos volume _ one_pos).ne').ne')
  have hK4t : K4 ≠ ⊤ := ENNReal.mul_ne_top (by simp) KP_ne_top
  have hKP0 : KP d ≠ 0 := by
    unfold KP
    exact (ENNReal.mul_pos (by simp) (measure_closedBall_pos volume _ one_pos).ne').ne'
  refine ⟨K4 ^ (2 - r) * 4 ^ r * (Cc * ((2 ^ (d + 1) * KP d) ^ r * 2)) * 4, ?_, fun φ ψ B hB hFB => ?_⟩
  · refine ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by linarith) hK4t)
      (ENNReal.rpow_ne_top_of_nonneg hr0.le (by simp))) (ENNReal.mul_ne_top hCc
      (ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hr0.le
        (ENNReal.mul_ne_top (ENNReal.pow_ne_top (by simp)) KP_ne_top)) (by simp)))) (by simp)
  set f : 𝔼 → ℝ≥0∞ := fun z => ‖ψ z‖ₑ with hf
  have hfm : Measurable f := ψ.continuous.measurable.enorm
  have hfi : ∫⁻ y, f y ≠ ⊤ := by
    simpa [hf] using (ψ.integrable.hasFiniteIntegral.ne)
  have hMx : Measurable (Mx ψ) := Mx_meas ψ
  have hFjm : ∀ j, Measurable (fun x => ‖Fj α φ j x‖ₑ ^ 2) := fun j =>
    (Fj_meas α φ j).enorm.pow_const 2
  -- the embedding for the four shifts
  have hemb : ∀ s : ℤ, s ≤ 0 →
      ∑' j, ∫⁻ x, ‖Fj α φ j x‖ₑ ^ 2 * Gc ψ (j + s) x ^ r ≤
        Cc * B ^ 2 * ((2 ^ (d + 1) * KP d) ^ r * 2 * ∫⁻ x, Mx ψ x ^ r) := by
    intro s hs
    have h := hcar (⇑(Fm α φ)) (Fm α φ).continuous.measurable (Fm α φ).integrable B hB hFB f hfm
      hfi (fun j => CvP (j + s) f) (KP d) KP_ne_top hKP0
      (fun j => CvP_measurable _ hfm)
      (fun j x y hxy => CvP_shift (j + s) hfm (lt_of_lt_of_le hxy
        (zpow_le_zpow_right₀ (by norm_num) (by omega))))
      (fun j y => CvP_le _ hfm y) r hr0 (fun _ => 1) measurable_const
    have hw : ∫⁻ x, (1 + cmxHLS_Md (cmxHLS_Md (fun _ : 𝔼 => (1 : ℝ≥0∞))) x) *
        cmxHLS_Md f x ^ r ≤ 2 * ∫⁻ x, Mx ψ x ^ r := by
      rw [← lintegral_const_mul _ (hMx.pow_const r)]
      refine lintegral_mono fun x => ?_
      have h1 : cmxHLS_Md (cmxHLS_Md (fun _ : 𝔼 => (1 : ℝ≥0∞))) x ≤ 1 :=
        Md_le_of_le (fun y => Md_one_le y) x
      calc (1 + cmxHLS_Md (cmxHLS_Md (fun _ : 𝔼 => (1 : ℝ≥0∞))) x) * cmxHLS_Md f x ^ r
          ≤ (1 + 1) * cmxHLS_Md f x ^ r := by gcongr
        _ = 2 * Mx ψ x ^ r := by norm_num [Mx, hf]
    simp only [mul_one] at h
    calc ∑' j, ∫⁻ x, ‖Fj α φ j x‖ₑ ^ 2 * Gc ψ (j + s) x ^ r
        ≤ Cc * B ^ 2 * ((2 ^ (d + 1) * KP d) ^ r *
            ∫⁻ x, (1 + cmxHLS_Md (cmxHLS_Md (fun _ : 𝔼 => (1 : ℝ≥0∞))) x) * cmxHLS_Md f x ^ r) := h
      _ ≤ Cc * B ^ 2 * ((2 ^ (d + 1) * KP d) ^ r * (2 * ∫⁻ x, Mx ψ x ^ r)) :=
          mul_le_mul_right (mul_le_mul_right hw _) _
      _ = _ := by ring
  have hpt : ∀ x, QQ α φ ψ x * Mx ψ x ^ (r - 2) ≤
      ∑' j, ‖Fj α φ j x‖ₑ ^ 2 * (K4 ^ (2 - r) * 4 ^ r *
        (Gc ψ (j + -3) x ^ r + Gc ψ (j + -2) x ^ r + Gc ψ (j + -1) x ^ r + Gc ψ j x ^ r)) := by
    intro x
    unfold QQ
    rw [← ENNReal.tsum_mul_right]
    refine ENNReal.tsum_le_tsum fun j => ?_
    unfold hh
    rw [mul_pow, mul_assoc]
    refine mul_le_mul_right ?_ _
    have h1 := enn_pt_ineq hK40 hK4t (Mx_ne_top ψ x) (a := Gs ψ j x) (by
      calc Gs ψ j x ≤ 4 * (KP d * Mx ψ x) := Gs_le ψ j x
        _ = K4 * Mx ψ x := by rw [hK4]; ring) hr2 hr0
    refine h1.trans ?_
    calc K4 ^ (2 - r) * Gs ψ j x ^ r ≤ K4 ^ (2 - r) * (4 ^ r * (Gc ψ (j + -3) x ^ r +
          Gc ψ (j + -2) x ^ r + Gc ψ (j + -1) x ^ r + Gc ψ j x ^ r)) :=
          mul_le_mul_right (Gs_rpow_le ψ hr0.le j x) _
      _ = _ := by ring
  have hem3 := hemb (-3) (by norm_num)
  have hem2 := hemb (-2) (by norm_num)
  have hem1 := hemb (-1) (by norm_num)
  have hem0 := hemb 0 le_rfl
  simp only [add_zero] at hem0
  have hGc : ∀ l : ℤ, Measurable (Gc ψ l) := fun l => Gc_meas ψ l
  have hper : ∀ j, ∫⁻ x, ‖Fj α φ j x‖ₑ ^ 2 * (K4 ^ (2 - r) * 4 ^ r *
        (Gc ψ (j + -3) x ^ r + Gc ψ (j + -2) x ^ r + Gc ψ (j + -1) x ^ r + Gc ψ j x ^ r)) =
      K4 ^ (2 - r) * 4 ^ r * ((∫⁻ x, ‖Fj α φ j x‖ₑ ^ 2 * Gc ψ (j + -3) x ^ r) +
        (∫⁻ x, ‖Fj α φ j x‖ₑ ^ 2 * Gc ψ (j + -2) x ^ r) +
        (∫⁻ x, ‖Fj α φ j x‖ₑ ^ 2 * Gc ψ (j + -1) x ^ r) +
        ∫⁻ x, ‖Fj α φ j x‖ₑ ^ 2 * Gc ψ j x ^ r) := by
    intro j
    have m3 : Measurable (fun x => ‖Fj α φ j x‖ₑ ^ 2 * Gc ψ (j + -3) x ^ r) :=
      (hFjm j).mul ((hGc _).pow_const r)
    have m2 : Measurable (fun x => ‖Fj α φ j x‖ₑ ^ 2 * Gc ψ (j + -2) x ^ r) :=
      (hFjm j).mul ((hGc _).pow_const r)
    have m1 : Measurable (fun x => ‖Fj α φ j x‖ₑ ^ 2 * Gc ψ (j + -1) x ^ r) :=
      (hFjm j).mul ((hGc _).pow_const r)
    have m0 : Measurable (fun x => ‖Fj α φ j x‖ₑ ^ 2 * Gc ψ j x ^ r) :=
      (hFjm j).mul ((hGc _).pow_const r)
    have m32 : Measurable (fun x => ‖Fj α φ j x‖ₑ ^ 2 * Gc ψ (j + -3) x ^ r +
        ‖Fj α φ j x‖ₑ ^ 2 * Gc ψ (j + -2) x ^ r) := m3.add m2
    have m321 : Measurable (fun x => ‖Fj α φ j x‖ₑ ^ 2 * Gc ψ (j + -3) x ^ r +
        ‖Fj α φ j x‖ₑ ^ 2 * Gc ψ (j + -2) x ^ r + ‖Fj α φ j x‖ₑ ^ 2 * Gc ψ (j + -1) x ^ r) :=
      m32.add m1
    have m3210 : Measurable (fun x => ‖Fj α φ j x‖ₑ ^ 2 * Gc ψ (j + -3) x ^ r +
        ‖Fj α φ j x‖ₑ ^ 2 * Gc ψ (j + -2) x ^ r + ‖Fj α φ j x‖ₑ ^ 2 * Gc ψ (j + -1) x ^ r +
        ‖Fj α φ j x‖ₑ ^ 2 * Gc ψ j x ^ r) := m321.add m0
    have e : ∀ x, ‖Fj α φ j x‖ₑ ^ 2 * (K4 ^ (2 - r) * 4 ^ r *
        (Gc ψ (j + -3) x ^ r + Gc ψ (j + -2) x ^ r + Gc ψ (j + -1) x ^ r + Gc ψ j x ^ r)) =
        K4 ^ (2 - r) * 4 ^ r * (‖Fj α φ j x‖ₑ ^ 2 * Gc ψ (j + -3) x ^ r +
        ‖Fj α φ j x‖ₑ ^ 2 * Gc ψ (j + -2) x ^ r + ‖Fj α φ j x‖ₑ ^ 2 * Gc ψ (j + -1) x ^ r +
        ‖Fj α φ j x‖ₑ ^ 2 * Gc ψ j x ^ r) := fun x => by ring
    simp_rw [e]
    rw [lintegral_const_mul _ m3210, lintegral_add_left m321, lintegral_add_left m32,
      lintegral_add_left m3]
  have hmeasj : ∀ j, Measurable (fun x => ‖Fj α φ j x‖ₑ ^ 2 * (K4 ^ (2 - r) * 4 ^ r *
        (Gc ψ (j + -3) x ^ r + Gc ψ (j + -2) x ^ r + Gc ψ (j + -1) x ^ r + Gc ψ j x ^ r))) := by
    intro j
    exact (hFjm j).mul (measurable_const.mul ((((hGc _).pow_const r).add ((hGc _).pow_const r)).add
      ((hGc _).pow_const r) |>.add ((hGc _).pow_const r)))
  calc ∫⁻ x, QQ α φ ψ x * Mx ψ x ^ (r - 2)
      ≤ ∫⁻ x, ∑' j, ‖Fj α φ j x‖ₑ ^ 2 * (K4 ^ (2 - r) * 4 ^ r *
        (Gc ψ (j + -3) x ^ r + Gc ψ (j + -2) x ^ r + Gc ψ (j + -1) x ^ r + Gc ψ j x ^ r)) :=
        lintegral_mono hpt
    _ = ∑' j, ∫⁻ x, ‖Fj α φ j x‖ₑ ^ 2 * (K4 ^ (2 - r) * 4 ^ r *
        (Gc ψ (j + -3) x ^ r + Gc ψ (j + -2) x ^ r + Gc ψ (j + -1) x ^ r + Gc ψ j x ^ r)) := by
        rw [lintegral_tsum]
        intro j; exact (hmeasj j).aemeasurable
    _ = ∑' j, K4 ^ (2 - r) * 4 ^ r * ((∫⁻ x, ‖Fj α φ j x‖ₑ ^ 2 * Gc ψ (j + -3) x ^ r) +
        (∫⁻ x, ‖Fj α φ j x‖ₑ ^ 2 * Gc ψ (j + -2) x ^ r) +
        (∫⁻ x, ‖Fj α φ j x‖ₑ ^ 2 * Gc ψ (j + -1) x ^ r) +
        ∫⁻ x, ‖Fj α φ j x‖ₑ ^ 2 * Gc ψ j x ^ r) := tsum_congr hper
    _ = K4 ^ (2 - r) * 4 ^ r * ((∑' j, ∫⁻ x, ‖Fj α φ j x‖ₑ ^ 2 * Gc ψ (j + -3) x ^ r) +
        (∑' j, ∫⁻ x, ‖Fj α φ j x‖ₑ ^ 2 * Gc ψ (j + -2) x ^ r) +
        (∑' j, ∫⁻ x, ‖Fj α φ j x‖ₑ ^ 2 * Gc ψ (j + -1) x ^ r) +
        ∑' j, ∫⁻ x, ‖Fj α φ j x‖ₑ ^ 2 * Gc ψ j x ^ r) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_add]
    _ ≤ K4 ^ (2 - r) * 4 ^ r * (Cc * B ^ 2 * ((2 ^ (d + 1) * KP d) ^ r * 2 * ∫⁻ x, Mx ψ x ^ r) +
        Cc * B ^ 2 * ((2 ^ (d + 1) * KP d) ^ r * 2 * ∫⁻ x, Mx ψ x ^ r) +
        Cc * B ^ 2 * ((2 ^ (d + 1) * KP d) ^ r * 2 * ∫⁻ x, Mx ψ x ^ r) +
        Cc * B ^ 2 * ((2 ^ (d + 1) * KP d) ^ r * 2 * ∫⁻ x, Mx ψ x ^ r)) := by
        gcongr
    _ = _ := by ring

lemma QQ_meas (φ ψ : SchwartzMap 𝔼 ℂ) : Measurable (QQ α φ ψ) := by
  unfold QQ
  exact Measurable.tsum fun j => (hh_meas α φ ψ j).pow_const 2

lemma QQ_eq_zero_of_Mx (φ ψ : SchwartzMap 𝔼 ℂ) {x : 𝔼} (hx : Mx ψ x = 0) : QQ α φ ψ x = 0 := by
  unfold QQ
  refine ENNReal.tsum_eq_zero.2 fun j => ?_
  have : Gs ψ j x = 0 := by
    have := Gs_le ψ j x
    rw [hx] at this
    simpa using this
  unfold hh
  rw [this]; simp

lemma Q_pt (φ ψ : SchwartzMap 𝔼 ℂ) {r : ℝ} (hr0 : 0 < r) (hr2 : r < 2) (x : 𝔼) :
    QQ α φ ψ x ^ (r / 2) ≤ (QQ α φ ψ x * Mx ψ x ^ (r - 2)) ^ (r / 2) * Mx ψ x ^ ((2 - r) * (r / 2)) := by
  by_cases hx : Mx ψ x = 0
  · rw [QQ_eq_zero_of_Mx α φ ψ hx, ENNReal.zero_rpow_of_pos (by positivity)]
    exact zero_le
  · have hxt := Mx_ne_top ψ x
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul, mul_assoc,
      ← ENNReal.rpow_add _ _ hx hxt]
    have : (r - 2) * (r / 2) + (2 - r) * (r / 2) = 0 := by ring
    rw [this, ENNReal.rpow_zero, mul_one]

/-- **the Carleson endpoint estimate for `1 < r ≤ 2`** -/
theorem E4_le (hd : 1 ≤ d) {r : ℝ} (hr1 : 1 < r) (hr2 : r ≤ 2) : E4At (d := d) α r := by
  have hr0 : 0 < r := by linarith
  obtain ⟨A2, hA2, hQN⟩ := QN_bound α hd hr1 hr2
  obtain ⟨CM, hCM⟩ := Mx_strong hd hr1
  rcases hr2.eq_or_lt with h2 | h2
  · -- `r = 2`
    subst h2
    refine ⟨A2 * CM, ENNReal.mul_ne_top hA2 (by simp), fun φ ψ => ?_⟩
    set Bn : ℝ≥0∞ := eLpNorm (⇑(Fm α φ)) ⊤ volume with hBn
    have hBnt : Bn ≠ ⊤ := eLpNorm_top_sch_ne_top _
    have hFB : ∀ x, ‖Fm α φ x‖ₑ ≤ Bn := fun x => enorm_le_eLpNorm_top _ x
    have h1 := hQN φ ψ Bn hBnt hFB
    have h3 : ∫⁻ x, Mx ψ x ^ (2 : ℝ) ≤ CM * ∫⁻ x, ‖ψ x‖ₑ ^ (2 : ℝ) :=
      hCM _ ψ.continuous.measurable.enorm
    calc ∫⁻ x, QQ α φ ψ x ^ ((2 : ℝ) / 2) = ∫⁻ x, QQ α φ ψ x * Mx ψ x ^ ((2 : ℝ) - 2) := by
          refine lintegral_congr fun x => ?_
          norm_num
      _ ≤ A2 * Bn ^ 2 * ∫⁻ x, Mx ψ x ^ (2 : ℝ) := h1
      _ ≤ A2 * Bn ^ 2 * (CM * ∫⁻ x, ‖ψ x‖ₑ ^ (2 : ℝ)) := mul_le_mul_right h3 _
      _ = (A2 * CM) * (Bn ^ (2 : ℝ) * ∫⁻ x, ‖ψ x‖ₑ ^ (2 : ℝ)) := by
          rw [ENNReal.rpow_two]; ring
  · -- `r < 2`
    set q : ℝ := r / 2 with hq
    have hq0 : 0 < q := by rw [hq]; positivity
    refine ⟨A2 ^ q * CM, ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hq0.le hA2)
      (by simp), fun φ ψ => ?_⟩
    set Bn : ℝ≥0∞ := eLpNorm (⇑(Fm α φ)) ⊤ volume with hBn
    have hBnt : Bn ≠ ⊤ := eLpNorm_top_sch_ne_top _
    have hFB : ∀ x, ‖Fm α φ x‖ₑ ≤ Bn := fun x => enorm_le_eLpNorm_top _ x
    have h1 := hQN φ ψ Bn hBnt hFB
    set I : ℝ≥0∞ := ∫⁻ x, Mx ψ x ^ r with hI
    have hIM : I ≤ CM * ∫⁻ x, ‖ψ x‖ₑ ^ r := hCM _ ψ.continuous.measurable.enorm
    have hXm : Measurable (fun x => QQ α φ ψ x * Mx ψ x ^ (r - 2)) :=
      (QQ_meas α φ ψ).mul ((Mx_meas ψ).pow_const _)
    have hsum : q / 1 + (2 - r) * q / r = 1 := by
      rw [hq]; field_simp; ring
    have hH := holder_pow hXm (Mx_meas ψ) (s := q) (p := 1) (q := r) (t := (2 - r) * q)
      hq0 (by rw [hq]; have : 0 < 2 - r := by linarith
              positivity) one_pos hr0 hsum
    have e1 : (2 - r) * q / r = 1 - q := by rw [hq]; field_simp
    rw [e1] at hH
    simp only [ENNReal.rpow_one, div_one] at hH
    calc ∫⁻ x, QQ α φ ψ x ^ q ≤ ∫⁻ x, (QQ α φ ψ x * Mx ψ x ^ (r - 2)) ^ q *
          Mx ψ x ^ ((2 - r) * q) := lintegral_mono fun x => Q_pt α φ ψ hr0 h2 x
      _ ≤ (∫⁻ x, QQ α φ ψ x * Mx ψ x ^ (r - 2)) ^ q * I ^ (1 - q) := hH
      _ ≤ (A2 * Bn ^ 2 * I) ^ q * I ^ (1 - q) := by
          gcongr
      _ = A2 ^ q * Bn ^ r * I := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hq0.le, ENNReal.mul_rpow_of_nonneg _ _ hq0.le,
            ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
          have e2 : (((2 : ℕ) : ℝ) * q) = r := by rw [hq]; push_cast; ring
          rw [e2]
          have e3 : I ^ q * I ^ (1 - q) = I := by
            rw [← ENNReal.rpow_add_of_nonneg _ _ hq0.le (by rw [hq]; linarith)]
            simp
          calc A2 ^ q * Bn ^ r * I ^ q * I ^ (1 - q) = A2 ^ q * Bn ^ r * (I ^ q * I ^ (1 - q)) := by ring
            _ = _ := by rw [e3]
      _ ≤ A2 ^ q * Bn ^ r * (CM * ∫⁻ x, ‖ψ x‖ₑ ^ r) := mul_le_mul_right hIM _
      _ = (A2 ^ q * CM) * (Bn ^ r * ∫⁻ x, ‖ψ x‖ₑ ^ r) := by ring

end E4le

end HRS.Commutator.Whole.XLI
