import HRS.Commutator.Whole.XLIAux2

/-!
# X-LI part 3: the vector-valued Fefferman–Stein inequality for dominated kernels, all `1 < p < ∞`
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal FourierTransform ContDiff Convolution

noncomputable section

namespace HRS.Commutator.Whole.XLI

open HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- subadditivity of `t ↦ t^s` for `s ≤ 1` over finite sums -/
lemma rpow_finsum_le {ι : Type*} {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (F : Finset ι)
    (f : ι → ℝ≥0∞) : (∑ i ∈ F, f i) ^ s ≤ ∑ i ∈ F, f i ^ s := by
  classical
  induction F using Finset.induction_on with
  | empty => simp [ENNReal.zero_rpow_of_pos hs0]
  | insert a F ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (ENNReal.rpow_add_le_add_rpow _ _ hs0.le hs1).trans (by gcongr)

lemma CvP_one_le (j : ℤ) (z : 𝔼) : CvP j (fun _ => (1 : ℝ≥0∞)) z ≤ KP d := by
  unfold CvP
  simpa using lintegral_Phi_le_KP (d := d) j

lemma CvP_sq_le (j : ℤ) {H : 𝔼 → ℝ≥0∞} (hH : Measurable H) (x : 𝔼) :
    CvP j H x ^ 2 ≤ KP d * CvP j (fun y => H y ^ 2) x := by
  unfold CvP
  have hm : AEMeasurable (fun y => H (x - y)) volume :=
    (hH.comp (measurable_const.sub measurable_id)).aemeasurable
  have := sq_lintegral_le volume (Phi_measurable j).aemeasurable hm
  exact this.trans (mul_le_mul' (lintegral_Phi_le_KP j) le_rfl)

/-- positive `ℓ²` Fefferman–Stein, exponent `s > 1` -/
lemma E3pos_gt (hd : 1 ≤ d) {s : ℝ} (hs : 1 < s) :
    ∃ C : ℝ≥0, ∀ H : ℤ → 𝔼 → ℝ≥0∞, (∀ j, Measurable (H j)) →
      ∫⁻ x, (∑' j, CvP j (H j) x ^ 2) ^ s ≤ C * ∫⁻ x, (∑' j, H j x ^ 2) ^ s := by
  have hs0 : 0 < s := by linarith
  obtain ⟨C, hC⟩ := conv_pos_strong hd hs
  refine ⟨((KP d) ^ s * C).toNNReal, fun H hH => ?_⟩
  have hfin : (KP d) ^ s * C ≠ ⊤ :=
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hs0.le KP_ne_top) ENNReal.coe_ne_top
  rw [ENNReal.coe_toNNReal hfin]
  have hpt : ∀ x, ∑' j, CvP j (H j) x ^ 2 ≤ KP d * ∑' j, CvP j (fun y => H j y ^ 2) x := by
    intro x
    rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun j => CvP_sq_le j (hH j) x
  calc ∫⁻ x, (∑' j, CvP j (H j) x ^ 2) ^ s
      ≤ ∫⁻ x, (KP d * ∑' j, CvP j (fun y => H j y ^ 2) x) ^ s :=
        lintegral_mono fun x => ENNReal.rpow_le_rpow (hpt x) hs0.le
    _ = ∫⁻ x, (KP d) ^ s * (∑' j, CvP j (fun y => H j y ^ 2) x) ^ s :=
        lintegral_congr fun x => ENNReal.mul_rpow_of_nonneg _ _ hs0.le
    _ = (KP d) ^ s * ∫⁻ x, (∑' j, CvP j (fun y => H j y ^ 2) x) ^ s :=
        lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hs0.le KP_ne_top)
    _ ≤ (KP d) ^ s * (C * ∫⁻ x, (∑' j, H j x ^ 2) ^ s) := by
        gcongr
        exact hC (fun j y => H j y ^ 2) (fun j => (hH j).pow_const 2)
    _ = _ := by rw [← mul_assoc]

/-- positive `ℓ²` Fefferman–Stein at the exponent `s = 1` (`p = 2`) -/
lemma E3pos_one :
    ∀ H : ℤ → 𝔼 → ℝ≥0∞, (∀ j, Measurable (H j)) →
      ∫⁻ x, ∑' j, CvP j (H j) x ^ 2 ≤ (KP d * KP d) * ∫⁻ x, ∑' j, H j x ^ 2 := by
  intro H hH
  have hpt : ∀ x, ∑' j, CvP j (H j) x ^ 2 ≤ KP d * ∑' j, CvP j (fun y => H j y ^ 2) x := by
    intro x
    rw [← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun j => CvP_sq_le j (hH j) x
  calc ∫⁻ x, ∑' j, CvP j (H j) x ^ 2 ≤ ∫⁻ x, KP d * ∑' j, CvP j (fun y => H j y ^ 2) x :=
        lintegral_mono hpt
    _ = KP d * ∑' j, ∫⁻ x, CvP j (fun y => H j y ^ 2) x := by
        rw [lintegral_const_mul' _ _ KP_ne_top, lintegral_tsum]
        intro j; exact (CvP_measurable j ((hH j).pow_const 2)).aemeasurable
    _ ≤ KP d * ∑' j, KP d * ∫⁻ x, H j x ^ 2 := by
        gcongr with j
        have h1 := lintegral_CvP_mul j (H := fun y => H j y ^ 2) (w := fun _ => (1 : ℝ≥0∞))
          ((hH j).pow_const 2) measurable_const
        simp only [mul_one] at h1
        rw [h1, ← lintegral_const_mul' _ _ KP_ne_top]
        refine lintegral_mono fun z => ?_
        calc H j z ^ 2 * CvP j (fun _ => (1 : ℝ≥0∞)) z ≤ H j z ^ 2 * KP d :=
              mul_le_mul_right (CvP_one_le j z) _
          _ = KP d * H j z ^ 2 := mul_comm _ _
    _ = (KP d * KP d) * ∫⁻ x, ∑' j, H j x ^ 2 := by
        rw [lintegral_tsum fun j => ((hH j).pow_const 2).aemeasurable, ENNReal.tsum_mul_left,
          mul_assoc]

lemma rpow_self_mul {s : ℝ} (hs : 0 < s) {v : ℝ≥0∞} (hv : v ≠ ⊤) : v * v ^ (s - 1) = v ^ s := by
  by_cases h0 : v = 0
  · subst h0; simp [ENNReal.zero_rpow_of_pos hs]
  · calc v * v ^ (s - 1) = v ^ (1 : ℝ) * v ^ (s - 1) := by rw [ENNReal.rpow_one]
      _ = v ^ ((1 : ℝ) + (s - 1)) := (ENNReal.rpow_add _ _ h0 hv).symm
      _ = v ^ s := by congr 1; ring

lemma rpow_self_mul_sq {s : ℝ} (hs : 1 / 2 < s) {v : ℝ≥0∞} (hv : v ≠ ⊤) :
    v * (v ^ (s - 1)) ^ 2 = v ^ (2 * s - 1) := by
  by_cases h0 : v = 0
  · subst h0
    simp [ENNReal.zero_rpow_of_pos (by linarith : 0 < 2 * s - 1)]
  · rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    calc v * v ^ ((s - 1) * ((2 : ℕ) : ℝ)) = v ^ (1 : ℝ) * v ^ ((s - 1) * ((2 : ℕ) : ℝ)) := by
          rw [ENNReal.rpow_one]
      _ = v ^ ((1 : ℝ) + (s - 1) * ((2 : ℕ) : ℝ)) := (ENNReal.rpow_add _ _ h0 hv).symm
      _ = v ^ (2 * s - 1) := by congr 1; push_cast; ring

/-- positive `ℓ²` Fefferman–Stein, exponent `1/2 < s < 1` (`1 < p < 2`), by duality with `E3pos_gt`. -/
lemma E3pos_lt (hd : 1 ≤ d) {s : ℝ} (hs1 : 1 / 2 < s) (hs2 : s < 1) :
    ∃ C : ℝ≥0, ∀ H : ℤ → 𝔼 → ℝ≥0∞, (∀ j, Measurable (H j)) →
      ∫⁻ x, (∑' j, CvP j (H j) x ^ 2) ^ s ≤ C * ∫⁻ x, (∑' j, H j x ^ 2) ^ s := by
  have hs0 : 0 < s := by linarith
  have h2s : 0 < 2 * s - 1 := by linarith
  set s' : ℝ := s / (2 * s - 1) with hs'
  have hs'1 : 1 < s' := by rw [hs', lt_div_iff₀ h2s]; linarith
  have hs'0 : 0 < s' := by linarith
  obtain ⟨C1, hC1⟩ := E3pos_gt hd hs'1
  obtain ⟨CM, hCM⟩ := Mx_strong hd (p := 2 * s) (by linarith)
  set q : ℝ := 1 / (2 * s) with hq
  set q' : ℝ := 1 / (2 * s') with hq'
  have hqq : q + q' = 1 := by
    rw [hq, hq', hs']
    field_simp
    ring
  have hconj : (2 * s).HolderConjugate (2 * s') := by
    rw [Real.holderConjugate_iff]
    refine ⟨by linarith, ?_⟩
    have := hqq
    rw [hq, hq'] at this
    simpa [one_div] using this
  refine ⟨max 1 (C1 ^ (s / s')), fun H hH => ?_⟩
  have hC1ne : (max 1 (C1 ^ (s / s')) : ℝ≥0) ≠ 0 :=
    (lt_of_lt_of_le one_pos (le_max_left _ _)).ne'
  by_cases hI : ∫⁻ x, (∑' j, H j x ^ 2) ^ s = ⊤
  · rw [hI, ENNReal.mul_top (by exact_mod_cast hC1ne)]; exact le_top
  set I : ℝ≥0∞ := ∫⁻ x, (∑' j, H j x ^ 2) ^ s with hIdef
  have key : ∀ n : ℕ, ∫⁻ x, (∑ j ∈ Fn n, CvP j (H j) x ^ 2) ^ s ≤
      ((C1 ^ (s / s') : ℝ≥0) : ℝ≥0∞) * I := by
    intro n
    set F := Fn n with hF
    set u : ℤ → 𝔼 → ℝ≥0∞ := fun j => CvP j (H j) with hu
    have hum : ∀ j, Measurable (u j) := fun j => CvP_measurable j (hH j)
    set V : 𝔼 → ℝ≥0∞ := fun x => ∑ j ∈ F, u j x ^ 2 with hV
    have hVm : Measurable V := Finset.measurable_sum _ fun j _ => (hum j).pow_const 2
    -- finiteness of `∫ V^s`
    have hHj : ∀ j, ∫⁻ x, (H j x) ^ (2 * s) ≤ I := by
      intro j
      refine lintegral_mono fun x => ?_
      calc H j x ^ (2 * s) = (H j x ^ 2) ^ s := by
            rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
            congr 1
        _ ≤ (∑' i, H i x ^ 2) ^ s :=
            ENNReal.rpow_le_rpow (ENNReal.le_tsum (f := fun i => H i x ^ 2) j) hs0.le
    have hKPs : KP d ^ (2 * s) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by linarith) KP_ne_top
    have hu_fin : ∀ j, ∫⁻ x, (u j x) ^ (2 * s) ≠ ⊤ := by
      intro j
      refine ne_top_of_le_ne_top (b := (KP d) ^ (2 * s) * (CM * I))
        (ENNReal.mul_ne_top hKPs (ENNReal.mul_ne_top ENNReal.coe_ne_top hI)) ?_
      calc ∫⁻ x, u j x ^ (2 * s) ≤ ∫⁻ x, (KP d * cmxHLS_Md (H j) x) ^ (2 * s) :=
            lintegral_mono fun x => ENNReal.rpow_le_rpow (CvP_le j (hH j) x) (by linarith)
        _ = KP d ^ (2 * s) * ∫⁻ x, cmxHLS_Md (H j) x ^ (2 * s) := by
            rw [← lintegral_const_mul' _ _ hKPs]
            exact lintegral_congr fun x => ENNReal.mul_rpow_of_nonneg _ _ (by linarith)
        _ ≤ KP d ^ (2 * s) * (CM * ∫⁻ x, H j x ^ (2 * s)) := by
            gcongr; exact hCM _ (hH j)
        _ ≤ KP d ^ (2 * s) * (CM * I) := by gcongr; exact hHj j
    have hVfin : ∫⁻ x, V x ^ s ≠ ⊤ := by
      refine ne_top_of_le_ne_top (b := ∑ j ∈ F, ∫⁻ x, (u j x) ^ (2 * s))
        (ENNReal.sum_lt_top.2 fun j _ => lt_top_iff_ne_top.2 (hu_fin j)).ne ?_
      calc ∫⁻ x, V x ^ s ≤ ∫⁻ x, ∑ j ∈ F, (u j x ^ 2) ^ s :=
            lintegral_mono fun x => rpow_finsum_le hs0 hs2.le F _
        _ = ∑ j ∈ F, ∫⁻ x, (u j x) ^ (2 * s) := by
            rw [lintegral_finsetSum _ (fun j _ => ((hum j).pow_const 2).pow_const s)]
            refine Finset.sum_congr rfl fun j _ => lintegral_congr fun x => ?_
            rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
            congr 1
    have hVlt : ∀ᵐ x ∂(volume : Measure 𝔼), V x < ⊤ := by
      have : ∀ᵐ x ∂(volume : Measure 𝔼), V x ^ s < ⊤ := ae_lt_top (hVm.pow_const s) hVfin
      filter_upwards [this] with x hx
      by_contra h
      have h' : V x = ⊤ := by simpa using h
      rw [h', ENNReal.top_rpow_of_pos hs0] at hx
      exact lt_irrefl _ hx
    set W : 𝔼 → ℝ≥0∞ := fun x => V x ^ (s - 1) with hW
    have hWm : Measurable W := hVm.pow_const _
    set g : ℤ → 𝔼 → ℝ≥0∞ := fun j x => u j x * W x with hg
    have hgm : ∀ j, Measurable (g j) := fun j => (hum j).mul hWm
    set X : ℝ≥0∞ := ∫⁻ x, V x ^ s with hX
    have hXeq : X = ∫⁻ x, ∑ j ∈ F, u j x * g j x := by
      refine lintegral_congr_ae ?_
      filter_upwards [hVlt] with x hx
      rw [← rpow_self_mul hs0 hx.ne]
      simp only [hV, hg, hW]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have hstep1 : ∫⁻ x, ∑ j ∈ F, u j x * g j x = ∑ j ∈ F, ∫⁻ x, H j x * CvP j (g j) x := by
      have hm : ∀ j ∈ F, Measurable (fun x => u j x * g j x) := fun j _ => (hum j).mul (hgm j)
      rw [lintegral_finsetSum F hm]
      refine Finset.sum_congr rfl fun j _ => ?_
      exact lintegral_CvP_mul j (hH j) (hgm j)
    -- Cauchy–Schwarz in `j`, Hölder in `x`
    set A : 𝔼 → ℝ≥0∞ := fun x => (∑' j, H j x ^ 2) ^ (1 / 2 : ℝ) with hA
    set b : ℤ → 𝔼 → ℝ≥0∞ := fun j => CvP j (g j) with hb
    have hbm : ∀ j, Measurable (b j) := fun j => CvP_measurable j (hgm j)
    set B : 𝔼 → ℝ≥0∞ := fun x => (∑ j ∈ F, b j x ^ 2) ^ (1 / 2 : ℝ) with hB
    have hAm : Measurable A :=
      (Measurable.ennreal_tsum fun j => (hH j).pow_const 2).pow_const _
    have hBm : Measurable B := (Finset.measurable_sum _ fun j _ => (hbm j).pow_const 2).pow_const _
    have hcs : ∀ x, ∑ j ∈ F, H j x * b j x ≤ A x * B x := by
      intro x
      have := ENNReal.inner_le_Lp_mul_Lq F (fun j => H j x) (fun j => b j x)
        (Real.HolderConjugate.two_two)
      refine this.trans (mul_le_mul' ?_ ?_)
      · simp only [hA, ENNReal.rpow_two, one_div]
        refine ENNReal.rpow_le_rpow ?_ (by norm_num)
        exact ENNReal.sum_le_tsum F
      · simp only [hB, ENNReal.rpow_two, one_div]
        exact le_rfl
    have hholder : ∫⁻ x, A x * B x ≤
        (∫⁻ x, A x ^ (2 * s)) ^ (1 / (2 * s)) * (∫⁻ x, B x ^ (2 * s')) ^ (1 / (2 * s')) :=
      ENNReal.lintegral_mul_le_Lp_mul_Lq volume hconj hAm.aemeasurable hBm.aemeasurable
    have hA_eq : ∫⁻ x, A x ^ (2 * s) = I := by
      refine lintegral_congr fun x => ?_
      simp only [hA]
      rw [← ENNReal.rpow_mul]
      congr 1; ring
    have hB_eq : ∀ x, B x ^ (2 * s') = (∑ j ∈ F, b j x ^ 2) ^ s' := by
      intro x
      simp only [hB]
      rw [← ENNReal.rpow_mul]
      congr 1; ring
    -- the dual estimate via `E3pos_gt`
    set G' : ℤ → 𝔼 → ℝ≥0∞ := fun j => if j ∈ F then g j else fun _ => 0 with hG'
    have hG'm : ∀ j, Measurable (G' j) := fun j => by
      by_cases h : j ∈ F
      · simp only [hG', h, if_true]; exact hgm j
      · simp only [hG', h, if_false]; exact measurable_const
    have h1 := hC1 G' hG'm
    have hl : ∀ x, ∑ j ∈ F, b j x ^ 2 ≤ ∑' j, CvP j (G' j) x ^ 2 := by
      intro x
      calc ∑ j ∈ F, b j x ^ 2 = ∑ j ∈ F, CvP j (G' j) x ^ 2 :=
            Finset.sum_congr rfl fun j hj => by simp [hG', hj, hb]
        _ ≤ ∑' j, CvP j (G' j) x ^ 2 := ENNReal.sum_le_tsum F
    have hr : ∀ x, ∑' j, G' j x ^ 2 = ∑ j ∈ F, g j x ^ 2 := by
      intro x
      rw [tsum_eq_sum (s := F)]
      · exact Finset.sum_congr rfl fun j hj => by simp [hG', hj]
      · intro j hj; simp [hG', hj]
    have hk : ∫⁻ x, (∑ j ∈ F, g j x ^ 2) ^ s' = X := by
      refine lintegral_congr_ae ?_
      filter_upwards [hVlt] with x hx
      have : ∑ j ∈ F, g j x ^ 2 = V x * (V x ^ (s - 1)) ^ 2 := by
        simp only [hV, hg, hW]
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [this, rpow_self_mul_sq hs1 hx.ne, ← ENNReal.rpow_mul]
      congr 1
      rw [hs']
      field_simp
    have hdual : ∫⁻ x, B x ^ (2 * s') ≤ C1 * X := by
      calc ∫⁻ x, B x ^ (2 * s') = ∫⁻ x, (∑ j ∈ F, b j x ^ 2) ^ s' := lintegral_congr hB_eq
        _ ≤ ∫⁻ x, (∑' j, CvP j (G' j) x ^ 2) ^ s' :=
            lintegral_mono fun x => ENNReal.rpow_le_rpow (hl x) hs'0.le
        _ ≤ C1 * ∫⁻ x, (∑' j, G' j x ^ 2) ^ s' := h1
        _ = C1 * X := by
            congr 1
            rw [← hk]
            exact lintegral_congr fun x => by rw [hr x]
    -- assemble
    have hmain : X ≤ I ^ q * (C1 * X) ^ q' := by
      calc X = ∫⁻ x, ∑ j ∈ F, u j x * g j x := hXeq
        _ = ∑ j ∈ F, ∫⁻ x, H j x * CvP j (g j) x := hstep1
        _ = ∫⁻ x, ∑ j ∈ F, H j x * b j x :=
            (lintegral_finsetSum F (fun j _ => (hH j).mul (hbm j))).symm
        _ ≤ ∫⁻ x, A x * B x := lintegral_mono hcs
        _ ≤ _ := hholder
        _ ≤ I ^ q * (C1 * X) ^ q' := by
            rw [hA_eq]
            gcongr
    by_cases hX0 : X = 0
    · rw [hX0]; exact zero_le
    have hXtop : X ≠ ⊤ := hVfin
    have hq0 : 0 < q := by rw [hq]; positivity
    have hq'0 : 0 < q' := by rw [hq']; positivity
    have hsplit : X = X ^ q * X ^ q' := by
      rw [← ENNReal.rpow_add _ _ hX0 hXtop, hqq, ENNReal.rpow_one]
    have hposq' : X ^ q' ≠ 0 := by
      intro h; rw [ENNReal.rpow_eq_zero_iff] at h
      rcases h with h | h
      · exact hX0 h.1
      · linarith [h.2]
    have hfinq' : X ^ q' ≠ ⊤ := by
      intro h; rw [ENNReal.rpow_eq_top_iff] at h
      rcases h with h | h
      · linarith [h.2]
      · exact hXtop h.1
    have h4 : X ^ q ≤ I ^ q * (C1 : ℝ≥0∞) ^ q' := by
      have : X ^ q * X ^ q' ≤ (I ^ q * (C1 : ℝ≥0∞) ^ q') * X ^ q' := by
        calc X ^ q * X ^ q' = X := hsplit.symm
          _ ≤ I ^ q * (C1 * X) ^ q' := hmain
          _ = _ := by rw [ENNReal.mul_rpow_of_nonneg _ _ hq'0.le]; ring
      exact (ENNReal.mul_le_mul_iff_left hposq' hfinq').mp this
    calc X = (X ^ q) ^ (1 / q) := by
          rw [← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one]
      _ ≤ (I ^ q * (C1 : ℝ≥0∞) ^ q') ^ (1 / q) := ENNReal.rpow_le_rpow h4 (by positivity)
      _ = I * ((C1 ^ (s / s') : ℝ≥0) : ℝ≥0∞) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
            ← ENNReal.rpow_mul, mul_one_div_cancel hq0.ne', ENNReal.rpow_one,
            ENNReal.coe_rpow_of_nonneg _ (by positivity)]
          congr 2
          rw [hq, hq']
          field_simp
      _ = _ := mul_comm _ _
  have hmono : Monotone (fun n : ℕ => fun x : 𝔼 => ∑ j ∈ Fn n, CvP j (H j) x ^ 2) := by
    intro m n hmn x
    exact Finset.sum_le_sum_of_subset (Fn_mono hmn)
  have hVm : ∀ n : ℕ, Measurable (fun x : 𝔼 => ∑ j ∈ Fn n, CvP j (H j) x ^ 2) := fun n =>
    Finset.measurable_sum _ fun j _ => (CvP_measurable j (hH j)).pow_const 2
  calc ∫⁻ x, (∑' j, CvP j (H j) x ^ 2) ^ s
      = ∫⁻ x, (⨆ n : ℕ, ∑ j ∈ Fn n, CvP j (H j) x ^ 2) ^ s := by
        refine lintegral_congr fun x => ?_
        rw [tsum_eq_iSup_Fn]
    _ = ⨆ n : ℕ, ∫⁻ x, (∑ j ∈ Fn n, CvP j (H j) x ^ 2) ^ s :=
        lintegral_rpow_iSup hVm hmono hs0
    _ ≤ ((C1 ^ (s / s') : ℝ≥0) : ℝ≥0∞) * I := iSup_le key
    _ ≤ _ := by
        gcongr
        exact_mod_cast le_max_right _ _

/-- positive `ℓ²` Fefferman–Stein, all `s > 1/2` (i.e. all `p = 2s > 1`) -/
lemma E3pos (hd : 1 ≤ d) {s : ℝ} (hs : 1 / 2 < s) :
    ∃ C : ℝ≥0, ∀ H : ℤ → 𝔼 → ℝ≥0∞, (∀ j, Measurable (H j)) →
      ∫⁻ x, (∑' j, CvP j (H j) x ^ 2) ^ s ≤ C * ∫⁻ x, (∑' j, H j x ^ 2) ^ s := by
  rcases lt_trichotomy s 1 with h | h | h
  · exact E3pos_lt hd hs h
  · subst h
    refine ⟨(KP d * KP d).toNNReal, fun H hH => ?_⟩
    rw [ENNReal.coe_toNNReal (ENNReal.mul_ne_top KP_ne_top KP_ne_top)]
    simpa only [ENNReal.rpow_one] using E3pos_one H hH
  · exact E3pos_gt hd h

lemma enorm_cv_le_CvP {A : ℝ≥0∞} {j : ℤ} {K u : 𝔼 → ℂ} (hK : DecK A j K) (hu : Measurable u)
    (x : 𝔼) : ‖cv K u x‖ₑ ≤ A * CvP j (fun y => ‖u y‖ₑ) x := by
  refine (enorm_cv_le K u x).trans ?_
  unfold CvP
  have hmeas : Measurable (fun y : 𝔼 => Phi j y * ‖u (x - y)‖ₑ) :=
    (Phi_measurable j).mul ((hu.comp (measurable_const.sub measurable_id)).enorm)
  show ∫⁻ y, ‖K y‖ₑ * ‖u (x - y)‖ₑ ≤ A * ∫⁻ y, Phi j y * ‖u (x - y)‖ₑ
  rw [← lintegral_const_mul _ hmeas]
  refine lintegral_mono fun y => ?_
  rw [← mul_assoc]
  exact mul_le_mul_left (hK y) _

/-- **Vector-valued Fefferman–Stein inequality** for dominated convolution kernels:
`‖(∑_j |K_j ⋆ h_j|²)^{1/2}‖_p ≲ A ‖(∑_j |h_j|²)^{1/2}‖_p`, `p = 2s > 1`. -/
lemma E3 (hd : 1 ≤ d) {s : ℝ} (hs : 1 / 2 < s) :
    ∃ C : ℝ≥0, ∀ (A : ℝ≥0∞), A ≠ ⊤ → ∀ (K h : ℤ → 𝔼 → ℂ), (∀ j, DecK A j (K j)) →
      (∀ j, Measurable (h j)) →
      ∫⁻ x, sqS (fun j => cv (K j) (h j)) x ^ s ≤
        ((A * A) ^ s * C) * ∫⁻ x, sqS h x ^ s := by
  have hs0 : 0 < s := by linarith
  obtain ⟨C, hC⟩ := E3pos hd hs
  refine ⟨C, fun A hA K h hK hh => ?_⟩
  set H : ℤ → 𝔼 → ℝ≥0∞ := fun j y => ‖h j y‖ₑ with hH
  have hHm : ∀ j, Measurable (H j) := fun j => (hh j).enorm
  have hpt : ∀ x, sqS (fun j => cv (K j) (h j)) x ≤ (A * A) * ∑' j, CvP j (H j) x ^ 2 := by
    intro x
    unfold sqS
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun j => ?_
    calc ‖cv (K j) (h j) x‖ₑ ^ 2 ≤ (A * CvP j (H j) x) ^ 2 := by
          gcongr; exact enorm_cv_le_CvP (hK j) (hh j) x
      _ = _ := by ring
  calc ∫⁻ x, sqS (fun j => cv (K j) (h j)) x ^ s
      ≤ ∫⁻ x, ((A * A) * ∑' j, CvP j (H j) x ^ 2) ^ s :=
        lintegral_mono fun x => ENNReal.rpow_le_rpow (hpt x) hs0.le
    _ = ∫⁻ x, (A * A) ^ s * (∑' j, CvP j (H j) x ^ 2) ^ s :=
        lintegral_congr fun x => ENNReal.mul_rpow_of_nonneg _ _ hs0.le
    _ = (A * A) ^ s * ∫⁻ x, (∑' j, CvP j (H j) x ^ 2) ^ s :=
        lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hs0.le (ENNReal.mul_ne_top hA hA))
    _ ≤ (A * A) ^ s * (C * ∫⁻ x, (∑' j, H j x ^ 2) ^ s) := by
        gcongr
        exact hC H hHm
    _ = _ := by
        rw [← mul_assoc]
        rfl

end HRS.Commutator.Whole.XLI
