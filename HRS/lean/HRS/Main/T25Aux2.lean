import HRS.Main.T25Aux1

/-!
# T25-IN, part 2 (ENT-UNI): a weighted Gronwall inequality with horizon-independent constant

`P:eq:entropy-input` (TeX M L6558) is `sup_{t ≥ 0}`.  The Gronwall step of `movT_entropy_gronwall_proof` uses the supremum bound of the
Lipschitz constant and gives `e^{A T}`; the TeX uses `∫_0^∞ L < ∞`.  This file proves the abstract inequality in the form needed:

`v(t) = H₀ + ∫_0^t G`, `G ≤ L (A v + B)` with `A > 0`, `B ≥ 0`, `L ≥ 0` integrable, `v ≥ 0`, `∫_0^T L ≤ Λ₁`
  ⟹  `v(t) ≤ 2^{⌈2AΛ₁⌉+1} (H₀ + B/A)` for `0 ≤ t ≤ T` (`t25_gronwall_unif`),

by Λ-blocks: on a block with `A ∫_block L ≤ 1/2`, `sup v ≤ 2 v(start) + 2 B ∫_block L` (maximum at a point of the compact block).
-/

open MeasureTheory Filter Topology Set intervalIntegral
open scoped ENNReal NNReal

noncomputable section

namespace HRS

namespace T25

section Gronwall

variable {T A B H0 : ℝ} {G L : ℝ → ℝ}

/-- `v(r) = H₀ + ∫_0^r G`. -/
def t25V (H0 : ℝ) (G : ℝ → ℝ) (r : ℝ) : ℝ := H0 + ∫ x in (0 : ℝ)..r, G x

theorem t25_ii_of_sub (hG : IntegrableOn G (Set.Icc 0 T)) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hbT : b ≤ T) : IntervalIntegrable G volume a b :=
  (intervalIntegrable_iff_integrableOn_Icc_of_le hab).2
    (hG.mono_set (Set.Icc_subset_Icc ha hbT))

theorem t25V_sub (hG : IntegrableOn G (Set.Icc 0 T)) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (htT : t ≤ T) : t25V H0 G t - t25V H0 G s = ∫ x in s..t, G x := by
  have h0s : IntervalIntegrable G volume 0 s := t25_ii_of_sub hG le_rfl hs (hst.trans htT)
  have hst' : IntervalIntegrable G volume s t := t25_ii_of_sub hG hs hst htT
  have := integral_add_adjacent_intervals h0s hst'
  unfold t25V
  linarith

theorem t25V_contOn (hG : IntegrableOn G (Set.Icc 0 T)) (hT : 0 ≤ T) :
    ContinuousOn (t25V H0 G) (Set.Icc 0 T) := by
  unfold t25V
  refine continuousOn_const.add ?_
  have h : IntegrableOn G (Set.uIcc 0 T) := by rwa [Set.uIcc_of_le hT]
  have := intervalIntegral.continuousOn_primitive_interval (μ := volume) h
  rwa [Set.uIcc_of_le hT] at this

/-- One Λ-block. -/
theorem t25_block (hG : IntegrableOn G (Set.Icc 0 T)) (hL : IntegrableOn L (Set.Icc 0 T))
    (hL0 : ∀ r ∈ Set.Icc 0 T, 0 ≤ L r) (hA : 0 < A) (hB : 0 ≤ B)
    (hv0 : ∀ r ∈ Set.Icc 0 T, 0 ≤ t25V H0 G r)
    (hGv : ∀ r ∈ Set.Icc 0 T, G r ≤ L r * (A * t25V H0 G r + B))
    {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T)
    (hmass : A * ∫ x in s..t, L x ≤ 1 / 2) :
    ∀ r ∈ Set.Icc s t, t25V H0 G r ≤ 2 * t25V H0 G s + 2 * B * ∫ x in s..t, L x := by
  have hT : 0 ≤ T := hs.trans (hst.trans htT)
  have hcont : ContinuousOn (t25V H0 G) (Set.Icc s t) :=
    (t25V_contOn hG hT).mono (Set.Icc_subset_Icc hs htT)
  obtain ⟨r0, hr0, hmax⟩ := (isCompact_Icc : IsCompact (Set.Icc s t)).exists_isMaxOn
    (Set.nonempty_Icc.2 hst) hcont
  set M : ℝ := t25V H0 G r0 with hM
  have hr0T : r0 ∈ Set.Icc 0 T := ⟨hs.trans hr0.1, hr0.2.trans htT⟩
  have hM0 : 0 ≤ M := hv0 r0 hr0T
  have hle : ∀ r ∈ Set.Icc s t, t25V H0 G r ≤ M := fun r hr => hmax hr
  set lam : ℝ := ∫ x in s..t, L x with hlam
  have hlii : IntervalIntegrable L volume s t := t25_ii_of_sub hL hs hst htT
  have hlii' : IntervalIntegrable L volume s r0 :=
    t25_ii_of_sub hL hs hr0.1 (hr0.2.trans htT)
  have hlam0 : 0 ≤ lam := by
    refine intervalIntegral.integral_nonneg hst fun x hx => hL0 x ⟨hs.trans hx.1, hx.2.trans htT⟩
  have hlam1 : ∫ x in s..r0, L x ≤ lam := by
    have hadd := integral_add_adjacent_intervals hlii' (t25_ii_of_sub hL (hs.trans hr0.1) hr0.2 htT)
    have : 0 ≤ ∫ x in r0..t, L x :=
      intervalIntegral.integral_nonneg hr0.2 fun x hx =>
        hL0 x ⟨hs.trans (hr0.1.trans hx.1), hx.2.trans htT⟩
    linarith
  have hinc := t25V_sub (H0 := H0) hG hs hr0.1 (hr0.2.trans htT)
  have hG1 : ∫ x in s..r0, G x ≤ ∫ x in s..r0, L x * (A * M + B) := by
    refine intervalIntegral.integral_mono_on hr0.1 (t25_ii_of_sub hG hs hr0.1 (hr0.2.trans htT))
      (hlii'.mul_const _) fun x hx => ?_
    have hxT : x ∈ Set.Icc 0 T := ⟨hs.trans hx.1, hx.2.trans (hr0.2.trans htT)⟩
    have hxst : x ∈ Set.Icc s t := ⟨hx.1, hx.2.trans hr0.2⟩
    refine (hGv x hxT).trans ?_
    exact mul_le_mul_of_nonneg_left (by nlinarith [hle x hxst]) (hL0 x hxT)
  have hG2 : ∫ x in s..r0, L x * (A * M + B) = (∫ x in s..r0, L x) * (A * M + B) := by
    rw [intervalIntegral.integral_mul_const]
  have hAMB : 0 ≤ A * M + B := by positivity
  have hMle : M ≤ t25V H0 G s + (A * M + B) * lam := by
    have h1 : M - t25V H0 G s ≤ (∫ x in s..r0, L x) * (A * M + B) := by
      have := hinc
      rw [hG2] at hG1
      linarith
    have h2 : (∫ x in s..r0, L x) * (A * M + B) ≤ lam * (A * M + B) :=
      mul_le_mul_of_nonneg_right hlam1 hAMB
    nlinarith
  have hAM : A * M * lam ≤ M / 2 := by
    have : A * lam * M ≤ (1 / 2) * M := mul_le_mul_of_nonneg_right (by linarith) hM0
    nlinarith
  intro r hr
  have h3 : M ≤ 2 * t25V H0 G s + 2 * B * lam := by nlinarith
  exact (hle r hr).trans h3

/-- Chain of blocks: `n + 1` blocks of mass `≤ 1/(2A)`. -/
theorem t25_chain (hG : IntegrableOn G (Set.Icc 0 T)) (hL : IntegrableOn L (Set.Icc 0 T))
    (hL0 : ∀ r ∈ Set.Icc 0 T, 0 ≤ L r) (hA : 0 < A) (hB : 0 ≤ B)
    (hv0 : ∀ r ∈ Set.Icc 0 T, 0 ≤ t25V H0 G r)
    (hGv : ∀ r ∈ Set.Icc 0 T, G r ≤ L r * (A * t25V H0 G r + B)) :
    ∀ n : ℕ, ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T → A * ∫ x in s..t, L x ≤ ((n : ℝ) + 1) / 2 →
      ∀ r ∈ Set.Icc s t, t25V H0 G r ≤ 2 ^ (n + 1) * t25V H0 G s + (2 ^ (n + 1) - 1) * (B / A) := by
  intro n
  induction n with
  | zero =>
    intro s t hs hst htT hmass r hr
    have hb := t25_block hG hL hL0 hA hB hv0 hGv hs hst htT (by simpa using hmass) r hr
    have hlam0 : 0 ≤ ∫ x in s..t, L x :=
      intervalIntegral.integral_nonneg hst fun x hx => hL0 x ⟨hs.trans hx.1, hx.2.trans htT⟩
    have : 2 * B * ∫ x in s..t, L x ≤ B / A := by
      have h1 : A * (2 * B * ∫ x in s..t, L x) ≤ B := by nlinarith
      rw [le_div_iff₀ hA]; linarith
    simp only [zero_add, pow_one]
    linarith
  | succ n ih =>
    intro s t hs hst htT hmass r hr
    by_cases hsmall : A * ∫ x in s..t, L x ≤ 1 / 2
    · have hb := t25_block hG hL hL0 hA hB hv0 hGv hs hst htT hsmall r hr
      have hlam0 : 0 ≤ ∫ x in s..t, L x :=
        intervalIntegral.integral_nonneg hst fun x hx => hL0 x ⟨hs.trans hx.1, hx.2.trans htT⟩
      have h2 : 2 * B * ∫ x in s..t, L x ≤ B / A := by
        have h1 : A * (2 * B * ∫ x in s..t, L x) ≤ B := by nlinarith
        rw [le_div_iff₀ hA]; linarith
      have hv00 : 0 ≤ t25V H0 G s := hv0 s ⟨hs, hst.trans htT⟩
      have hp : (2 : ℝ) ≤ 2 ^ (n + 1 + 1) := by
        calc (2 : ℝ) = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (n + 1 + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have hbA : 0 ≤ B / A := by positivity
      have hq : (1 : ℝ) ≤ 2 ^ (n + 1 + 1) - 1 := by linarith
      nlinarith [mul_le_mul_of_nonneg_right hp hv00, mul_le_mul_of_nonneg_right hq hbA]
    · push_neg at hsmall
      -- choose s' with block mass exactly 1/(2A)
      have hlii : ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T → IntervalIntegrable L volume a b :=
        fun a b ha hab hbT => t25_ii_of_sub hL ha hab hbT
      have hcontF : ContinuousOn (fun x => ∫ y in s..x, L y) (Set.Icc s t) := by
        have h : IntegrableOn L (Set.uIcc s t) := by
          rw [Set.uIcc_of_le hst]; exact hL.mono_set (Set.Icc_subset_Icc hs htT)
        have := intervalIntegral.continuousOn_primitive_interval (μ := volume) h
        rwa [Set.uIcc_of_le hst] at this
      have hF0 : (fun x => ∫ y in s..x, L y) s = 0 := by simp
      have hAinv : (0 : ℝ) < 1 / (2 * A) := by positivity
      have hmem : 1 / (2 * A) ∈ Set.Icc ((fun x => ∫ y in s..x, L y) s)
          ((fun x => ∫ y in s..x, L y) t) := by
        refine ⟨by simp only [hF0]; exact hAinv.le, ?_⟩
        show 1 / (2 * A) ≤ ∫ y in s..t, L y
        rw [div_le_iff₀ (by positivity)]
        nlinarith
      obtain ⟨s', hs', hs'eq⟩ := intermediate_value_Icc hst hcontF hmem
      have hs'eq' : ∫ y in s..s', L y = 1 / (2 * A) := hs'eq
      have hmass1 : A * ∫ y in s..s', L y ≤ 1 / 2 := by
        rw [hs'eq']; field_simp; rfl
      have hblock := t25_block hG hL hL0 hA hB hv0 hGv hs hs'.1 (hs'.2.trans htT) hmass1
      have hlamB : 2 * B * ∫ y in s..s', L y = B / A := by
        rw [hs'eq']; field_simp
      have hv_s' : t25V H0 G s' ≤ 2 * t25V H0 G s + B / A := by
        have := hblock s' ⟨hs'.1, le_rfl⟩
        rw [hlamB] at this; exact this
      -- the remaining mass
      have hrest : A * ∫ y in s'..t, L y ≤ ((n : ℝ) + 1) / 2 := by
        have hadd := integral_add_adjacent_intervals
          (hlii s s' hs hs'.1 (hs'.2.trans htT)) (hlii s' t (hs.trans hs'.1) hs'.2 htT)
        have : A * ∫ y in s..s', L y = 1 / 2 := by rw [hs'eq']; field_simp
        have hh : A * ∫ y in s..t, L y ≤ (((n + 1 : ℕ) : ℝ) + 1) / 2 := hmass
        push_cast at hh
        nlinarith
      by_cases hrs : r ≤ s'
      · have := hblock r ⟨hr.1, hrs⟩
        rw [hlamB] at this
        have hv00 : 0 ≤ t25V H0 G s := hv0 s ⟨hs, hst.trans htT⟩
        have hp : (2 : ℝ) ≤ 2 ^ (n + 1 + 1) := by
          calc (2 : ℝ) = 2 ^ 1 := by norm_num
            _ ≤ 2 ^ (n + 1 + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
        have hbA : 0 ≤ B / A := by positivity
        have hq : (1 : ℝ) ≤ 2 ^ (n + 1 + 1) - 1 := by linarith
        nlinarith [mul_le_mul_of_nonneg_right hp hv00, mul_le_mul_of_nonneg_right hq hbA]
      · push_neg at hrs
        have h1 := ih s' t (hs.trans hs'.1) hs'.2 htT hrest r ⟨hrs.le, hr.2⟩
        have hpn : (0 : ℝ) ≤ 2 ^ (n + 1) := by positivity
        have h2 := mul_le_mul_of_nonneg_left hv_s' hpn
        have e1 : (2 : ℝ) ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) := by ring
        rw [e1]
        nlinarith

/-- **Weighted Gronwall with horizon-independent constant.** -/
theorem t25_gronwall_unif (hG : IntegrableOn G (Set.Icc 0 T)) (hL : IntegrableOn L (Set.Icc 0 T))
    (hL0 : ∀ r ∈ Set.Icc 0 T, 0 ≤ L r) (hA : 0 < A) (hB : 0 ≤ B)
    (hv0 : ∀ r ∈ Set.Icc 0 T, 0 ≤ t25V H0 G r)
    (hGv : ∀ r ∈ Set.Icc 0 T, G r ≤ L r * (A * t25V H0 G r + B))
    {Λ₁ : ℝ} (hΛ : ∫ x in (0 : ℝ)..T, L x ≤ Λ₁) (hT : 0 ≤ T) :
    ∀ t ∈ Set.Icc 0 T,
      t25V H0 G t ≤ 2 ^ (⌈2 * A * Λ₁⌉₊ + 1) * (H0 + B / A) := by
  intro t ht
  have hmass : A * ∫ x in (0 : ℝ)..t, L x ≤ (((⌈2 * A * Λ₁⌉₊ : ℕ) : ℝ) + 1) / 2 := by
    have h1 : ∫ x in (0 : ℝ)..t, L x ≤ ∫ x in (0 : ℝ)..T, L x := by
      have hadd := integral_add_adjacent_intervals (t25_ii_of_sub hL le_rfl ht.1 ht.2)
        (t25_ii_of_sub hL ht.1 ht.2 le_rfl)
      have : 0 ≤ ∫ x in t..T, L x :=
        intervalIntegral.integral_nonneg ht.2 fun x hx => hL0 x ⟨ht.1.trans hx.1, hx.2⟩
      linarith
    have h2 : 2 * A * Λ₁ ≤ (⌈2 * A * Λ₁⌉₊ : ℝ) := Nat.le_ceil _
    nlinarith
  have := t25_chain hG hL hL0 hA hB hv0 hGv ⌈2 * A * Λ₁⌉₊ 0 t le_rfl ht.1 ht.2 hmass t ⟨ht.1, le_rfl⟩
  have hv00 : t25V H0 G 0 = H0 := by simp [t25V]
  rw [hv00] at this
  refine this.trans ?_
  have hbA : 0 ≤ B / A := by positivity
  have hp : (0 : ℝ) ≤ 2 ^ (⌈2 * A * Λ₁⌉₊ + 1) := by positivity
  nlinarith [mul_nonneg hp hbA]

end Gronwall

end T25

end HRS

end
