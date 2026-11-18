import HRS.MS.S21F_S26aT

/-!
# S21F, packet R26-T3.S26a: scalar range cutoffs preserve bounded positive derivatives of a Stein function

`f_n(x) = (n+1) θ((f x - f 0)/(n+1))` with `θ` of `s21f_theta`.  `D f_n = b(φ_n) • D f` (`φ_n = (f - f 0)/(n+1)`), so
`D^{k+1} f_n = D^k (b(φ_n) • D f)` is bounded by the Leibniz formula (`norm_iteratedFDeriv_smul_le`), the chain rule bound
(`norm_iteratedFDeriv_comp_le` applied to the BOUNDED `b`, with `‖D^l φ_n‖ ≤ 1`) and `‖D^l f‖ ≤ 1`, uniformly in `n`; `f_n` is bounded
by `(n+1) sup|θ|`; near any `x`, `f_n = f - f 0` for large `n`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff
open HRS HRS.Whole

namespace HRS.MS.R26T3

theorem s21f_iter_sub_const {f : SeqL2 → ℝ} {N : ℕ} (hf : ContDiff ℝ N f) {j : ℕ} (hj : 1 ≤ j) (hjN : j ≤ N)
    (c : ℝ) (x : SeqL2) : iteratedFDeriv ℝ j (fun y => f y - c) x = iteratedFDeriv ℝ j f x := by
  have h1 := iteratedFDeriv_sub_apply (i := j) (f := f) (g := fun _ => c) (x := x)
    ((hf.of_le (by exact_mod_cast hjN)).contDiffAt) contDiffAt_const
  change iteratedFDeriv ℝ j (f - fun _ => c) x = _
  rw [h1, iteratedFDeriv_const_of_ne (by omega)]
  simp

theorem s21f_phi_iter {f : SeqL2 → ℝ} (hf : ContDiff ℝ 5 f)
    (hb : ∀ i : ℕ, 1 ≤ i → i ≤ 5 → ∀ z, ‖iteratedFDeriv ℝ i f z‖ ≤ 1) (n : ℕ) {j : ℕ} (hj : 1 ≤ j) (hj5 : j ≤ 5)
    (x : SeqL2) :
    ‖iteratedFDeriv ℝ j (fun y => ((n : ℝ) + 1)⁻¹ • (f y - f 0)) x‖ ≤ 1 ^ j := by
  have hc : ContDiff ℝ 5 (fun y => f y - f 0) := hf.sub contDiff_const
  rw [iteratedFDeriv_const_smul_apply' ((hc.of_le (by exact_mod_cast hj5)).contDiffAt),
    s21f_iter_sub_const hf hj hj5, norm_smul, one_pow]
  have ha : ‖((n : ℝ) + 1)⁻¹‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
    exact inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  calc ‖((n : ℝ) + 1)⁻¹‖ * ‖iteratedFDeriv ℝ j f x‖ ≤ 1 * 1 :=
        mul_le_mul ha (hb j hj hj5 x) (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem s21f_cut_hasFDeriv {θ b : ℝ → ℝ} (hθ : ∀ t, HasDerivAt θ (b t) t) {f : SeqL2 → ℝ}
    (hf : ContDiff ℝ 5 f) (n : ℕ) (x : SeqL2) :
    HasFDerivAt (fun y => ((n : ℝ) + 1) * θ (((n : ℝ) + 1)⁻¹ • (f y - f 0)))
      ((b (((n : ℝ) + 1)⁻¹ • (f x - f 0))) • fderiv ℝ f x) x := by
  set a : ℝ := (n : ℝ) + 1 with ha
  have ha0 : a ≠ 0 := by rw [ha]; positivity
  have hfd : HasFDerivAt f (fderiv ℝ f x) x :=
    ((hf.differentiable (by norm_num)) x).hasFDerivAt
  have h1 : HasFDerivAt (fun y => a⁻¹ • (f y - f 0)) (a⁻¹ • fderiv ℝ f x) x :=
    (hfd.sub_const (f 0)).const_smul a⁻¹
  have h2 := ((hθ (a⁻¹ • (f x - f 0))).comp_hasFDerivAt x h1).const_mul a
  refine (show HasFDerivAt (fun y => a * θ (a⁻¹ • (f y - f 0))) _ x from h2).congr_fderiv ?_
  ext v
  simp only [smul_apply, smul_eq_mul]
  field_simp

theorem s21f_cut_bound {θ b : ℝ → ℝ} (hθ : ∀ t, HasDerivAt θ (b t) t) (hb : ContDiff ℝ ∞ b) {C : ℝ}
    (hC0 : 0 ≤ C) (hC : ∀ k : ℕ, k ≤ 2 → ∀ t, ‖iteratedFDeriv ℝ k b t‖ ≤ C) {f : SeqL2 → ℝ}
    (hf : ContDiff ℝ 5 f) (hfb : ∀ i : ℕ, 1 ≤ i → i ≤ 5 → ∀ z, ‖iteratedFDeriv ℝ i f z‖ ≤ 1) (n : ℕ)
    {k : ℕ} (hk : k ≤ 2) (x : SeqL2) :
    ‖iteratedFDeriv ℝ (k + 1) (fun y => ((n : ℝ) + 1) * θ (((n : ℝ) + 1)⁻¹ • (f y - f 0))) x‖ ≤ 24 * C := by
  set a : ℝ := (n : ℝ) + 1 with ha
  have ha0 : 0 < a := by rw [ha]; positivity
  have hφ : ContDiff ℝ 5 (fun y => a⁻¹ • (f y - f 0)) := (hf.sub contDiff_const).const_smul _
  have hF : ContDiff ℝ 2 (fun y => b (a⁻¹ • (f y - f 0))) :=
    (hb.of_le (by norm_num)).comp (hφ.of_le (by norm_num))
  have hG : ContDiff ℝ 2 (fderiv ℝ f) := hf.fderiv_right (m := 2) (by norm_num)
  have hfd : fderiv ℝ (fun y => a * θ (a⁻¹ • (f y - f 0))) =
      fun y => (b (a⁻¹ • (f y - f 0))) • fderiv ℝ f y := by
    funext y
    have := (s21f_cut_hasFDeriv hθ hf n y).fderiv
    rw [this]
  rw [← norm_iteratedFDeriv_fderiv, hfd]
  refine (norm_iteratedFDeriv_smul_le hF hG x (by exact_mod_cast hk)).trans ?_
  have hterm : ∀ i : ℕ, i ≤ 2 → ‖iteratedFDeriv ℝ i (fun y => b (a⁻¹ • (f y - f 0))) x‖ ≤ 2 * C := by
    intro i hi
    have h := norm_iteratedFDeriv_comp_le (g := b) (f := fun y => a⁻¹ • (f y - f 0)) (n := i) (N := 2)
      (hb.of_le (by norm_num)) (hφ.of_le (by norm_num)) (by exact_mod_cast hi) x (C := C) (D := 1)
      (fun l hl => hC l (hl.trans hi) _)
      (fun l hl1 hl2 => s21f_phi_iter hf hfb n hl1 (by omega) x)
    refine h.trans ?_
    have : (i.factorial : ℝ) ≤ 2 := by interval_cases i <;> norm_num [Nat.factorial]
    simp only [one_pow, mul_one]
    nlinarith
  have hG1 : ∀ l : ℕ, l ≤ 2 → ‖iteratedFDeriv ℝ l (fderiv ℝ f) x‖ ≤ 1 := fun l hl => by
    rw [norm_iteratedFDeriv_fderiv]; exact hfb (l + 1) (by omega) (by omega) x
  have hch : ∀ i : ℕ, ((k.choose i : ℕ) : ℝ) ≤ 4 := fun i => by
    have h1 : k.choose i ≤ 2 ^ k := Nat.choose_le_two_pow k i
    have h2 : 2 ^ k ≤ 4 := by calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk
                                _ = 4 := by norm_num
    exact_mod_cast h1.trans h2
  calc ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (fun y => b (a⁻¹ • (f y - f 0))) x‖ * ‖iteratedFDeriv ℝ (k - i) (fderiv ℝ f) x‖
      ≤ ∑ i ∈ Finset.range (k + 1), (4 * (2 * C) * 1) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi2 : i ≤ 2 := by have := Finset.mem_range.1 hi; omega
        have e1 := hterm i hi2
        have e2 := hG1 (k - i) (by omega)
        have e3 := hch i
        have n1 := norm_nonneg (iteratedFDeriv ℝ i (fun y => b (a⁻¹ • (f y - f 0))) x)
        have n2 := norm_nonneg (iteratedFDeriv ℝ (k - i) (fderiv ℝ f) x)
        have c0 : (0 : ℝ) ≤ (k.choose i : ℝ) := Nat.cast_nonneg _
        calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y => b (a⁻¹ • (f y - f 0))) x‖ *
              ‖iteratedFDeriv ℝ (k - i) (fderiv ℝ f) x‖
            ≤ 4 * (2 * C) * 1 := by
              gcongr
        _ = _ := rfl
    _ = (k + 1 : ℕ) * (4 * (2 * C) * 1) := by simp
    _ ≤ 3 * (4 * (2 * C) * 1) := by
        have : ((k + 1 : ℕ) : ℝ) ≤ 3 := by exact_mod_cast (by omega : k + 1 ≤ 3)
        nlinarith
    _ = 24 * C := by ring

theorem r26t3_stein_cutoff (f : SeqL2 → ℝ) (hf : S99.SteinCl f) :
    ∃ fn : ℕ → SeqL2 → ℝ, (∀ n, MemCb 3 (fn n)) ∧
      (∃ C : ℝ, ∀ n j, 1 ≤ j → j ≤ 3 → ∀ x, ‖iteratedFDeriv ℝ j (fn n) x‖ ≤ C) ∧
      (∀ x, ∀ j : ℕ, 1 ≤ j → j ≤ 3 →
        Tendsto (fun n => iteratedFDeriv ℝ j (fn n) x) atTop
          (𝓝 (iteratedFDeriv ℝ j f x))) := by
  obtain ⟨θ, b, hb, hθ, hid, ⟨B, hB⟩, ⟨C, hC0, hC⟩⟩ := s21f_theta
  obtain ⟨hf5, hfb⟩ := hf
  have hθs : ContDiff ℝ ∞ θ := by
    rw [contDiff_infty_iff_deriv]
    refine ⟨fun t => (hθ t).differentiableAt, ?_⟩
    have : deriv θ = b := funext fun t => (hθ t).deriv
    rw [this]; exact hb
  have hfc : Continuous f := hf5.continuous
  refine ⟨fun n x => ((n : ℝ) + 1) * θ (((n : ℝ) + 1)⁻¹ • (f x - f 0)), fun n => ⟨?_, fun j hj => ?_⟩,
    ⟨24 * C, fun n j hj1 hj3 x => ?_⟩, fun x j hj1 hj3 => ?_⟩
  · exact contDiff_const.mul ((hθs.of_le (by norm_num)).comp ((hf5.sub contDiff_const).const_smul _ |>.of_le (by norm_num)))
  · rcases Nat.eq_zero_or_pos j with h0 | hpos
    · subst h0
      refine ⟨((n : ℝ) + 1) * B, ?_⟩
      rintro _ ⟨x, rfl⟩
      simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_mul]
      rw [abs_of_pos (by positivity)]
      exact mul_le_mul_of_nonneg_left (hB _) (by positivity)
    · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      refine ⟨24 * C, ?_⟩
      rintro _ ⟨x, rfl⟩
      exact s21f_cut_bound hθ hb hC0 hC hf5 hfb n (by omega) x
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    exact s21f_cut_bound hθ hb hC0 hC hf5 hfb n (by omega) x
  · obtain ⟨N0, hN0⟩ := exists_nat_gt |f x - f 0|
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N0] with n hn
    have hnr : |f x - f 0| < (n : ℝ) + 1 := by
      have : (N0 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have hU : ∀ᶠ y in 𝓝 x, |f y - f 0| < (n : ℝ) + 1 :=
      (isOpen_lt ((hfc.sub continuous_const).abs) continuous_const).mem_nhds hnr
    have heq : (fun y => ((n : ℝ) + 1) * θ (((n : ℝ) + 1)⁻¹ • (f y - f 0))) =ᶠ[𝓝 x]
        fun y => f y - f 0 := hU.mono fun y hy => by
      have ha : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hlt := abs_lt.1 hy
      have hmem : ((n : ℝ) + 1)⁻¹ • (f y - f 0) ∈ Icc (-1 : ℝ) 1 := by
        rw [smul_eq_mul]
        constructor
        · rw [← neg_one_mul, ← div_eq_inv_mul, le_div_iff₀ ha]; linarith
        · rw [← div_eq_inv_mul, div_le_one ha]; linarith
      show ((n : ℝ) + 1) * θ _ = _
      rw [hid _ hmem, smul_eq_mul]
      field_simp
    show iteratedFDeriv ℝ j f x = iteratedFDeriv ℝ j _ x
    have hf5' : ContDiff ℝ ((5 : ℕ) : ℕ∞ω) f := by exact_mod_cast hf5
    rw [(heq.iteratedFDeriv ℝ j).eq_of_nhds, s21f_iter_sub_const (N := 5) hf5' hj1 (by omega)]

end HRS.MS.R26T3
