import HRS.MS.WrKerAux1

/-!
# HRS.MS.WrKerAux2 -- site kernels and Wu's inequality for the generic weak kernel (WR-1, part 2)

Port of `HRS/Energy/WeakReference.lean` lines 452-673 (sections `Site3`, `Wu`) to a general measurable
space `E` (instantiate `E := Euc d` for the Euclidean whole space).  Main declarations:

* `EWeakKernel.siteKernel_le_E`: the conditional density of the one-site kernel is `≤ C μ` for `C ≥ e^{2β'a}`.
* `EWeakKernel.siteKernel_coeff_E`: Dobrushin coefficient `≤ 4 e^{2β'a} β' a / N`.
* `EWeakKernel.wu_clause_E`: Wu's variance inequality for `pairGibbsLawE` with constant 2.
-/

set_option linter.unusedSectionVars false

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

variable {E : Type*} [MeasurableSpace E] {N : ℕ}

section Site3

set_option linter.unusedSectionVars false

variable {μ : Measure (E)} [IsProbabilityMeasure μ] {a : ℝ} {q : E → E → ℝ}

lemma EWeakKernel.siteKernel_le_E (h : EWeakKernel μ a q) (ha : 0 ≤ a) {β' : ℝ} (hβ : 0 ≤ β')
    {N : ℕ} (hN : 0 < N) (i : Fin N) (x : (Fin N → E)) {C : ℝ} (hC : Real.exp (2 * (β' * a)) ≤ C) :
    External.siteKernel μ (pairWeightE q N β' μ) i x ≤ ENNReal.ofReal C • μ := by
  rw [h.wr1_siteKernel_eq ha hβ hN i x]
  have hVp := lt_of_lt_of_le (Real.exp_pos _) (h.wr1_integral_vfun_ge ha hβ hN i x)
  refine Measure.le_iff.2 fun S hS => ?_
  rw [withDensity_apply _ hS, Measure.smul_apply, smul_eq_mul, ← setLIntegral_const]
  refine lintegral_mono fun z => ?_
  refine ENNReal.ofReal_le_ofReal ?_
  rw [div_le_iff₀ (lt_of_lt_of_le (Real.exp_pos _) (h.wr1_integral_vfun_ge ha hβ hN i x))]
  have h1 := h.wr1_vfun_le ha hβ N i x z
  have h2 := h.wr1_integral_vfun_ge ha hβ hN i x
  have h3 : Real.exp (2 * (β' * a)) * Real.exp (-(β' * a)) = Real.exp (β' * a) := by
    rw [← Real.exp_add]; congr 1; ring
  have h4 : Real.exp (2 * (β' * a)) * Real.exp (-(β' * a)) ≤ C * ∫ w, vfunE q μ N β' i x w ∂μ := by
    calc _ ≤ C * Real.exp (-(β' * a)) :=
          mul_le_mul_of_nonneg_right hC (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul_of_nonneg_left h2 ((Real.exp_pos _).le.trans hC)
  linarith

lemma EWeakKernel.wr1_abs_vfun_sub_le (h : EWeakKernel μ a q) (ha : 0 ≤ a) {β' : ℝ} (hβ : 0 ≤ β')
    {N : ℕ} (i j : Fin N) (hij : i ≠ j) (x y : (Fin N → E)) (hxy : ∀ k, k ≠ j → x k = y k)
    (z : E) :
    |vfunE q μ N β' i x z - vfunE q μ N β' i y z|
      ≤ Real.exp (β' * a) * (β' / N * (q z (x j) + q z (y j))) := by
  unfold vfunE
  set A : (Fin N → E) → ℝ := fun x => β' / N * ∑ l ∈ Finset.univ.erase i, q z (x l) with hA
  have hA0 : ∀ x, 0 ≤ A x := fun x => mul_nonneg (div_nonneg hβ (Nat.cast_nonneg N))
    (Finset.sum_nonneg fun l _ => h.nonneg _ _)
  have hAx : ∀ x : (Fin N → E), -(β' / N) * ∑ l ∈ Finset.univ.erase i, q z (x l)
      + β' * rowIntE q μ z = -A x + β' * rowIntE q μ z := fun x => by simp only [hA]; ring
  simp_rw [hAx]
  have e : ∀ x : (Fin N → E), Real.exp (-A x + β' * rowIntE q μ z)
      = Real.exp (-A x) * Real.exp (β' * rowIntE q μ z) := fun x => by rw [← Real.exp_add]
  simp_rw [e]
  rw [← sub_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hle : Real.exp (β' * rowIntE q μ z) ≤ Real.exp (β' * a) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (h.wr1_rowInt_le ha z) hβ)
  have hdiff : |A x - A y| ≤ β' / N * (q z (x j) + q z (y j)) := by
    have hj : j ∈ Finset.univ.erase i := Finset.mem_erase.2 ⟨hij.symm, Finset.mem_univ j⟩
    have hs : ∑ l ∈ Finset.univ.erase i, q z (x l) - ∑ l ∈ Finset.univ.erase i, q z (y l)
        = q z (x j) - q z (y j) := by
      rw [← Finset.sum_sub_distrib]
      rw [Finset.sum_eq_single j]
      · intro l _ hl; rw [hxy l hl]; ring
      · intro hj'; exact absurd hj hj'
    have : A x - A y = β' / N * (q z (x j) - q z (y j)) := by
      simp only [hA]; rw [← mul_sub, hs]
    rw [this, abs_mul, abs_of_nonneg (div_nonneg hβ (Nat.cast_nonneg N))]
    refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hβ (Nat.cast_nonneg N))
    have := h.nonneg z (x j); have := h.nonneg z (y j)
    rw [abs_le]; constructor <;> linarith
  calc |Real.exp (-A x) - Real.exp (-A y)| * Real.exp (β' * rowIntE q μ z)
      ≤ |A x - A y| * Real.exp (β' * a) :=
        mul_le_mul (wr1_abs_exp_neg_sub_le (hA0 x) (hA0 y)) hle (Real.exp_pos _).le (abs_nonneg _)
    _ ≤ _ := by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_left hdiff (Real.exp_pos _).le

lemma EWeakKernel.siteKernel_coeff_E (h : EWeakKernel μ a q) (ha : 0 ≤ a) {β' : ℝ} (hβ : 0 ≤ β')
    {N : ℕ} (hN : 0 < N) (i j : Fin N) (hij : i ≠ j) (x y : (Fin N → E))
    (hxy : ∀ k, k ≠ j → x k = y k) (S : Set (E)) (hS : MeasurableSet S) :
    |(External.siteKernel μ (pairWeightE q N β' μ) i x).real S
        - (External.siteKernel μ (pairWeightE q N β' μ) i y).real S|
      ≤ 4 * Real.exp (2 * (β' * a)) * β' * a / N := by
  have hbd : ∀ (x : (Fin N → E)) z, |vfunE q μ N β' i x z| ≤ Real.exp (β' * a) := fun x z => by
    rw [abs_of_pos (wr1_vfunE_pos N β' i x z)]; exact h.wr1_vfun_le ha hβ N i x z
  have ivf : ∀ x : (Fin N → E), Integrable (vfunE q μ N β' i x) μ := fun x =>
    wr1_integrable_of_bdd' μ (h.wr1_measurable_vfun N β' i x) (hbd x)
  have hVp : ∀ x : (Fin N → E), 0 < ∫ w, vfunE q μ N β' i x w ∂μ := fun x =>
    lt_of_lt_of_le (Real.exp_pos _) (h.wr1_integral_vfun_ge ha hβ hN i x)
  have hreal : ∀ x : (Fin N → E),
      (External.siteKernel μ (pairWeightE q N β' μ) i x).real S
        = ∫ z in S, vfunE q μ N β' i x z / ∫ w, vfunE q μ N β' i x w ∂μ ∂μ := by
    intro x
    rw [h.wr1_siteKernel_eq ha hβ hN i x, Measure.real]
    exact wr1_real_withDensity_ofReal μ (fun z => div_nonneg (wr1_vfunE_pos N β' i x z).le (hVp x).le)
      ((ivf x).div_const _) hS
  rw [hreal x, hreal y]
  have htv := wr1_tv_normalized μ (h.wr1_measurable_vfun N β' i x) (h.wr1_measurable_vfun N β' i y)
    (fun z => (wr1_vfunE_pos N β' i x z).le) (fun z => (wr1_vfunE_pos N β' i y z).le)
    (fun z => h.wr1_vfun_le ha hβ N i x z) (fun z => h.wr1_vfun_le ha hβ N i y z) (Real.exp_pos (-(β' * a)))
    (h.wr1_integral_vfun_ge ha hβ hN i x) (h.wr1_integral_vfun_ge ha hβ hN i y) S
  refine htv.trans ?_
  -- bound the L¹ distance
  have iq : ∀ x : (Fin N → E), Integrable (fun z => q z (x j)) μ := fun x => h.wr1_integrable_col (x j)
  have hI : ∫ z, |vfunE q μ N β' i x z - vfunE q μ N β' i y z| ∂μ
      ≤ Real.exp (β' * a) * (β' / N * (2 * a)) := by
    calc ∫ z, |vfunE q μ N β' i x z - vfunE q μ N β' i y z| ∂μ
        ≤ ∫ z, Real.exp (β' * a) * (β' / N * (q z (x j) + q z (y j))) ∂μ :=
          integral_mono ((ivf x).sub (ivf y)).abs
            (((iq x).add (iq y)).const_mul _ |>.const_mul _)
            (fun z => h.wr1_abs_vfun_sub_le ha hβ i j hij x y hxy z)
      _ = Real.exp (β' * a) * (β' / N * (rowIntE q μ (x j) + rowIntE q μ (y j))) := by
          rw [integral_const_mul, integral_const_mul, integral_add (iq x) (iq y),
            h.wr1_integral_col, h.wr1_integral_col]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
          refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hβ (Nat.cast_nonneg N))
          have := h.wr1_rowInt_le ha (x j); have := h.wr1_rowInt_le ha (y j); linarith
  have hm : 2 / Real.exp (-(β' * a)) = 2 * Real.exp (β' * a) := by
    rw [div_eq_mul_inv, ← Real.exp_neg, neg_neg]
  rw [hm]
  have h2 : (2 : ℝ) * Real.exp (β' * a) * (Real.exp (β' * a) * (β' / N * (2 * a)))
      = 4 * Real.exp (2 * (β' * a)) * β' * a / N := by
    have : Real.exp (2 * (β' * a)) = Real.exp (β' * a) * Real.exp (β' * a) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]; ring
  rw [← h2]
  exact mul_le_mul_of_nonneg_left hI (by positivity)

end Site3

section Wu

set_option linter.unusedSectionVars false

variable {μ : Measure (E)} [IsProbabilityMeasure μ] {a : ℝ} {q : E → E → ℝ}

lemma wr1_siteKernel_div_const {E : Type*} [MeasurableSpace E] {n : ℕ} (μ : Measure E)
    [IsProbabilityMeasure μ] (W : (Fin n → E) → ℝ≥0∞) (K : ℝ≥0∞) (hK0 : K ≠ 0) (hKt : K ≠ ⊤)
    (i : Fin n) :
    External.siteKernel μ (fun X => W X / K) i = External.siteKernel μ W i := by
  unfold External.siteKernel
  congr 1
  funext x z
  have hKi0 : K⁻¹ ≠ 0 := ENNReal.inv_ne_zero.2 hKt
  have hKit : K⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.2 hK0
  have hn : External.normalizer μ (fun X => W X / K) i x = External.normalizer μ W i x * K⁻¹ := by
    unfold External.normalizer
    simp_rw [div_eq_mul_inv]
    exact lintegral_mul_const' _ _ hKit
  rw [hn]
  simp only [div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inr hKit) (Or.inr hKi0), inv_inv]
  calc W (Function.update x i z) * K⁻¹ * ((External.normalizer μ W i x)⁻¹ * K)
      = W (Function.update x i z) * (External.normalizer μ W i x)⁻¹ * (K⁻¹ * K) := by ring
    _ = _ := by rw [ENNReal.inv_mul_cancel hK0 hKt, mul_one]

lemma EWeakKernel.wr1_pairWeight_le (h : EWeakKernel μ a q) (ha : 0 ≤ a) {β' : ℝ} (hβ : 0 ≤ β')
    {N : ℕ} (hN : 0 < N) (X : (Fin N → E)) :
    pairWeightE q N β' μ X ≤ ENNReal.ofReal (Real.exp (β' * N * a)) := by
  unfold pairWeightE
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  rw [wr1_exponent_eq q μ β' X hN]
  have h1 : 0 ≤ pairSumE q X := Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun l _ => h.nonneg _ _
  have h2 : ∑ k, rowIntE q μ (X k) ≤ N * a := by
    calc ∑ k, rowIntE q μ (X k) ≤ ∑ _k : Fin N, a := Finset.sum_le_sum fun k _ => h.wr1_rowInt_le ha _
      _ = N * a := by simp
  have h3 : 0 ≤ ∫ x, ∫ y, q x y ∂μ ∂μ := integral_nonneg fun x => h.wr1_rowInt_nonneg x
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h4 : 0 ≤ β' / (2 * N) * pairSumE q X := mul_nonneg (by positivity) h1
  have h5 : 0 ≤ β' * N * (∫ x, ∫ y, q x y ∂μ ∂μ) / 2 := by positivity
  have h6 : β' * ∑ k, rowIntE q μ (X k) ≤ β' * (N * a) := mul_le_mul_of_nonneg_left h2 hβ
  have e : β' * N * a = β' * (N * a) := by ring
  rw [e]
  have : -(β' / (2 * N)) * pairSumE q X = -(β' / (2 * N) * pairSumE q X) := by ring
  rw [this]
  linarith

lemma EWeakKernel.wr1_partition_pos_lt (h : EWeakKernel μ a q) (ha : 0 ≤ a) {β' : ℝ} (hβ : 0 ≤ β')
    {N : ℕ} (hN : 0 < N) :
    pairPartitionE q N β' μ ≠ 0 ∧ pairPartitionE q N β' μ ≠ ⊤ := by
  have hW := h.wr1_measurable_pairWeight N β'
  constructor
  · unfold pairPartitionE
    intro h0
    rw [lintegral_eq_zero_iff hW] at h0
    have hne : ∀ᵐ X ∂(Measure.pi fun _ : Fin N => μ), False := by
      filter_upwards [h0] with X hX
      have : (0 : ℝ≥0∞) < pairWeightE q N β' μ X := ENNReal.ofReal_pos.2 (Real.exp_pos _)
      exact this.ne' hX
    have := ae_iff.mp hne
    simp at this
  · unfold pairPartitionE
    refine ne_of_lt (lt_of_le_of_lt (lintegral_mono fun X => h.wr1_pairWeight_le ha hβ hN X) ?_)
    simp

lemma EWeakKernel.wu_clause_E (h : EWeakKernel μ a q) (ha : 0 ≤ a) {β' : ℝ} (hβ : 0 ≤ β')
    {N : ℕ} (hN : 0 < N) (κ : ℝ) (hκ0 : 0 ≤ κ) (hκ : κ ≤ 1 / 2)
    (hcoef : ∀ i j : Fin N, i ≠ j → ∀ x y : (Fin N → E), (∀ k, k ≠ j → x k = y k) →
      ∀ S : Set (E), MeasurableSet S →
        |(External.siteKernel μ (pairWeightE q N β' μ) i x).real S
          - (External.siteKernel μ (pairWeightE q N β' μ) i y).real S| ≤ κ / N)
    (F : (Fin N → E) → ℝ) (hF : Measurable F) :
    ProbabilityTheory.evariance F (pairGibbsLawE q N β' μ) ≤
      2 * ∑ i, ∫⁻ x, ProbabilityTheory.evariance (fun z => F (Function.update x i z))
        (External.siteKernel μ (pairWeightE q N β' μ) i x) ∂(pairGibbsLawE q N β' μ : Measure ((Fin N → E))) := by
  obtain ⟨hK0, hKt⟩ := h.wr1_partition_pos_lt ha hβ hN
  set K := pairPartitionE q N β' μ with hK
  set W := pairWeightE q N β' μ with hWdef
  have hW : Measurable W := h.wr1_measurable_pairWeight N β'
  have hW' : Measurable (fun X => W X / K) := by
    simpa [div_eq_mul_inv] using hW.mul_const K⁻¹
  have hpos : ∀ X, 0 < W X / K := fun X =>
    ENNReal.div_pos (ENNReal.ofReal_pos.2 (Real.exp_pos _)).ne' hKt
  have hbd0 : ENNReal.ofReal (Real.exp (β' * N * a)) / K ≠ ⊤ :=
    (ENNReal.div_lt_top ENNReal.ofReal_ne_top hK0).ne
  have hbd : ∀ X, W X / K ≤ ((ENNReal.ofReal (Real.exp (β' * N * a)) / K).toNNReal : ℝ≥0∞) := by
    intro X
    rw [ENNReal.coe_toNNReal hbd0]
    exact ENNReal.div_le_div_right (h.wr1_pairWeight_le ha hβ hN X) K
  have hnorm : ∫⁻ X, W X / K ∂(Measure.pi fun _ : Fin N => μ) = 1 := by
    simp_rw [div_eq_mul_inv]
    rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 hK0)]
    exact ENNReal.mul_inv_cancel hK0 hKt
  have := External.wu_resampling_half μ (fun X => W X / K) hW' hpos _ hbd hnorm
    (fun _ _ => κ / N) (fun _ _ => div_nonneg hκ0 (Nat.cast_nonneg N))
    (fun i j hij x y hxy S hS => by
      rw [wr1_siteKernel_div_const μ W K hK0 hKt i]
      exact hcoef i j hij x y hxy S hS)
    (fun i => (External.row_sum_le_of_uniform hN le_rfl hκ0 i).trans hκ) F hF
  simp_rw [wr1_siteKernel_div_const μ W K hK0 hKt] at this
  exact this

end Wu
end HRS.MS.Wr
