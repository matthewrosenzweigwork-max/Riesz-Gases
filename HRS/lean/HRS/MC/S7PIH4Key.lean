import HRS.MC.S7PIH3Expand

/-!
# Packet piH, part 4: second order expansion of a Gaussian average with a tail estimate
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MatrixOrder

noncomputable section

namespace HRS.MC.Sec7.S7PIH

variable {q : ℕ}

theorem S7PIH_gauss_expand {Δ : Matrix (Fin q) (Fin q) ℝ} (hΔ : Δ.PosSemidef) {b : ℝ} (hb : 0 < b)
    (hbΔ : ∀ u : EuclideanSpace ℝ (Fin q), u.ofLp ⬝ᵥ Δ.mulVec u.ofLp ≤ b ^ 2 * ‖u‖ ^ 2)
    {H : EuclideanSpace ℝ (Fin q) → ℝ} (hH : ContDiff ℝ 2 H) {C0 : ℝ} (hbd : ∀ y, |H y| ≤ C0)
    (c : EuclideanSpace ℝ (Fin q)) {M ε δ : ℝ} (hδ : 0 < δ)
    (hM : ∀ y, ‖iteratedFDeriv ℝ 2 H y - iteratedFDeriv ℝ 2 H c‖ ≤ M)
    (hε : ∀ y, ‖y - c‖ ≤ δ → ‖iteratedFDeriv ℝ 2 H y - iteratedFDeriv ℝ 2 H c‖ ≤ ε) :
    |∫ k, H (c + k) ∂(multivariateGaussian 0 Δ) - H c - (1 / 2) * ∑ i, ∑ j, Δ i j *
        iteratedFDeriv ℝ 2 H c ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]|
      ≤ b ^ 2 * (ε * S7PIH_V2 q + M * S7PIH_tail q (δ / b)) := by
  set N := multivariateGaussian (0 : EuclideanSpace ℝ (Fin q)) Δ with hN
  set μ0 := stdGaussian (EuclideanSpace ℝ (Fin q)) with hμ0
  set B := Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt Δ) with hB
  have hNmap : N = μ0.map (fun x => 0 + B x) := rfl
  have hε0 : 0 ≤ ε := (norm_nonneg _).trans (hε c (by simp [hδ.le]))
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM c)
  have hBb : ∀ z, ‖B z‖ ≤ b * ‖z‖ := by
    intro z
    have h := S7PIH_normB_sq hΔ z
    have h2 : ‖B z‖ ^ 2 ≤ (b * ‖z‖) ^ 2 := by rw [hB, h, mul_pow]; exact hbΔ z
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).1 h2
  set T2 := fderiv ℝ (fderiv ℝ H) c with hT2
  have hD2 : ∀ k, iteratedFDeriv ℝ 2 H c ![k, k] = T2 k k := fun k => by
    simp [iteratedFDeriv_two_apply, hT2]
  have hD2e : ∀ i j : Fin q, iteratedFDeriv ℝ 2 H c ![EuclideanSpace.single i 1, EuclideanSpace.single j 1]
      = T2 (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) := fun i j => by
    simp [iteratedFDeriv_two_apply, hT2]
  obtain ⟨hqi, hqv⟩ := S7PIH_gauss_quad hΔ T2
  have hHc : Continuous H := hH.continuous
  have hHint : Integrable (fun k => H (c + k)) N :=
    Integrable.of_bound (C := C0) (hHc.comp (by fun_prop : Continuous fun k : EuclideanSpace ℝ (Fin q) => c + k)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun k => by simpa using hbd (c + k))
  have hlin : Integrable (fun k => fderiv ℝ H c k) N :=
    (fderiv ℝ H c).integrable_comp (IsGaussian.integrable_id)
  have hlin0 : ∫ k, fderiv ℝ H c k ∂N = 0 := by
    have := ContinuousLinearMap.integral_comp_comm (fderiv ℝ H c) (μ := N) (φ := id)
      IsGaussian.integrable_id
    simpa [hN] using this
  set r' : EuclideanSpace ℝ (Fin q) → ℝ :=
    fun k => H (c + k) - H c - fderiv ℝ H c k - (1 / 2) * T2 k k with hr'
  have step1 : ∫ k, r' k ∂N = ∫ k, H (c + k) ∂N - H c -
      (1 / 2) * ∑ i, ∑ j, Δ i j * iteratedFDeriv ℝ 2 H c
        ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] := by
    have i1 : Integrable (fun k => H (c + k) - H c) N := hHint.sub (integrable_const _)
    have i2 : Integrable (fun k => H (c + k) - H c - fderiv ℝ H c k) N := i1.sub hlin
    have i3 : Integrable (fun k => (1 / 2) * T2 k k) N := hqi.const_mul _
    simp only [hr']
    rw [integral_sub i2 i3, integral_sub i1 hlin, integral_sub hHint (integrable_const _),
      integral_const_mul, hqv, hlin0]
    simp [hD2e]
  have hr'cont : Continuous r' := by
    have : Continuous fun k : EuclideanSpace ℝ (Fin q) => T2 k k :=
      T2.continuous.clm_apply continuous_id
    simp only [hr']
    have h1 : Continuous fun k : EuclideanSpace ℝ (Fin q) => H (c + k) :=
      hHc.comp (by fun_prop)
    have h2 : Continuous fun k : EuclideanSpace ℝ (Fin q) => fderiv ℝ H c k :=
      (fderiv ℝ H c).continuous
    fun_prop
  have step2 : ∫ k, r' k ∂N = ∫ z, r' (0 + B z) ∂μ0 := by
    rw [hNmap]
    exact integral_map (by fun_prop) hr'cont.aestronglyMeasurable
  set g : EuclideanSpace ℝ (Fin q) → ℝ := fun z => b ^ 2 * (ε * ‖z‖ ^ 2 +
    M * Set.indicator {z : EuclideanSpace ℝ (Fin q) | δ / b < ‖z‖} (fun z => ‖z‖ ^ 2) z) with hg
  have hgint : Integrable g μ0 := by
    refine Integrable.const_mul (Integrable.add ((S7PIH_sq_integrable q).const_mul ε) ?_) _
    exact ((S7PIH_sq_integrable q).indicator
      (measurableSet_lt measurable_const measurable_norm)).const_mul M
  have hpt : ∀ z, ‖r' (0 + B z)‖ ≤ g z := by
    intro z
    simp only [zero_add]
    set m : ℝ := if ‖z‖ ≤ δ / b then ε else M with hm
    have hm0 : 0 ≤ m := by rw [hm]; split_ifs <;> assumption
    have hmθ : ∀ θ ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ 2 H (c + θ • B z) - iteratedFDeriv ℝ 2 H c‖ ≤ m := by
      intro θ hθ
      rw [hm]
      split_ifs with h
      · refine hε _ ?_
        have : ‖c + θ • B z - c‖ = θ * ‖B z‖ := by
          rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ.1]
        rw [this]
        have h1 : ‖B z‖ ≤ δ := by
          calc ‖B z‖ ≤ b * ‖z‖ := hBb z
            _ ≤ b * (δ / b) := by gcongr
            _ = δ := by field_simp
        nlinarith [hθ.1, hθ.2, norm_nonneg (B z)]
      · exact hM _
    have ht := S7PIH_taylor2 hH c (B z) hmθ
    rw [hD2] at ht
    rw [Real.norm_eq_abs]
    refine ht.trans ?_
    have hBz2 : ‖B z‖ ^ 2 ≤ b ^ 2 * ‖z‖ ^ 2 := by
      rw [← mul_pow]; exact pow_le_pow_left₀ (norm_nonneg _) (hBb z) 2
    calc m * ‖B z‖ ^ 2 ≤ m * (b ^ 2 * ‖z‖ ^ 2) := by gcongr
      _ = b ^ 2 * (m * ‖z‖ ^ 2) := by ring
      _ ≤ g z := by
        rw [hg]
        simp only
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg b)
        by_cases h : ‖z‖ ≤ δ / b
        · have hind : Set.indicator {z : EuclideanSpace ℝ (Fin q) | δ / b < ‖z‖} (fun z => ‖z‖ ^ 2) z = 0 :=
            Set.indicator_of_notMem (by simpa using h) _
          rw [hm, if_pos h, hind]
          simp
        · have hind : Set.indicator {z : EuclideanSpace ℝ (Fin q) | δ / b < ‖z‖} (fun z => ‖z‖ ^ 2) z = ‖z‖ ^ 2 :=
            Set.indicator_of_mem (by simpa using h) _
          rw [hm, if_neg h, hind]
          nlinarith [mul_nonneg hε0 (sq_nonneg ‖z‖)]
  have step3 : ‖∫ z, r' (0 + B z) ∂μ0‖ ≤ ∫ z, g z ∂μ0 :=
    norm_integral_le_of_norm_le hgint (Filter.Eventually.of_forall hpt)
  have hgval : ∫ z, g z ∂μ0 = b ^ 2 * (ε * S7PIH_V2 q + M * S7PIH_tail q (δ / b)) := by
    rw [hg]
    simp only
    rw [integral_const_mul, integral_add ((S7PIH_sq_integrable q).const_mul ε)
      (((S7PIH_sq_integrable q).indicator
        (measurableSet_lt measurable_const measurable_norm)).const_mul M),
      integral_const_mul, integral_const_mul]
    rfl
  rw [← step1, step2, ← Real.norm_eq_abs, ← hgval]
  exact step3

end HRS.MC.Sec7.S7PIH

end
