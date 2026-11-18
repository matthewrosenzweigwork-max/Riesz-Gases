import HRS.MC.Q714GTCore

/-!
# Packet GT (row 7.14), law-level Gaussian Taylor expansion

`gt_core`: the two bounds of `gaussian_taylor` for Gaussian laws `γ₁, γ₂` on `B` (no random elements).
-/

open MeasureTheory ProbabilityTheory
open HRS

noncomputable section

namespace HRS.MC.Q714.GT

section Iter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Norm of the `j`-th derivative of the `m`-th derivative. -/
lemma gt_norm_iter_iter (f : E → ℝ) (m : ℕ) : ∀ (j : ℕ) (w : E),
    ‖iteratedFDeriv ℝ j (iteratedFDeriv ℝ m f) w‖ = ‖iteratedFDeriv ℝ (m + j) f w‖ := by
  induction m with
  | zero =>
    intro j w
    rw [iteratedFDeriv_zero_eq_comp, zero_add]
    exact LinearIsometryEquiv.norm_iteratedFDeriv_comp_left
      (continuousMultilinearCurryFin0 ℝ E ℝ).symm f w j
  | succ m ih =>
    intro j w
    have e : iteratedFDeriv ℝ (m + 1) f =
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) ℝ).symm ∘
          fderiv ℝ (iteratedFDeriv ℝ m f) := iteratedFDeriv_succ_eq_comp_left
    have h1 := LinearIsometryEquiv.norm_iteratedFDeriv_comp_left (𝕜 := ℝ) (E := E)
      (F := E →L[ℝ] (E [×m]→L[ℝ] ℝ)) (G := E [×(m+1)]→L[ℝ] ℝ)
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => E) ℝ).symm
      (fderiv ℝ (iteratedFDeriv ℝ m f)) w j
    rw [e, h1, norm_iteratedFDeriv_fderiv, ih, show m + (j + 1) = m + 1 + j by omega]

lemma gt_norm_D2 (Θ : E → ℝ) (u : E) :
    ‖fderiv ℝ (fderiv ℝ Θ) u‖ = ‖iteratedFDeriv ℝ 2 Θ u‖ := by
  have := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := Θ) (x := u) (n := 1)
  simpa using this

end Iter

/-- Comparison of increments from derivative bounds. -/
lemma gt_cmp_abs {f f' g g' : ℝ → ℝ} (hf : ∀ θ, HasDerivAt f (f' θ) θ)
    (hg : ∀ θ, HasDerivAt g (g' θ) θ) {a b : ℝ} (hab : a ≤ b)
    (h : ∀ θ ∈ Set.Icc a b, |f' θ| ≤ g' θ) : |f b - f a| ≤ g b - g a := by
  have key : ∀ s : ℝ, (s = 1 ∨ s = -1) → s * (f b - f a) ≤ g b - g a := by
    intro s hs
    have hmono : MonotoneOn (fun θ => g θ - s * f θ) (Set.Icc a b) := by
      refine monotoneOn_of_deriv_nonneg (convex_Icc a b) ?_ ?_ ?_
      · exact fun θ _ => ((hg θ).sub ((hf θ).const_mul s)).continuousAt.continuousWithinAt
      · exact fun θ _ =>
          ((hg θ).sub ((hf θ).const_mul s)).differentiableAt.differentiableWithinAt
      · intro θ hθ
        rw [interior_Icc] at hθ
        have hd : HasDerivAt (fun θ => g θ - s * f θ) (g' θ - s * f' θ) θ :=
          (hg θ).sub ((hf θ).const_mul s)
        rw [hd.deriv]
        have := h θ (Set.Ioo_subset_Icc_self hθ)
        rcases hs with rfl | rfl <;> linarith [le_abs_self (f' θ), neg_abs_le (f' θ)]
    have := hmono (Set.left_mem_Icc.2 hab) (Set.right_mem_Icc.2 hab) hab
    simp only at this
    linarith
  rw [abs_le]
  constructor
  · have := key (-1) (Or.inr rfl); linarith
  · have := key 1 (Or.inl rfl); linarith

lemma gt_hasDerivAt_sin_sq (c θ : ℝ) :
    HasDerivAt (fun θ => c * Real.sin θ ^ 2) (2 * c * Real.sin θ * Real.cos θ) θ := by
  have := ((Real.hasDerivAt_sin θ).pow 2).const_mul c
  convert this using 1
  simp; ring

lemma gt_hasDerivAt_sin_four (c θ : ℝ) :
    HasDerivAt (fun θ => c * Real.sin θ ^ 4) (4 * c * Real.sin θ ^ 3 * Real.cos θ) θ := by
  have := ((Real.hasDerivAt_sin θ).pow 4).const_mul c
  convert this using 1
  simp; ring

lemma gt_sin_cos_nonneg {θ : ℝ} (h0 : 0 ≤ θ) (h1 : θ ≤ Real.pi / 2) :
    0 ≤ Real.sin θ * Real.cos θ :=
  mul_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi h0 (h1.trans (by linarith [Real.pi_pos])))
    (Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) h1)

variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B]
  [MeasurableSpace B] [BorelSpace B] [SecondCountableTopology B]

lemma gt_bilin_int {γ : Measure B} [IsFiniteMeasure γ] (hs : Integrable (fun z : B => ‖z‖ ^ 2) γ)
    (M : B [×2]→L[ℝ] ℝ) : Integrable (fun z => M ![z, z]) γ := by
  refine (hs.const_mul ‖M‖).mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · exact (M.cont.comp (continuous_pi fun i => by
      fin_cases i <;> exact continuous_id)).aestronglyMeasurable
  · have := M.le_opNorm ![z, z]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at this
    calc _ ≤ ‖M‖ * (‖z‖ * ‖z‖) := this
      _ = _ := by ring

/-- `Δ` is a bounded linear functional on bounded bilinear forms. -/
lemma gt_delta_clm {γ₁ γ₂ : Measure B} [IsProbabilityMeasure γ₁] [IsProbabilityMeasure γ₂]
    (hs₁ : Integrable (fun z : B => ‖z‖ ^ 2) γ₁) (hs₂ : Integrable (fun z : B => ‖z‖ ^ 2) γ₂)
    (Δ : (B [×2]→L[ℝ] ℝ) → ℝ)
    (hΔ : ∀ M : B [×2]→L[ℝ] ℝ, Δ M = ∫ z, M ![z, z] ∂γ₂ - ∫ z, M ![z, z] ∂γ₁)
    (δ : ℝ) (hδ : ∀ M : B [×2]→L[ℝ] ℝ, ‖M‖ ≤ 1 → |Δ M| ≤ δ) :
    ∃ L : (B [×2]→L[ℝ] ℝ) →L[ℝ] ℝ, (∀ M, L M = Δ M) ∧ 0 ≤ δ ∧ ‖L‖ ≤ δ := by
  have hδ0 : 0 ≤ δ := by
    have := hδ 0 (by simp)
    exact (abs_nonneg _).trans this
  have hadd : ∀ M N, Δ (M + N) = Δ M + Δ N := by
    intro M N
    simp only [hΔ, add_apply]
    rw [integral_add (gt_bilin_int hs₁ M) (gt_bilin_int hs₁ N),
      integral_add (gt_bilin_int hs₂ M) (gt_bilin_int hs₂ N)]
    ring
  have hsmul : ∀ (c : ℝ) M, Δ (c • M) = c * Δ M := by
    intro c M
    simp only [hΔ, smul_apply, smul_eq_mul]
    rw [integral_const_mul, integral_const_mul]
    ring
  have hbd : ∀ M, ‖Δ M‖ ≤ δ * ‖M‖ := by
    intro M
    by_cases hM : M = 0
    · subst hM
      have : Δ 0 = 0 := by simpa using hsmul 0 0
      simp [this]
    · have hn : 0 < ‖M‖ := norm_pos_iff.2 hM
      have h1 := hδ (‖M‖⁻¹ • M) (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne'])
      rw [hsmul, abs_mul, abs_inv, abs_norm] at h1
      rw [Real.norm_eq_abs]
      have := (inv_mul_le_iff₀ hn).1 h1
      linarith
  let Lm : (B [×2]→L[ℝ] ℝ) →ₗ[ℝ] ℝ :=
    { toFun := Δ, map_add' := hadd, map_smul' := fun c M => by simpa using hsmul c M }
  refine ⟨Lm.mkContinuous δ (fun M => by simpa [Lm] using hbd M), fun M => rfl, hδ0, ?_⟩
  exact LinearMap.mkContinuous_norm_le _ hδ0 _

end HRS.MC.Q714.GT

end
