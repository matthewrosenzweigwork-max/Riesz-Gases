import HRS.MC.CepH2Aux16

/-!
# CEPH2, helper 17: the time-slice inequality

For a fixed probability measure `μ`, `u = Ĝ * μ`, `ℓ = log u + U/θ`, `χ = χ_R`:

`∫_cell χ (ℓ+1) ∫ A dμ ≤ -θ(1-δ) ∫_cell χ u ‖dℓ‖² + K² N v/(4θδ) - ∫_cell ∫ (ℓ+1) B_χ dμ`.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Pointwise

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

theorem h2_contDiff_chi1 (R : ℝ) : ContDiff ℝ 1 (h2_chi (N := N) R) :=
  (h2_contDiff_chi R).of_le (by exact_mod_cast le_top)

/-- The bound for the integrated-by-parts integrand in terms of `‖dφ(x)‖`. -/
theorem h2_B_bound {v : ℝ} (hv : 0 < v) (θ : ℝ) (U : Ch N → ℝ) :
    ∃ B2 : ℝ, 0 ≤ B2 ∧ ∀ (φ : Ch N → ℝ) (x y : Ch N) (c : ℝ), 0 ≤ c → ‖fderiv ℝ φ x‖ ≤ c →
      |h2_B θ v U φ x y| ≤ c * B2 * (1 + ‖gradient U y‖) := by
  obtain ⟨B, hB0, hB⟩ := h2_per_le (N := N) hv
  refine ⟨|θ| * N * B + B, by positivity, fun φ x y c hc hφc => ?_⟩
  have h1 : |h2_B θ v U φ x y| ≤ c * (|θ| * N * B) + c * B * ‖gradient U y‖ := by
    unfold h2_B
    refine le_trans (abs_add_le _ _) (add_le_add ?_ ?_)
    · rw [abs_mul]
      calc |θ| * |∑ k, fderiv ℝ φ x (h2_e k) * h2_per1 v (x - y) (h2_e k)|
          ≤ |θ| * ∑ _k : Fin N, c * B := by
            refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
              (Finset.sum_le_sum fun k _ => ?_)) (abs_nonneg _)
            rw [abs_mul]
            refine mul_le_mul ?_ ?_ (abs_nonneg _) hc
            · rw [← Real.norm_eq_abs]
              calc ‖fderiv ℝ φ x (h2_e k)‖ ≤ ‖fderiv ℝ φ x‖ * ‖h2_e k‖ := ContinuousLinearMap.le_opNorm _ _
                _ ≤ c := by rw [h2_norm_e]; simpa using hφc
            · rw [← Real.norm_eq_abs]
              calc ‖h2_per1 v (x - y) (h2_e k)‖ ≤ ‖h2_per1 v (x - y)‖ * ‖h2_e k‖ := ContinuousLinearMap.le_opNorm _ _
                _ ≤ B := by rw [h2_norm_e]; simpa using (hB _).2.1
        _ = c * (|θ| * N * B) := by simp; ring
    · rw [abs_mul]
      calc |fderiv ℝ φ x (gradient U y)| * |h2_per v (x - y)| ≤ (c * ‖gradient U y‖) * B := by
            refine mul_le_mul ?_ ?_ (abs_nonneg _) (by positivity)
            · rw [← Real.norm_eq_abs]
              calc ‖fderiv ℝ φ x (gradient U y)‖ ≤ ‖fderiv ℝ φ x‖ * ‖gradient U y‖ := ContinuousLinearMap.le_opNorm _ _
                _ ≤ c * ‖gradient U y‖ := mul_le_mul_of_nonneg_right hφc (norm_nonneg _)
            · rw [← Real.norm_eq_abs]; exact (hB _).1
        _ = c * B * ‖gradient U y‖ := by ring
  have hg := norm_nonneg (gradient U y)
  have h3 : 0 ≤ c * (|θ| * N * B) * ‖gradient U y‖ := by positivity
  have e : c * (|θ| * N * B + B) * (1 + ‖gradient U y‖) =
      c * (|θ| * N * B) + c * B * ‖gradient U y‖ + (c * (|θ| * N * B) * ‖gradient U y‖ + c * B) := by ring
  rw [e]
  linarith [mul_nonneg hc hB0]

theorem h2_continuous_B {v : ℝ} (hv : 0 < v) {θ : ℝ} {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U) {φ : Ch N → ℝ}
    (hφ : ContDiff ℝ 1 φ) : Continuous (Function.uncurry fun x y => h2_B θ v U φ x y) := by
  have hgc := h2_continuous_gradient hU
  have hper1c : Continuous (h2_per1 (N := N) v) := h2_continuous_per1 hv
  have hperc : Continuous (h2_per (N := N) v) := h2_continuous_per hv
  have hdφ : Continuous (fderiv ℝ φ) := hφ.continuous_fderiv (by simp)
  have hsub : Continuous fun z : Ch N × Ch N => z.1 - z.2 := continuous_fst.sub continuous_snd
  unfold h2_B
  refine Continuous.add (continuous_const.mul (continuous_finset_sum _ fun k _ => ?_)) ?_
  · exact ((hdφ.comp continuous_fst).clm_apply continuous_const).mul ((hper1c.comp hsub).clm_apply continuous_const)
  · exact ((hdφ.comp continuous_fst).clm_apply (hgc.comp continuous_snd)).mul (hperc.comp hsub)

theorem h2_integrable_B {v : ℝ} (hv : 0 < v) {θ : ℝ} {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U) {μ : Measure (Ch N)}
    [IsFiniteMeasure μ] (hG1 : Integrable (fun y => ‖gradient U y‖) μ) {φ : Ch N → ℝ} (hφ : ContDiff ℝ 1 φ)
    (x : Ch N) : Integrable (fun y => h2_B θ v U φ x y) μ := by
  obtain ⟨B2, hB2, hB⟩ := h2_B_bound hv θ U
  have hb : Integrable (fun y => ‖fderiv ℝ φ x‖ * B2 * (1 + ‖gradient U y‖)) μ :=
    ((integrable_const (1 : ℝ)).add hG1).const_mul _
  refine Integrable.mono' hb ?_ (ae_of_all _ fun y => ?_)
  · exact ((h2_continuous_B hv hU hφ).comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · rw [Real.norm_eq_abs]; exact hB φ x y _ (norm_nonneg _) le_rfl

/-! ### The function `ℓ = log u + U/θ` -/

/-- `ℓ = log u + U/θ`, the derivative of the free-energy density. -/
def h2_ell (θ v : ℝ) (U : Ch N → ℝ) (μ : Measure (Ch N)) (x : Ch N) : ℝ :=
  Real.log (h2_mu v μ x) + (1 / θ) * U x

theorem h2_continuous_mu1 {v : ℝ} (hv : 0 < v) (μ : Measure (Ch N)) [IsFiniteMeasure μ] :
    Continuous (h2_mu1 v μ) :=
  continuous_iff_continuousAt.2 fun x => (h2_hasFDerivAt_mu1 hv μ x).continuousAt

theorem h2_contDiff_mu {v : ℝ} (hv : 0 < v) (μ : Measure (Ch N)) [IsFiniteMeasure μ] :
    ContDiff ℝ 1 (h2_mu v μ) := by
  rw [contDiff_one_iff_hasFDerivAt]
  exact ⟨h2_mu1 v μ, h2_continuous_mu1 hv μ, h2_hasFDerivAt_mu hv μ⟩

theorem h2_contDiff_ell {θ v : ℝ} (hv : 0 < v) {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U) (μ : Measure (Ch N))
    [IsProbabilityMeasure μ] : ContDiff ℝ 1 (h2_ell θ v U μ) :=
  ((h2_contDiff_mu hv μ).log (fun x => (h2_mu_pos hv μ x).ne')).add (contDiff_const.mul hU)

theorem h2_ell_periodic {θ v : ℝ} {U : Ch N → ℝ} (hUper : ∀ z, U (z + cep_diag N) = U z) (μ : Measure (Ch N))
    (x : Ch N) : h2_ell θ v U μ (x + cep_diag N) = h2_ell θ v U μ x := by
  simp only [h2_ell, h2_mu_periodic, hUper]

theorem h2_fderiv_ell {θ v : ℝ} (hv : 0 < v) {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U) (μ : Measure (Ch N))
    [IsProbabilityMeasure μ] (x : Ch N) :
    fderiv ℝ (h2_ell θ v U μ) x = (h2_mu v μ x)⁻¹ • h2_mu1 v μ x + (1 / θ) • fderiv ℝ U x := by
  have h1 := (h2_hasFDerivAt_mu hv μ x).log (h2_mu_pos hv μ x).ne'
  have h2 := (hU.differentiable (by simp) x).hasFDerivAt.const_mul (1 / θ)
  exact (h1.add h2).fderiv

theorem h2_mu1_eq_of_ell {θ v : ℝ} (hv : 0 < v) {U : Ch N → ℝ} (hU : ContDiff ℝ 1 U) (μ : Measure (Ch N))
    [IsProbabilityMeasure μ] (x : Ch N) :
    h2_mu1 v μ x = h2_mu v μ x • (fderiv ℝ (h2_ell θ v U μ) x - (1 / θ) • fderiv ℝ U x) := by
  rw [h2_fderiv_ell hv hU μ x, add_sub_cancel_right, smul_smul, mul_inv_cancel₀ (h2_mu_pos hv μ x).ne', one_smul]

/-! ### The slice inequality -/

theorem h2_slice {θ v δ R : ℝ} (hθ : 0 < θ) (hv : 0 < v) (hδ : 0 < δ) (hR : 0 < R) {U : Ch N → ℝ}
    (hU : ContDiff ℝ 1 U) (hUper : ∀ z, U (z + cep_diag N) = U z) {K : ℝ≥0} (hK : LipschitzWith K (gradient U))
    (μ : Measure (Ch N)) [IsProbabilityMeasure μ] (hG1 : Integrable (fun y => ‖gradient U y‖) μ)
    (hG2 : Integrable (fun y => ‖gradient U y‖ ^ 2) μ) :
    ∫ x in cep_cell N, h2_chi R x * (h2_ell θ v U μ x + 1) * (∫ y, h2_A θ v U x y ∂μ) ≤
      -(θ * (1 - δ)) * (∫ x in cep_cell N, h2_chi R x * (h2_mu v μ x * ‖fderiv ℝ (h2_ell θ v U μ) x‖ ^ 2))
        + (K : ℝ) ^ 2 * (N * v) / (4 * θ * δ)
        - ∫ x in cep_cell N, ∫ y, (h2_ell θ v U μ x + 1) * h2_B θ v U (h2_chi R) x y ∂μ := by
  have hU1 : ContDiff ℝ 1 U := hU.of_le (by norm_num)
  have hℓ : ContDiff ℝ 1 (h2_ell θ v U μ) := h2_contDiff_ell hv hU1 μ
  have hχ : ContDiff ℝ 1 (h2_chi (N := N) R) := h2_contDiff_chi1 R
  have hℓper := h2_ell_periodic (θ := θ) (v := v) hUper μ
  have hχper := h2_chi_periodic (N := N) R
  have hμc := h2_continuous_mu hv μ
  obtain ⟨B2, hB2, hB⟩ := h2_B_bound hv θ U
  set ℓ := h2_ell θ v U μ with hℓdef
  set χ := h2_chi (N := N) R with hχdef
  have hχ0 : ∀ x, 2 * R < ‖h2_perp x‖ → χ x = 0 := fun x hx => h2_chi_support hR x hx
  have hφ : ContDiff ℝ 1 (fun x => χ x * (ℓ x + 1)) := hχ.mul (hℓ.add contDiff_const)
  have hφper : ∀ x, χ (x + cep_diag N) * (ℓ (x + cep_diag N) + 1) = χ x * (ℓ x + 1) := fun x => by
    rw [hχper, hℓper]
  have hφR : ∀ x, 2 * R < ‖h2_perp x‖ → χ x * (ℓ x + 1) = 0 := fun x hx => by rw [hχ0 x hx, zero_mul]
  have IBP := h2_ibp_mollified (θ := θ) hv hU1 hG1 hφ hφper hφR
  -- derivative of `φ`
  have hd : ∀ x, fderiv ℝ (fun x => χ x * (ℓ x + 1)) x = (ℓ x + 1) • fderiv ℝ χ x + χ x • fderiv ℝ ℓ x := by
    intro x
    have h1 := (hχ.differentiable (by simp) x).hasFDerivAt
    have h2 := ((hℓ.differentiable (by simp) x).hasFDerivAt).add_const 1
    have h3 := h1.mul h2
    change HasFDerivAt (fun x => χ x * (ℓ x + 1)) _ x at h3
    rw [h3.fderiv, add_comm]
  have hBs : ∀ x y, h2_B θ v U (fun x => χ x * (ℓ x + 1)) x y =
      (ℓ x + 1) * h2_B θ v U χ x y + χ x * h2_B θ v U ℓ x y := fun x y => h2_B_leibniz (hd x) y
  -- bounds
  obtain ⟨Cχ, hCχ0, hCχ⟩ := h2_bdd_of_far hχ hχper hχ0
  have hℓ1c : Continuous (fun x => ℓ x + 1) := hℓ.continuous.add continuous_const
  obtain ⟨c1, hc1⟩ := h2_bdd_tube hℓ1c (fun x => by rw [hℓper]) (2 * R)
  obtain ⟨cℓ, hcℓ⟩ := h2_bdd_tube (hℓ.continuous_fderiv (by simp)) (h2_fderiv_periodic hℓper) (2 * R)
  have hc1' : ∀ x, ‖h2_perp x‖ ≤ 2 * R → |ℓ x + 1| ≤ |c1| := fun x hx => by
    have := hc1 x hx; rw [Real.norm_eq_abs] at this; exact this.trans (le_abs_self _)
  have hcℓ' : ∀ x, ‖h2_perp x‖ ≤ 2 * R → ‖fderiv ℝ ℓ x‖ ≤ |cℓ| := fun x hx => (hcℓ x hx).trans (le_abs_self _)
  have hG : Integrable (fun y => 1 + ‖gradient U y‖) μ := (integrable_const 1).add hG1
  have hχd0 : ∀ x, 2 * R < ‖h2_perp x‖ → fderiv ℝ χ x = 0 := fun x hx => h2_fderiv_eq_zero_of_far hχ0 hx
  -- the two integrands
  have iH1 : Integrable (Function.uncurry fun x y => (ℓ x + 1) * h2_B θ v U χ x y)
      ((volume.restrict (cep_cell N)).prod μ) := by
    refine h2_integrable_prod_tube (R := 2 * R) (C := |c1| * (Cχ * B2)) (G := fun y => 1 + ‖gradient U y‖) ?_ ?_ hG ?_
    · exact ((hℓ.continuous.add continuous_const).comp continuous_fst).mul (h2_continuous_B hv hU1 hχ)
    · intro x y hx; simp [h2_B, hχd0 x hx]
    · intro x y
      have hp : 0 ≤ 1 + ‖gradient U y‖ := by positivity
      rw [abs_of_nonneg hp]
      by_cases hx : ‖h2_perp x‖ ≤ 2 * R
      · rw [abs_mul]
        have := hB χ x y Cχ hCχ0 (hCχ x).2
        calc |ℓ x + 1| * |h2_B θ v U χ x y| ≤ |c1| * (Cχ * B2 * (1 + ‖gradient U y‖)) :=
              mul_le_mul (hc1' x hx) this (abs_nonneg _) (abs_nonneg _)
          _ = |c1| * (Cχ * B2) * (1 + ‖gradient U y‖) := by ring
      · have : h2_B θ v U χ x y = 0 := by simp [h2_B, hχd0 x (not_le.1 hx)]
        simp [this]
        positivity
  have iH2 : Integrable (Function.uncurry fun x y => χ x * h2_B θ v U ℓ x y)
      ((volume.restrict (cep_cell N)).prod μ) := by
    refine h2_integrable_prod_tube (R := 2 * R) (C := |cℓ| * B2) (G := fun y => 1 + ‖gradient U y‖) ?_ ?_ hG ?_
    · exact (hχ.continuous.comp continuous_fst).mul (h2_continuous_B hv hU1 hℓ)
    · intro x y hx; simp [hχ0 x hx]
    · intro x y
      have hp : 0 ≤ 1 + ‖gradient U y‖ := by positivity
      rw [abs_of_nonneg hp]
      by_cases hx : ‖h2_perp x‖ ≤ 2 * R
      · rw [abs_mul]
        have := hB ℓ x y |cℓ| (abs_nonneg _) (hcℓ' x hx)
        calc |χ x| * |h2_B θ v U ℓ x y| ≤ 1 * (|cℓ| * B2 * (1 + ‖gradient U y‖)) := by
              refine mul_le_mul ?_ this (abs_nonneg _) zero_le_one
              rw [abs_of_nonneg (h2_chi_nonneg R x)]; exact h2_chi_le_one R x
          _ = _ := by ring
      · have : χ x = 0 := hχ0 x (not_le.1 hx)
        simp [this]
        positivity
  -- pointwise splitting of the inner integral
  have hinner : ∀ x, ∫ y, h2_B θ v U (fun x => χ x * (ℓ x + 1)) x y ∂μ =
      (∫ y, (ℓ x + 1) * h2_B θ v U χ x y ∂μ) + χ x * ∫ y, h2_B θ v U ℓ x y ∂μ := by
    intro x
    simp_rw [hBs]
    rw [integral_add ((h2_integrable_B hv hU1 hG1 hχ x).const_mul _) ((h2_integrable_B hv hU1 hG1 hℓ x).const_mul _)]
    simp only [integral_const_mul]
  have f1int : Integrable (fun x => ∫ y, (ℓ x + 1) * h2_B θ v U χ x y ∂μ) (volume.restrict (cep_cell N)) :=
    iH1.integral_prod_left
  have f2int : Integrable (fun x => χ x * ∫ y, h2_B θ v U ℓ x y ∂μ) (volume.restrict (cep_cell N)) := by
    have := iH2.integral_prod_left
    refine this.congr (ae_of_all _ fun x => ?_)
    simp only [Function.uncurry_apply_pair, integral_const_mul]
  have split : ∫ x in cep_cell N, ∫ y, h2_B θ v U (fun x => χ x * (ℓ x + 1)) x y ∂μ =
      (∫ x in cep_cell N, ∫ y, (ℓ x + 1) * h2_B θ v U χ x y ∂μ) +
        ∫ x in cep_cell N, χ x * ∫ y, h2_B θ v U ℓ x y ∂μ := by
    simp_rw [hinner]
    exact integral_add f1int f2int
  -- the lower bound for the second part
  have hC := h2_integrableOn_C hv hU1 hUper hK μ hG2
  have hCle := h2_integral_C_le hv hU1 hUper hK μ hG2
  have hJ : Integrable (fun x => χ x * (h2_mu v μ x * ‖fderiv ℝ ℓ x‖ ^ 2)) (volume.restrict (cep_cell N)) := by
    refine h2_integrable_cell_of_far (R := 2 * R) ?_ ?_ (fun x hx => by simp [hχ0 x hx])
    · exact hχ.continuous.mul (hμc.mul ((hℓ.continuous_fderiv (by simp)).norm.pow 2))
    · intro x; simp only [hχper, h2_mu_periodic, h2_fderiv_periodic hℓper]
  have hχC : Integrable (fun x => χ x * h2_C v U μ x) (volume.restrict (cep_cell N)) := by
    refine Integrable.mono' hC ((hχ.continuous.measurable.mul (h2_measurable_C hv hU1 μ)).aestronglyMeasurable)
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (h2_chi_nonneg R x) (h2_C_nonneg hv U μ x))]
    exact mul_le_of_le_one_left (h2_C_nonneg hv U μ x) (h2_chi_le_one R x)
  have hχCle : ∫ x in cep_cell N, χ x * h2_C v U μ x ≤ (K : ℝ) ^ 2 * (N * v) := by
    refine le_trans (integral_mono_of_nonneg (ae_of_all _ fun x => mul_nonneg (h2_chi_nonneg R x)
      (h2_C_nonneg hv U μ x)) hC (ae_of_all _ fun x => mul_le_of_le_one_left (h2_C_nonneg hv U μ x)
      (h2_chi_le_one R x))) hCle
  have hpt : ∀ x, θ * (1 - δ) * (χ x * (h2_mu v μ x * ‖fderiv ℝ ℓ x‖ ^ 2)) - (1 / (4 * θ * δ)) * (χ x * h2_C v U μ x)
      ≤ χ x * ∫ y, h2_B θ v U ℓ x y ∂μ := by
    intro x
    have h := h2_pointwise_diss hv hθ hδ hU1 hG1 hG2 x (fderiv ℝ ℓ x) (h2_mu1_eq_of_ell hv hU1 μ x)
    rw [← h2_Bint_ell hv hU1 hG1 ℓ x] at h
    have h' := mul_le_mul_of_nonneg_left h (h2_chi_nonneg R x)
    calc _ = χ x * (θ * (1 - δ) * h2_mu v μ x * ‖fderiv ℝ ℓ x‖ ^ 2 - h2_C v U μ x / (4 * θ * δ)) := by ring
      _ ≤ _ := h'
  have hgint : Integrable (fun x => θ * (1 - δ) * (χ x * (h2_mu v μ x * ‖fderiv ℝ ℓ x‖ ^ 2)) -
      (1 / (4 * θ * δ)) * (χ x * h2_C v U μ x)) (volume.restrict (cep_cell N)) :=
    (hJ.const_mul _).sub (hχC.const_mul _)
  have hmono := integral_mono hgint f2int hpt
  rw [integral_sub (hJ.const_mul _) (hχC.const_mul _), integral_const_mul, integral_const_mul] at hmono
  have hcb : (1 / (4 * θ * δ)) * ∫ x in cep_cell N, χ x * h2_C v U μ x ≤ (K : ℝ) ^ 2 * (N * v) / (4 * θ * δ) := by
    calc _ ≤ (1 / (4 * θ * δ)) * ((K : ℝ) ^ 2 * (N * v)) :=
          mul_le_mul_of_nonneg_left hχCle (by positivity)
      _ = _ := by ring
  have hL : ∫ x in cep_cell N, χ x * (ℓ x + 1) * (∫ y, h2_A θ v U x y ∂μ) =
      -∫ x in cep_cell N, ∫ y, h2_B θ v U (fun x => χ x * (ℓ x + 1)) x y ∂μ := IBP
  rw [hL, split]
  nlinarith [hmono, hcb]

end HRS.MC.CepH2
