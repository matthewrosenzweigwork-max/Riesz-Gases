import HRS.MC.CepH2Aux27

/-!
# CEPH2, helper 28: uniform bound and tail of the cut-off error `Eχ_R(s)`
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Pointwise

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

theorem h2_lintegral_Om_prod_le {v : ℝ} (hv : 0 < v) {a₁ b₁ : ℝ} (ha₁ : 0 ≤ a₁) (hb₁ : 0 ≤ b₁) (R : ℝ)
    (μ : Measure (Ch N)) [IsProbabilityMeasure μ] (hmom : Integrable (fun y => ‖h2_perp y‖ ^ 2) μ) :
    ∫⁻ z, h2_Om v a₁ b₁ R z.1 z.2 ∂((volume.restrict (cep_cell N)).prod μ) ≤
      ENNReal.ofReal (h2_A2 N v a₁ b₁ + h2_B2 (N := N) v a₁ b₁ * ∫ y, ‖h2_perp y‖ ^ 2 ∂μ) := by
  have h := lintegral_prod (μ := volume.restrict (cep_cell N)) (ν := μ)
    (fun z : Ch N × Ch N => h2_Om v a₁ b₁ R z.1 z.2) (h2_measurable_Om hv a₁ b₁ R).aemeasurable
  refine h.trans_le ?_
  exact h2_lintegral_Om_le hv ha₁ hb₁ R μ hmom

theorem h2_tendsto_Om_prod {v : ℝ} (hv : 0 < v) {a₁ b₁ : ℝ} (ha₁ : 0 ≤ a₁) (hb₁ : 0 ≤ b₁)
    (μ : Measure (Ch N)) [IsProbabilityMeasure μ] (hmom : Integrable (fun y => ‖h2_perp y‖ ^ 2) μ) :
    Tendsto (fun n : ℕ => ∫⁻ z, h2_Om v a₁ b₁ ((n : ℝ) + 1) z.1 z.2 ∂((volume.restrict (cep_cell N)).prod μ))
      atTop (𝓝 0) := by
  have hfin : ∫⁻ z, h2_Om v a₁ b₁ 0 z.1 z.2 ∂((volume.restrict (cep_cell N)).prod μ) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h2_lintegral_Om_prod_le hv ha₁ hb₁ 0 μ hmom)
  have := tendsto_lintegral_of_dominated_convergence (μ := (volume.restrict (cep_cell N)).prod μ)
    (F := fun (n : ℕ) (z : Ch N × Ch N) => h2_Om v a₁ b₁ ((n : ℝ) + 1) z.1 z.2) (f := fun _ => 0)
    (fun z => h2_Om v a₁ b₁ 0 z.1 z.2)
    (fun n => (h2_measurable_Om hv a₁ b₁ _)) (fun n => ae_of_all _ fun z => h2_Om_le_Om0 a₁ b₁ _ ha₁ hb₁ z.1 z.2)
    hfin (ae_of_all _ fun z => by
      refine tendsto_const_nhds.congr' ?_
      rw [EventuallyEq, eventually_atTop]
      refine ⟨⌈‖h2_perp z.1‖⌉₊ + 1, fun n hn => ?_⟩
      have h1 : ‖h2_perp z.1‖ < (n : ℝ) + 1 := by
        have := Nat.le_ceil ‖h2_perp z.1‖
        have h2 : (⌈‖h2_perp z.1‖⌉₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn
        linarith
      unfold h2_Om
      rw [h2_ind_of_lt h1]
      simp)
  simpa using this

section
variable {θ v : ℝ} {U : Ch N → ℝ} {K : ℝ≥0} {μ : ℝ → Measure (Ch N)} {T M : ℝ}

theorem H2Set.int_e_prod (S : H2Set θ v U K μ T M) {R : ℝ} (hR : 0 < R) (s : ℝ) :
    Integrable (Function.uncurry fun (x y : Ch N) => (h2_ell θ v U (μ s) x + 1) * h2_B θ v U (h2_chi R) x y)
      ((volume.restrict (cep_cell N)).prod (μ s)) := by
  haveI := S.hprob s
  obtain ⟨B2, hB2, hB⟩ := h2_B_bound S.hv θ U
  obtain ⟨cE, hcE, hE⟩ := S.ell_bound
  obtain ⟨Cχ, hCχ0, hCχ⟩ := h2_chi_bdd (N := N) hR
  have hℓ := h2_contDiff_ell (θ := θ) S.hv S.hU1 (μ s)
  have hd0 : ∀ x : Ch N, 2 * R < ‖h2_perp x‖ → fderiv ℝ (h2_chi R) x = 0 := fun x hx =>
    h2_fderiv_eq_zero_of_far (fun x hx => h2_chi_support hR x hx) hx
  have hG : Integrable (fun y => 1 + ‖gradient U y‖) (μ s) := (integrable_const 1).add (S.gradInt s).1
  refine h2_integrable_prod_tube (R := 2 * R) (C := (cE * (1 + (2 * R) ^ 2) + 1) * (Cχ * B2))
    (G := fun y => 1 + ‖gradient U y‖) ?_ ?_ hG ?_
  · exact ((hℓ.continuous.add continuous_const).comp continuous_fst).mul
      (h2_continuous_B S.hv S.hU1 (h2_contDiff_chi1 R))
  · intro x y hx; simp [h2_B, hd0 x hx]
  · intro x y
    have hp : 0 ≤ 1 + ‖gradient U y‖ := by positivity
    rw [abs_of_nonneg hp]
    by_cases hx : ‖h2_perp x‖ ≤ 2 * R
    · rw [abs_mul]
      have h2 : |h2_ell θ v U (μ s) x + 1| ≤ cE * (1 + (2 * R) ^ 2) + 1 := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_one]
        have := hE s x
        have h3 : 1 + ‖h2_perp x‖ ^ 2 ≤ 1 + (2 * R) ^ 2 := by nlinarith [norm_nonneg (h2_perp x)]
        nlinarith [mul_le_mul_of_nonneg_left h3 hcE]
      have := hB (h2_chi R) x y Cχ hCχ0 (hCχ x)
      calc |h2_ell θ v U (μ s) x + 1| * |h2_B θ v U (h2_chi R) x y|
          ≤ (cE * (1 + (2 * R) ^ 2) + 1) * (Cχ * B2 * (1 + ‖gradient U y‖)) :=
            mul_le_mul h2 this (abs_nonneg _) (by positivity)
        _ = _ := by ring
    · have : h2_B θ v U (h2_chi R) x y = 0 := by simp [h2_B, hd0 x (not_le.1 hx)]
      simp [this]
      positivity

theorem H2Set.E_tail (S : H2Set θ v U K μ T M) :
    ∃ CE : ℝ, 0 ≤ CE ∧ (∀ (s R : ℝ), 1 ≤ R → |h2_Echi θ v U μ R s| ≤ CE) ∧
      (∀ s : ℝ, Tendsto (fun n : ℕ => h2_Echi θ v U μ ((n : ℝ) + 1) s) atTop (𝓝 0)) := by
  obtain ⟨a₁, b₁, CE, ha₁, hb₁, hCE, hdom⟩ := S.E_dom
  have hM0 := S.hM0
  have hA2 : 0 ≤ h2_A2 N v a₁ b₁ := by unfold h2_A2; have := S.hv; positivity
  have hB2 : 0 ≤ h2_B2 (N := N) v a₁ b₁ := by unfold h2_B2; have := S.hv; positivity
  -- the key estimate
  have key : ∀ (s R : ℝ), 1 ≤ R → |h2_Echi θ v U μ R s| ≤
      (ENNReal.ofReal CE * ∫⁻ z, h2_Om v a₁ b₁ R z.1 z.2 ∂((volume.restrict (cep_cell N)).prod (μ s))).toReal := by
    intro s R hR
    haveI := S.hprob s
    have hR0 : 0 < R := by linarith
    have hint := S.int_e_prod hR0 s
    have e1 : h2_Echi θ v U μ R s = ∫ z, (h2_ell θ v U (μ s) z.1 + 1) * h2_B θ v U (h2_chi R) z.1 z.2
        ∂((volume.restrict (cep_cell N)).prod (μ s)) :=
      (integral_prod _ hint).symm
    have hpt : ∀ x y : Ch N, ‖(h2_ell θ v U (μ s) x + 1) * h2_B θ v U (h2_chi R) x y‖ₑ ≤
        ENNReal.ofReal CE * h2_Om v a₁ b₁ R x y := by
      intro x y
      have hI : 0 ≤ h2_ind R x * (‖h2_perp x‖ * (a₁ + b₁ * ‖h2_perp y‖)) :=
        mul_nonneg (h2_ind_nonneg R x) (by positivity)
      calc ‖(h2_ell θ v U (μ s) x + 1) * h2_B θ v U (h2_chi R) x y‖ₑ
          = ENNReal.ofReal |(h2_ell θ v U (μ s) x + 1) * h2_B θ v U (h2_chi R) x y| := by
            rw [← ofReal_norm, Real.norm_eq_abs]
        _ ≤ ENNReal.ofReal (CE * (h2_ind R x * (‖h2_perp x‖ * (a₁ + b₁ * ‖h2_perp y‖)) *
              h2_per (2 * v) (x - y))) := ENNReal.ofReal_le_ofReal (hdom s R x y hR)
        _ = ENNReal.ofReal CE * h2_Om v a₁ b₁ R x y := by
            unfold h2_Om
            rw [ENNReal.ofReal_mul hCE, ENNReal.ofReal_mul hI]
            ring
    have hfin : ENNReal.ofReal CE * ∫⁻ z, h2_Om v a₁ b₁ R z.1 z.2 ∂((volume.restrict (cep_cell N)).prod (μ s)) ≠ ⊤ :=
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h2_lintegral_Om_prod_le S.hv ha₁ hb₁ R (μ s) (S.hmom s)))
    have hle : ∫⁻ z, ‖(h2_ell θ v U (μ s) z.1 + 1) * h2_B θ v U (h2_chi R) z.1 z.2‖ₑ
        ∂((volume.restrict (cep_cell N)).prod (μ s)) ≤
        ENNReal.ofReal CE * ∫⁻ z, h2_Om v a₁ b₁ R z.1 z.2 ∂((volume.restrict (cep_cell N)).prod (μ s)) := by
      have hm : Measurable (fun z : Ch N × Ch N => h2_Om v a₁ b₁ R z.1 z.2) :=
        h2_measurable_Om (N := N) S.hv a₁ b₁ R
      rw [← lintegral_const_mul _ hm]
      exact lintegral_mono fun z => hpt z.1 z.2
    rw [e1, ← Real.norm_eq_abs]
    calc _ ≤ ∫ z, ‖(h2_ell θ v U (μ s) z.1 + 1) * h2_B θ v U (h2_chi R) z.1 z.2‖
          ∂((volume.restrict (cep_cell N)).prod (μ s)) := norm_integral_le_integral_norm _
      _ = (∫⁻ z, ‖(h2_ell θ v U (μ s) z.1 + 1) * h2_B θ v U (h2_chi R) z.1 z.2‖ₑ
          ∂((volume.restrict (cep_cell N)).prod (μ s))).toReal :=
          integral_norm_eq_lintegral_enorm hint.aestronglyMeasurable
      _ ≤ _ := ENNReal.toReal_mono hfin hle
  refine ⟨CE * (h2_A2 N v a₁ b₁ + h2_B2 (N := N) v a₁ b₁ * M), by positivity, fun s R hR => ?_, fun s => ?_⟩
  · haveI := S.hprob s
    refine (key s R hR).trans ?_
    have h1 := h2_lintegral_Om_prod_le S.hv ha₁ hb₁ R (μ s) (S.hmom s)
    have h2 : ∫ y, ‖h2_perp y‖ ^ 2 ∂(μ s) ≤ M := S.hM s
    have h3 : h2_A2 N v a₁ b₁ + h2_B2 (N := N) v a₁ b₁ * ∫ y, ‖h2_perp y‖ ^ 2 ∂(μ s) ≤
        h2_A2 N v a₁ b₁ + h2_B2 (N := N) v a₁ b₁ * M := by nlinarith
    have h4 := mul_le_mul' (le_refl (ENNReal.ofReal CE)) h1
    rw [← ENNReal.ofReal_mul hCE] at h4
    calc _ ≤ (ENNReal.ofReal (CE * (h2_A2 N v a₁ b₁ + h2_B2 (N := N) v a₁ b₁ *
            ∫ y, ‖h2_perp y‖ ^ 2 ∂(μ s)))).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h4
      _ = CE * (h2_A2 N v a₁ b₁ + h2_B2 (N := N) v a₁ b₁ * ∫ y, ‖h2_perp y‖ ^ 2 ∂(μ s)) :=
          ENNReal.toReal_ofReal (mul_nonneg hCE (add_nonneg hA2 (mul_nonneg hB2
            (integral_nonneg fun y => by positivity))))
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 hCE
  · haveI := S.hprob s
    have ht := h2_tendsto_Om_prod S.hv ha₁ hb₁ (μ s) (S.hmom s)
    have ht2 := ENNReal.Tendsto.const_mul (a := ENNReal.ofReal CE) ht (Or.inr ENNReal.ofReal_ne_top)
    rw [mul_zero] at ht2
    have ht3 := (ENNReal.tendsto_toReal (a := 0) ENNReal.zero_ne_top).comp ht2
    simp only [ENNReal.toReal_zero] at ht3
    refine squeeze_zero_norm (fun n => ?_) ht3
    rw [Real.norm_eq_abs]
    exact key s _ (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith)

end

end HRS.MC.CepH2
