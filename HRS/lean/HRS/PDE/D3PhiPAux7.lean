import HRS.PDE.D3PhiPAux6

/-!
# D3PHIP, helper 7: absolute continuity of `r ↦ A(r,x)` and the pointwise (in `x`) fundamental theorem of calculus
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS

variable {n : ℕ}

/-- A function continuous on `[0,T]` whose derivative on `(0,T)` is bounded is absolutely continuous. -/
theorem d3pp_ac_of_deriv {f f' : ℝ → ℝ} {T K : ℝ} (hT : 0 ≤ T) (hc : ContinuousOn f (Set.Icc 0 T))
    (hd : ∀ r ∈ Set.Ioo 0 T, HasDerivAt f (f' r) r) (hK : ∀ r ∈ Set.Ioo 0 T, |f' r| ≤ K) :
    AbsolutelyContinuousOnInterval f 0 T := by
  have hK0 : ∀ a b : ℝ, a ∈ Set.Icc 0 T → b ∈ Set.Icc 0 T → a < b → |f b - f a| ≤ K * (b - a) := by
    intro a b ha hb hab
    obtain ⟨c, hc1, hc2⟩ := exists_hasDerivAt_eq_slope f f' hab
      (hc.mono (Set.Icc_subset_Icc ha.1 hb.2))
      (fun x hx => hd x ⟨lt_of_le_of_lt ha.1 hx.1, lt_of_lt_of_le hx.2 hb.2⟩)
    have h1 : f b - f a = f' c * (b - a) := by
      rw [hc2, div_mul_cancel₀ _ (sub_pos.2 hab).ne']
    rw [h1, abs_mul, abs_of_pos (sub_pos.2 hab)]
    exact mul_le_mul_of_nonneg_right (hK c ⟨lt_of_le_of_lt ha.1 hc1.1, lt_of_lt_of_le hc1.2 hb.2⟩)
      (sub_pos.2 hab).le
  have hlip : LipschitzOnWith K.toNNReal f (Set.Icc 0 T) := by
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal']
    rcases lt_trichotomy a b with h | h | h
    · rw [abs_sub_comm a b, abs_of_pos (sub_pos.2 h), abs_sub_comm (f a)]
      calc |f b - f a| ≤ K * (b - a) := hK0 a b ha hb h
        _ ≤ max K 0 * (b - a) := mul_le_mul_of_nonneg_right (le_max_left _ _) (sub_pos.2 h).le
    · subst h; simp
    · rw [abs_of_pos (sub_pos.2 h)]
      calc |f a - f b| ≤ K * (a - b) := hK0 b a hb ha h
        _ ≤ max K 0 * (a - b) := mul_le_mul_of_nonneg_right (le_max_left _ _) (sub_pos.2 h).le
  refine LipschitzOnWith.absolutelyContinuousOnInterval (K := K.toNNReal) ?_
  rw [Set.uIcc_of_le hT]
  exact hlip

/-- `exp` is Lipschitz on every bounded interval. -/
theorem d3pp_exp_lip (C : ℝ) : ∃ K : NNReal, LipschitzOnWith K Real.exp (Set.Icc (-C) C) :=
  ContDiffOn.exists_lipschitzOnWith (n := 1) Real.contDiff_exp.contDiffOn (by decide) (convex_Icc _ _)
    isCompact_Icc

section time

variable {κ : ℝ} {U : Torus n → ℝ} {T : ℝ} {w : ℝ → Torus n → ℝ} {ψ ψt : ℝ → Torus n → ℝ}

theorem d3pp_A_eq_exp (hκ : 0 < κ) (hU : Torus.IsSmooth U) (hw : D3Classical κ U T w)
    (hψ : IsC12Test T ψ ψt) (p : ℝ → ℝ) {r : ℝ} (hr : r ∈ Set.Icc 0 T) (x : Torus n) :
    d3pp_A κ U ψ w p r x = Real.exp (p r * d3pp_ell κ U ψ w r x + d3pp_m κ U ψ r x) := by
  unfold d3pp_A d3pp_ell
  have hh := d3pp_h_pos hκ hU hw hψ (⟨r, hr⟩, x)
  simp only at hh
  rw [Real.rpow_def_of_pos hh, Real.exp_add, mul_comm (Real.log _) (p r)]

/-- The pointwise exponent integrand is absolutely continuous in time. -/
theorem d3pp_A_ac (hκ : 0 < κ) (hU : Torus.IsSmooth U) (hT : 0 < T) (hw : D3Classical κ U T w)
    (hψ : IsC12Test T ψ ψt) {p : ℝ → ℝ} (hpac : AbsolutelyContinuousOnInterval p 0 T)
    (x : Torus n) :
    AbsolutelyContinuousOnInterval (fun r => d3pp_A κ U ψ w p r x) 0 T := by
  have hT0 := hT.le
  have hmem : ∀ r ∈ Set.uIcc (0 : ℝ) T, r ∈ Set.Icc (0 : ℝ) T := fun r hr => by
    rwa [Set.uIcc_of_le hT0] at hr
  -- Lipschitz bounds for ℓ and m
  obtain ⟨K1, hK1⟩ := d3a_bound (d3pp_ellr_cont_sub hκ hU hT hw hψ)
  obtain ⟨K2, hK2⟩ := d3a_bound (d3pp_mr_cont_sub hκ hU hT hψ)
  have hell : AbsolutelyContinuousOnInterval (fun r => d3pp_ell κ U ψ w r x) 0 T :=
    d3pp_ac_of_deriv hT0 (d3a_contOn_time (F := fun r x => d3pp_ell κ U ψ w r x)
        (d3pp_ell_cont_sub hκ hU hw hψ) x)
      (d3pp_ell_hasDeriv hκ hU hw hψ x) (K := K1) (fun r hr => by
        have := hK1 r (Set.Ioo_subset_Icc_self hr) x
        simpa using this)
  have hm : AbsolutelyContinuousOnInterval (fun r => d3pp_m κ U ψ r x) 0 T :=
    d3pp_ac_of_deriv hT0 (d3a_contOn_time (F := fun r x => d3pp_m κ U ψ r x)
        (d3pp_m_cont_sub hκ hU hψ) x)
      (d3pp_m_hasDeriv hκ hU hψ x) (K := K2) (fun r hr => by
        have := hK2 r (Set.Ioo_subset_Icc_self hr) x
        simpa using this)
  have hΛ : AbsolutelyContinuousOnInterval
      (fun r => p r * d3pp_ell κ U ψ w r x + d3pp_m κ U ψ r x) 0 T :=
    (hpac.fun_mul hell).fun_add hm
  obtain ⟨C, hC⟩ := hΛ.exists_bound
  obtain ⟨K, hK⟩ := d3pp_exp_lip C
  have hexp := hK.comp_absolutelyContinuousOnInterval (g := fun r => p r * d3pp_ell κ U ψ w r x +
    d3pp_m κ U ψ r x) (a := 0) (b := T) (fun r hr => by
      have := hC r hr
      rw [Real.norm_eq_abs, abs_le] at this
      exact ⟨this.1, this.2⟩) hΛ
  exact hexp.congr fun r hr => (d3pp_A_eq_exp hκ hU hw hψ p (hmem r hr) x).symm

/-- Pointwise derivative of `A` at a point where `p` is differentiable. -/
theorem d3pp_A_hasDeriv (hκ : 0 < κ) (hU : Torus.IsSmooth U) (hw : D3Classical κ U T w)
    (hψ : IsC12Test T ψ ψt) {p : ℝ → ℝ} (x : Torus n) {r : ℝ} (hr : r ∈ Set.Ioo 0 T)
    (hpr : DifferentiableAt ℝ p r) :
    HasDerivAt (fun r => d3pp_A κ U ψ w p r x) (d3pp_D κ U ψ ψt w p (deriv p) r x) r := by
  have h1 := ((hpr.hasDerivAt.mul (d3pp_ell_hasDeriv hκ hU hw hψ x r hr)).add
    (d3pp_m_hasDeriv hκ hU hψ x r hr)).exp
  have heq : (fun r' => d3pp_A κ U ψ w p r' x) =ᶠ[𝓝 r]
      fun r' => Real.exp (p r' * d3pp_ell κ U ψ w r' x + d3pp_m κ U ψ r' x) := by
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with r' hr'
    exact d3pp_A_eq_exp hκ hU hw hψ p (Set.Ioo_subset_Icc_self hr') x
  refine (h1.congr_of_eventuallyEq heq).congr_deriv ?_
  simp only [Pi.add_apply, Pi.mul_apply]
  unfold d3pp_D
  rw [d3pp_A_eq_exp hκ hU hw hψ p (Set.Ioo_subset_Icc_self hr) x]
  ring

/-- Pointwise (in `x`) fundamental theorem of calculus for `A`. -/
theorem d3pp_FTC_x (hκ : 0 < κ) (hU : Torus.IsSmooth U) (hT : 0 < T) (hw : D3Classical κ U T w)
    (hψ : IsC12Test T ψ ψt) {p : ℝ → ℝ} (hpac : AbsolutelyContinuousOnInterval p 0 T)
    (x : Torus n) {t : ℝ} (ht : t ∈ Set.Icc 0 T) :
    ∫ r in (0 : ℝ)..t, d3pp_D κ U ψ ψt w p (deriv p) r x =
      d3pp_A κ U ψ w p t x - d3pp_A κ U ψ w p 0 x := by
  have hT0 := hT.le
  have hAac := d3pp_A_ac hκ hU hT hw hψ hpac x
  have hsub : Set.uIcc 0 t ⊆ Set.uIcc 0 T := by
    rw [Set.uIcc_of_le hT0, Set.uIcc_of_le ht.1]; exact Set.Icc_subset_Icc le_rfl ht.2
  have hAt := hAac.mono hsub
  rw [← hAt.integral_deriv_eq_sub]
  refine intervalIntegral.integral_congr_ae ?_
  have hneT : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ T := by simp [ae_iff, measure_singleton]
  filter_upwards [hpac.ae_differentiableAt, hneT] with r hr hrT hrmem
  rw [Set.uIoc_of_le ht.1] at hrmem
  have hrIoo : r ∈ Set.Ioo 0 T := ⟨hrmem.1, lt_of_le_of_ne (hrmem.2.trans ht.2) hrT⟩
  have hdiff : DifferentiableAt ℝ p r := hr (by rw [Set.uIcc_of_le hT0]; exact Set.Ioo_subset_Icc_self hrIoo)
  exact (d3pp_A_hasDeriv hκ hU hw hψ x hrIoo hdiff).deriv.symm

end time

end HRS
