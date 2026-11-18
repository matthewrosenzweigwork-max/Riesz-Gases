import HRS.MC.CepH2Aux13

/-!
# CEPH2, helper 14: transverse cut-offs

`χ_R(x) = ρ(‖P⊥ x‖² / R²)` with `ρ` smooth, `ρ = 1` on `(-∞,1]`, `ρ = 0` on `[4,∞)`, antitone.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators Pointwise

noncomputable section

namespace HRS.MC.CepH2

open HRS HRS.MC.Cepa

variable {N : ℕ} [NeZero N]

/-- Smooth non-increasing profile. -/
def h2_rho (s : ℝ) : ℝ := Real.smoothTransition ((4 - s) / 3)

theorem h2_rho_contDiff : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h2_rho := by
  unfold h2_rho
  exact Real.smoothTransition.contDiff.comp (((contDiff_const.sub contDiff_id)).div_const 3)

theorem h2_rho_one {s : ℝ} (hs : s ≤ 1) : h2_rho s = 1 := by
  unfold h2_rho; exact Real.smoothTransition.one_of_one_le (by linarith)

theorem h2_rho_zero {s : ℝ} (hs : 4 ≤ s) : h2_rho s = 0 := by
  unfold h2_rho; exact Real.smoothTransition.zero_of_nonpos (by linarith)

theorem h2_rho_nonneg (s : ℝ) : 0 ≤ h2_rho s := Real.smoothTransition.nonneg _

theorem h2_rho_le_one (s : ℝ) : h2_rho s ≤ 1 := Real.smoothTransition.le_one _

theorem h2_rho_anti : Antitone h2_rho := by
  intro a b hab
  unfold h2_rho
  exact Real.smoothTransition.monotone (by linarith)

theorem h2_continuous_deriv_rho : Continuous (deriv h2_rho) :=
  h2_rho_contDiff.continuous_deriv (by simp)

theorem h2_deriv_rho_eq_zero {s : ℝ} (hs : s ≤ 1 ∨ 4 ≤ s) : deriv h2_rho s = 0 := by
  have h1 : ∀ s : ℝ, s < 1 → deriv h2_rho s = 0 := by
    intro s hs
    have : h2_rho =ᶠ[𝓝 s] fun _ => (1 : ℝ) :=
      Filter.mem_of_superset (Iio_mem_nhds hs) fun t ht => h2_rho_one (le_of_lt ht)
    rw [this.deriv_eq]; simp
  have h4 : ∀ s : ℝ, 4 < s → deriv h2_rho s = 0 := by
    intro s hs
    have : h2_rho =ᶠ[𝓝 s] fun _ => (0 : ℝ) :=
      Filter.mem_of_superset (Ioi_mem_nhds hs) fun t ht => h2_rho_zero (le_of_lt ht)
    rw [this.deriv_eq]; simp
  have hcl : IsClosed {s : ℝ | deriv h2_rho s = 0} := isClosed_eq h2_continuous_deriv_rho continuous_const
  rcases hs with hs | hs
  · have : Iic (1 : ℝ) ⊆ {s | deriv h2_rho s = 0} := by
      rw [← closure_Iio]; exact closure_minimal (fun s hs => h1 s hs) hcl
    exact this hs
  · have : Ici (4 : ℝ) ⊆ {s | deriv h2_rho s = 0} := by
      rw [← closure_Ioi]; exact closure_minimal (fun s hs => h4 s hs) hcl
    exact this hs

theorem h2_deriv_rho_bound : ∃ L : ℝ, 0 ≤ L ∧ ∀ s, |deriv h2_rho s| ≤ L := by
  obtain ⟨L, hL⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 4)).exists_bound_of_continuousOn
    h2_continuous_deriv_rho.continuousOn
  refine ⟨max L 0, le_max_right _ _, fun s => ?_⟩
  by_cases hs : s ∈ Icc (1 : ℝ) 4
  · exact (by simpa [Real.norm_eq_abs] using hL s hs : |deriv h2_rho s| ≤ L).trans (le_max_left _ _)
  · have : s ≤ 1 ∨ 4 ≤ s := by
      by_contra h; push Not at h; exact hs ⟨h.1.le, h.2.le⟩
    rw [h2_deriv_rho_eq_zero this]; simp

/-- The transverse cut-off. -/
def h2_chi (R : ℝ) (x : Ch N) : ℝ := h2_rho (‖h2_perp x‖ ^ 2 / R ^ 2)

theorem h2_contDiff_perp_sq : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : Ch N => ‖h2_perp x‖ ^ 2) :=
  (contDiff_norm_sq ℝ).comp (h2_permL N).contDiff

theorem h2_contDiff_chi (R : ℝ) : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (h2_chi (N := N) R) := by
  unfold h2_chi
  exact h2_rho_contDiff.comp (h2_contDiff_perp_sq.div_const _)

theorem h2_chi_periodic (R : ℝ) (x : Ch N) : h2_chi R (x + cep_diag N) = h2_chi R x := by
  unfold h2_chi; rw [h2_perp_periodic]

theorem h2_chi_nonneg (R : ℝ) (x : Ch N) : 0 ≤ h2_chi R x := h2_rho_nonneg _

theorem h2_chi_le_one (R : ℝ) (x : Ch N) : h2_chi R x ≤ 1 := h2_rho_le_one _

theorem h2_chi_eq_one {R : ℝ} (hR : 0 < R) {x : Ch N} (hx : ‖h2_perp x‖ ≤ R) : h2_chi R x = 1 := by
  unfold h2_chi
  refine h2_rho_one ?_
  rw [div_le_one (by positivity)]
  nlinarith [norm_nonneg (h2_perp x)]

theorem h2_chi_eq_zero {R : ℝ} (hR : 0 < R) {x : Ch N} (hx : 2 * R ≤ ‖h2_perp x‖) : h2_chi R x = 0 := by
  unfold h2_chi
  refine h2_rho_zero ?_
  rw [le_div_iff₀ (by positivity)]
  nlinarith

theorem h2_chi_mono {R R' : ℝ} (hR : 0 < R) (hRR : R ≤ R') (x : Ch N) : h2_chi R x ≤ h2_chi R' x := by
  unfold h2_chi
  refine h2_rho_anti ?_
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ hR.le hRR 2)

theorem h2_chi_support {R : ℝ} (hR : 0 < R) (x : Ch N) (hx : 2 * R < ‖h2_perp x‖) : h2_chi R x = 0 :=
  h2_chi_eq_zero hR hx.le

/-- Gradient of the cut-off: vanishes in the tube and `‖∇χ_R‖ ‖P⊥ x‖ ≤ 8 L`. -/
theorem h2_fderiv_chi_bound : ∃ L : ℝ, 0 ≤ L ∧ ∀ {R : ℝ}, 0 < R → ∀ x : Ch N,
    (‖h2_perp x‖ ≤ R → fderiv ℝ (h2_chi R) x = 0) ∧ ‖fderiv ℝ (h2_chi R) x‖ * ‖h2_perp x‖ ≤ L := by
  obtain ⟨L, hL0, hL⟩ := h2_deriv_rho_bound
  refine ⟨8 * L, by positivity, fun {R} hR x => ?_⟩
  have hq : HasFDerivAt (fun x : Ch N => ‖h2_perp x‖ ^ 2)
      ((2 • innerSL ℝ (h2_perp x)).comp (h2_permL N : Ch N →L[ℝ] Ch N)) x := by
    have := (hasStrictFDerivAt_norm_sq (h2_permL N x)).hasFDerivAt.comp x (h2_permL N).hasFDerivAt
    exact this
  have hdiv : HasFDerivAt (fun x : Ch N => ‖h2_perp x‖ ^ 2 / R ^ 2)
      ((1 / R ^ 2) • ((2 • innerSL ℝ (h2_perp x)).comp (h2_permL N : Ch N →L[ℝ] Ch N))) x := by
    have h0 := hq.const_mul (1 / R ^ 2)
    have hf : (fun x : Ch N => ‖h2_perp x‖ ^ 2 / R ^ 2) = fun x => 1 / R ^ 2 * ‖h2_perp x‖ ^ 2 := by
      funext x; ring
    rw [hf]; exact h0
  have hρ : HasDerivAt h2_rho (deriv h2_rho (‖h2_perp x‖ ^ 2 / R ^ 2)) (‖h2_perp x‖ ^ 2 / R ^ 2) :=
    (h2_rho_contDiff.differentiable (by simp) _).hasDerivAt
  have hχ := hρ.comp_hasFDerivAt x hdiv
  have hfd : fderiv ℝ (h2_chi R) x = deriv h2_rho (‖h2_perp x‖ ^ 2 / R ^ 2) •
      ((1 / R ^ 2) • ((2 • innerSL ℝ (h2_perp x)).comp (h2_permL N : Ch N →L[ℝ] Ch N))) := hχ.fderiv
  constructor
  · intro hx
    rw [hfd, h2_deriv_rho_eq_zero (Or.inl ?_)]
    · simp
    · rw [div_le_one (by positivity)]
      nlinarith [norm_nonneg (h2_perp x)]
  · by_cases hp : ‖h2_perp x‖ ≤ R
    · rw [hfd, h2_deriv_rho_eq_zero (Or.inl ?_)]
      · simp; positivity
      · rw [div_le_one (by positivity)]
        nlinarith [norm_nonneg (h2_perp x)]
    · push Not at hp
      by_cases hp2 : 2 * R ≤ ‖h2_perp x‖
      · rw [hfd, h2_deriv_rho_eq_zero (Or.inr ?_)]
        · simp; positivity
        · rw [le_div_iff₀ (by positivity)]
          nlinarith
      · push Not at hp2
        rw [hfd]
        have hperm : ‖(h2_permL N : Ch N →L[ℝ] Ch N)‖ ≤ 1 :=
          ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun w => by
            simpa [h2_permL_apply] using h2_norm_perp_le w
        have h1 : ‖(2 • innerSL ℝ (h2_perp x)).comp (h2_permL N : Ch N →L[ℝ] Ch N)‖ ≤ 2 * ‖h2_perp x‖ := by
          refine le_trans (ContinuousLinearMap.opNorm_comp_le _ _) ?_
          have h3 : ‖(2 • innerSL ℝ (h2_perp x) : Ch N →L[ℝ] ℝ)‖ ≤ 2 * ‖h2_perp x‖ := by
            have := norm_nsmul_le (n := 2) (a := (innerSL ℝ (h2_perp x) : Ch N →L[ℝ] ℝ))
            rw [innerSL_apply_norm] at this
            simpa using this
          calc _ ≤ (2 * ‖h2_perp x‖) * 1 := mul_le_mul h3 hperm (norm_nonneg _) (by positivity)
            _ = _ := mul_one _
        have h2 : ‖deriv h2_rho (‖h2_perp x‖ ^ 2 / R ^ 2) •
            ((1 / R ^ 2) • ((2 • innerSL ℝ (h2_perp x)).comp (h2_permL N : Ch N →L[ℝ] Ch N)))‖ ≤
            L * ((1 / R ^ 2) * (2 * ‖h2_perp x‖)) := by
          refine le_trans (ContinuousLinearMap.opNorm_smul_le _ _) ?_
          refine mul_le_mul (by simpa [Real.norm_eq_abs] using hL _) ?_ (norm_nonneg _) hL0
          refine le_trans (ContinuousLinearMap.opNorm_smul_le _ _) ?_
          have hn : ‖(1 / R ^ 2 : ℝ)‖ = 1 / R ^ 2 := Real.norm_of_nonneg (by positivity)
          rw [hn]
          exact mul_le_mul_of_nonneg_left h1 (by positivity)
        refine (mul_le_mul_of_nonneg_right h2 (norm_nonneg _)).trans ?_
        have hR2 : ‖h2_perp x‖ < 2 * R := hp2
        have : ‖h2_perp x‖ ^ 2 < 4 * R ^ 2 := by nlinarith [norm_nonneg (h2_perp x)]
        have h3 : 1 / R ^ 2 * ‖h2_perp x‖ ^ 2 ≤ 4 := by
          rw [one_div, inv_mul_le_iff₀ (by positivity)]; nlinarith
        nlinarith [mul_nonneg hL0 (norm_nonneg (h2_perp x))]

end HRS.MC.CepH2
