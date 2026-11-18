import HRS.MP.SelfSimP4MolE5

/-!
# MPP4MOL stage 5c (10): the cut-off function `χ_R = ψ(2 - q/R²)`
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MP.SelfSimP4Mol

variable {d N : ℕ}

/-- The cut-off `χ_R(x) = ψ(2 - q(x)/R²)` with `ψ = smoothTransition`. -/
def p4m_chi (R : ℝ) (x : EucConfig d N) : ℝ := Real.smoothTransition (2 - p4m_q x / R ^ 2)

theorem p4m_psi_deriv_zero {s : ℝ} (hs : s ∉ Set.Icc (0 : ℝ) 1) : deriv Real.smoothTransition s = 0 := by
  by_cases h0 : s < 0
  · have : Real.smoothTransition =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds h0] with y hy
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
    rw [this.deriv_eq]; simp
  · have h1 : 1 < s := by
      by_contra hc
      exact hs ⟨not_lt.1 h0, not_lt.1 hc⟩
    have : Real.smoothTransition =ᶠ[𝓝 s] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds h1] with y hy
      exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
    rw [this.deriv_eq]; simp

theorem p4m_psi_deriv_bound : ∃ L : ℝ, 0 ≤ L ∧ ∀ s, |deriv Real.smoothTransition s| ≤ L := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨L, hL⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := deriv Real.smoothTransition)
    (s := Set.Icc (0 : ℝ) 1) hc.continuousOn
  refine ⟨max L 0, le_max_right _ _, fun s => ?_⟩
  by_cases hs : s ∈ Set.Icc (0 : ℝ) 1
  · exact (hL s hs).trans (le_max_left _ _)
  · rw [p4m_psi_deriv_zero hs]; simp

theorem p4m_contDiff_chi {R : ℝ} : ContDiff ℝ 1 (p4m_chi R : EucConfig d N → ℝ) :=
  (Real.smoothTransition.contDiff (n := 1)).comp (contDiff_const.sub ((p4m_contDiff_q).div_const _))

theorem p4m_chi_nonneg (R : ℝ) (x : EucConfig d N) : 0 ≤ p4m_chi R x := Real.smoothTransition.nonneg _

theorem p4m_chi_le_one (R : ℝ) (x : EucConfig d N) : p4m_chi R x ≤ 1 := Real.smoothTransition.le_one _

theorem p4m_chi_eq_one {R : ℝ} (hR : 0 < R) {x : EucConfig d N} (hx : p4m_q x ≤ R ^ 2) : p4m_chi R x = 1 := by
  unfold p4m_chi
  apply Real.smoothTransition.one_of_one_le
  have : p4m_q x / R ^ 2 ≤ 1 := (div_le_one (by positivity)).2 hx
  linarith

theorem p4m_chi_eq_zero {R : ℝ} (hR : 0 < R) {x : EucConfig d N} (hx : 2 * R ^ 2 ≤ p4m_q x) :
    p4m_chi R x = 0 := by
  unfold p4m_chi
  apply Real.smoothTransition.zero_of_nonpos
  have : 2 ≤ p4m_q x / R ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith
  linarith

theorem p4m_hasCompactSupport_chi {R : ℝ} (hR : 0 < R) : HasCompactSupport (p4m_chi R : EucConfig d N → ℝ) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : EucConfig d N) (2 * R)) fun x hx => ?_
  rw [mem_closedBall_zero_iff, not_le] at hx
  refine p4m_chi_eq_zero hR ?_
  have := p4m_norm_sq_le_q x
  nlinarith [norm_nonneg x]

theorem p4m_fderiv_chi_basis {R : ℝ} (hR : 0 < R) (x : EucConfig d N) (k : Fin N × Fin d) :
    fderiv ℝ (p4m_chi R) x (configBasis d N k) =
      deriv Real.smoothTransition (2 - p4m_q x / R ^ 2) * (-(2 * x k.1 k.2 / R ^ 2)) := by
  have hq := (p4m_hasFDerivAt_q x).const_smul ((R ^ 2)⁻¹)
  have h1 : HasFDerivAt (fun x : EucConfig d N => 2 - p4m_q x / R ^ 2)
      (-((R ^ 2)⁻¹ • ((2 : ℝ) • p4InnerL x))) x := by
    have := hq.const_sub 2
    convert this using 1
    funext y
    simp [div_eq_inv_mul]
  have h2 : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (2 - p4m_q x / R ^ 2))
      (2 - p4m_q x / R ^ 2) :=
    ((Real.smoothTransition.contDiff (n := 1)).differentiable (by norm_num) _).hasDerivAt
  have h3 := h2.comp_hasFDerivAt x h1
  have e : p4m_chi R = Real.smoothTransition ∘ fun x : EucConfig d N => 2 - p4m_q x / R ^ 2 := rfl
  rw [e, h3.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, smul_eq_mul]
  rw [p4m_inner_single]
  field_simp

theorem p4m_fderiv_chi_ne_zero {R : ℝ} (hR : 0 < R) {x : EucConfig d N} {k : Fin N × Fin d}
    (h : fderiv ℝ (p4m_chi R) x (configBasis d N k) ≠ 0) : R ^ 2 ≤ p4m_q x ∧ p4m_q x ≤ 2 * R ^ 2 := by
  rw [p4m_fderiv_chi_basis hR] at h
  have h1 : deriv Real.smoothTransition (2 - p4m_q x / R ^ 2) ≠ 0 := left_ne_zero_of_mul h
  have h2 : (2 - p4m_q x / R ^ 2) ∈ Set.Icc (0 : ℝ) 1 := by
    by_contra hc
    exact h1 (p4m_psi_deriv_zero hc)
  have hR2 : 0 < R ^ 2 := by positivity
  obtain ⟨a, b⟩ := h2
  constructor
  · have : p4m_q x / R ^ 2 ≥ 1 := by linarith
    rwa [ge_iff_le, le_div_iff₀ hR2, one_mul] at this
  · have : p4m_q x / R ^ 2 ≤ 2 := by linarith
    rw [div_le_iff₀ hR2] at this
    linarith

theorem p4m_fderiv_chi_bound : ∃ L : ℝ, 0 ≤ L ∧ ∀ R : ℝ, 0 < R → ∀ (x : EucConfig d N) (k : Fin N × Fin d),
    |fderiv ℝ (p4m_chi R) x (configBasis d N k)| ≤ L / R := by
  obtain ⟨Lψ, hL0, hL⟩ := p4m_psi_deriv_bound
  refine ⟨4 * Lψ, by positivity, fun R hR x k => ?_⟩
  by_cases h0 : fderiv ℝ (p4m_chi R) x (configBasis d N k) = 0
  · rw [h0]; simp only [abs_zero]; positivity
  · obtain ⟨-, hq⟩ := p4m_fderiv_chi_ne_zero hR h0
    rw [p4m_fderiv_chi_basis hR]
    have hx : |x k.1 k.2| ≤ 2 * R := by
      have := p4m_coord_sq_le x k
      exact abs_le.2 (abs_le_of_sq_le_sq' (by nlinarith) (by positivity))
    have hR2 : 0 < R ^ 2 := by positivity
    rw [abs_mul, abs_neg, abs_div, abs_mul, abs_of_pos hR2]
    calc |deriv Real.smoothTransition (2 - p4m_q x / R ^ 2)| * (|2| * |x k.1 k.2| / R ^ 2)
        ≤ Lψ * (2 * (2 * R) / R ^ 2) := by
          gcongr
          · exact hL _
          · simp
      _ = 4 * Lψ / R := by field_simp; ring

end HRS.MP.SelfSimP4Mol
