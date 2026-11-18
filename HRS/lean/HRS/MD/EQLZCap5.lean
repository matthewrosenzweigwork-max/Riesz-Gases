import HRS.MD.EQLZCap1

/-!
# EQ-LZ packet CAP, helper 5: the pair profile on the torus `𝕋^d`

`sT u = ∑_k (1 - cos(2π‖u_k‖))` (`‖·‖` the circle norm), `sE` its periodic lift
`sE y = ∑_k (1 - cos 2π y_k)`.  The log cut-off profile `Th m` (`Th m τ = ρ(log τ / m + 2)`, `ρ` the smooth
transition), `Th m = 0` for `τ ≤ e^{-2m}`, `= 1` for `τ ≥ e^{-m}`, `|Th m'(τ)| ≤ A/(mτ)`.
For `d ≥ 2`: `vol{sT ≤ τ} ≤ τ/2` and the capacity integral `∫ Psi m (sT) ≤ 2(m+1)`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology

namespace HRS.MD.EQLZ.Cap

variable {d : ℕ}

/-! ### The circle functions -/

def sT (u : Torus d) : ℝ := ∑ k, (1 - Real.cos (2 * Real.pi * ‖u k‖))

def sE (y : Euc d) : ℝ := ∑ k, (1 - Real.cos (2 * Real.pi * y k))

theorem norm_coe_circle (r : ℝ) : ‖((r : ℝ) : UnitAddCircle)‖ = |r - round r| := by
  have := AddCircle.norm_eq (1 : ℝ) (x := r)
  simpa using this

theorem cos_norm_coe (r : ℝ) :
    Real.cos (2 * Real.pi * ‖((r : ℝ) : UnitAddCircle)‖) = Real.cos (2 * Real.pi * r) := by
  rw [norm_coe_circle]
  have h1 : 2 * Real.pi * |r - round r| = |2 * Real.pi * (r - round r)| := by
    rw [abs_mul, abs_of_pos Real.two_pi_pos]
  rw [h1, Real.cos_abs]
  have := Real.cos_sub_int_mul_two_pi (2 * Real.pi * r) (round r)
  rw [← this]
  congr 1
  ring

theorem sT_mk (y : Euc d) : sT (Torus.mk y) = sE y := by
  unfold sT sE
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (Torus.mk y) k = ((y k : ℝ) : UnitAddCircle) from rfl, cos_norm_coe]

theorem sE_nonneg (y : Euc d) : 0 ≤ sE y :=
  Finset.sum_nonneg fun k _ => by linarith [Real.cos_le_one (2 * Real.pi * y k)]

theorem sT_nonneg (u : Torus d) : 0 ≤ sT u :=
  Finset.sum_nonneg fun k _ => by linarith [Real.cos_le_one (2 * Real.pi * ‖u k‖)]

theorem sT_zero : sT (0 : Torus d) = 0 := by
  unfold sT
  simp

theorem continuous_sT : Continuous (sT : Torus d → ℝ) := by
  unfold sT
  refine continuous_finsetSum _ fun k _ => ?_
  exact continuous_const.sub (Real.continuous_cos.comp (continuous_const.mul
    (continuous_norm.comp (continuous_apply k))))

theorem sE_eq_zero_imp (y : Euc d) (h : sE y = 0) : Torus.mk y = 0 := by
  unfold sE at h
  have hk := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by
    linarith [Real.cos_le_one (2 * Real.pi * y k)])).1 h
  funext k
  have h1 := hk k (Finset.mem_univ k)
  have h2 : Real.cos (2 * Real.pi * y k) = 1 := by linarith
  obtain ⟨m, hm⟩ := (Real.cos_eq_one_iff _).1 h2
  have h3 : y k = m := by
    have := Real.pi_pos
    nlinarith
  show ((y k : ℝ) : UnitAddCircle) = 0
  rw [h3, AddCircle.coe_eq_zero_iff]
  exact ⟨m, by simp⟩

theorem contDiff_sE : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (sE : Euc d → ℝ) := by
  unfold sE
  refine ContDiff.sum fun k _ => ?_
  refine contDiff_const.sub (Real.contDiff_cos.comp (contDiff_const.mul ?_))
  exact (EuclideanSpace.proj k : Euc d →L[ℝ] ℝ).contDiff

theorem hasFDerivAt_sE (y : Euc d) :
    HasFDerivAt (sE : Euc d → ℝ)
      (∑ k, (2 * Real.pi * Real.sin (2 * Real.pi * y k)) • (EuclideanSpace.proj k : Euc d →L[ℝ] ℝ)) y := by
  unfold sE
  refine HasFDerivAt.fun_sum fun k _ => ?_
  have h1 : HasFDerivAt (fun u : Euc d => 2 * Real.pi * u k)
      ((2 * Real.pi) • (EuclideanSpace.proj k : Euc d →L[ℝ] ℝ)) y :=
    (EuclideanSpace.proj k : Euc d →L[ℝ] ℝ).hasFDerivAt.const_mul (2 * Real.pi)
  have h2 := (Real.hasDerivAt_cos (2 * Real.pi * y k)).comp_hasFDerivAt y h1
  have h3 := (hasFDerivAt_const (1 : ℝ) y).sub h2
  convert h3 using 1
  · funext z; simp
  · rw [zero_sub, neg_smul, neg_neg, smul_smul]
    congr 1
    ring

theorem norm_fderiv_sE_sq (y : Euc d) : ‖fderiv ℝ sE y‖ ^ 2 ≤ 8 * Real.pi ^ 2 * d * sE y := by
  rw [(hasFDerivAt_sE y).fderiv]
  set c : Fin d → ℝ := fun k => 2 * Real.pi * Real.sin (2 * Real.pi * y k) with hc
  have h1 : ‖∑ k, c k • (EuclideanSpace.proj k : Euc d →L[ℝ] ℝ)‖ ≤ ∑ k, |c k| := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_smul, Real.norm_eq_abs]
    have : ‖(EuclideanSpace.proj k : Euc d →L[ℝ] ℝ)‖ ≤ 1 :=
      ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => by
        simpa using PiLp.norm_apply_le v k)
    calc |c k| * ‖(EuclideanSpace.proj k : Euc d →L[ℝ] ℝ)‖ ≤ |c k| * 1 := by gcongr
      _ = |c k| := mul_one _
  have h2 : (∑ k, |c k|) ^ 2 ≤ d * ∑ k, |c k| ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun k => |c k|)
    simpa using this
  have h3 : ∀ k, |c k| ^ 2 ≤ 8 * Real.pi ^ 2 * (1 - Real.cos (2 * Real.pi * y k)) := by
    intro k
    rw [sq_abs, hc]
    simp only
    have hs := Real.sin_sq_add_cos_sq (2 * Real.pi * y k)
    have hcos := Real.cos_le_one (2 * Real.pi * y k)
    have hcos' := Real.neg_one_le_cos (2 * Real.pi * y k)
    nlinarith [sq_nonneg Real.pi, mul_nonneg (sq_nonneg Real.pi) (sub_nonneg.2 hcos),
      mul_nonneg (mul_nonneg (sq_nonneg Real.pi) (sub_nonneg.2 hcos)) (by linarith : (0:ℝ) ≤ 1 + Real.cos (2 * Real.pi * y k))]
  have h4 : ∑ k, |c k| ^ 2 ≤ 8 * Real.pi ^ 2 * sE y := by
    unfold sE
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => h3 k
  calc ‖∑ k, c k • (EuclideanSpace.proj k : Euc d →L[ℝ] ℝ)‖ ^ 2 ≤ (∑ k, |c k|) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ d * ∑ k, |c k| ^ 2 := h2
    _ ≤ d * (8 * Real.pi ^ 2 * sE y) := by gcongr
    _ = 8 * Real.pi ^ 2 * d * sE y := by ring

/-! ### The logarithmic profile -/

theorem rho_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Real.smoothTransition :=
  Real.smoothTransition.contDiff (n := ⊤)

theorem deriv_rho_zero {x : ℝ} (hx : x ∉ Set.Icc (0 : ℝ) 1) : deriv Real.smoothTransition x = 0 := by
  rcases not_and_or.1 (show ¬(0 ≤ x ∧ x ≤ 1) from hx) with h | h
  · have h' : x < 0 := lt_of_not_ge h
    have : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds h'] with y hy
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
    rw [this.deriv_eq]; simp
  · have h' : 1 < x := lt_of_not_ge h
    have : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds h'] with y hy
      exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
    rw [this.deriv_eq]; simp

theorem exists_rho_deriv_bound : ∃ A : ℝ, 0 ≤ A ∧ ∀ x, |deriv Real.smoothTransition x| ≤ A := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (rho_smooth.of_le (by exact_mod_cast le_top : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))).continuous_deriv le_rfl
  have hs : HasCompactSupport (deriv Real.smoothTransition) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc (fun x hx => by
      by_contra h
      exact hx (deriv_rho_zero h))
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs
  exact ⟨max C 0, le_max_right _ _, fun x => by
    have := hC x
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)⟩

/-- The log cut-off profile at scale `m`. -/
def Th (m : ℕ) (τ : ℝ) : ℝ := if τ ≤ 0 then 0 else Real.smoothTransition (Real.log τ / m + 2)

section Th

variable {m : ℕ} (hm : 1 ≤ m)
include hm

theorem Th_eq_pos {τ : ℝ} (hτ : 0 < τ) : Th m τ = Real.smoothTransition (Real.log τ / m + 2) := by
  simp [Th, not_le.2 hτ]

theorem Th_zero {τ : ℝ} (hτ : τ ≤ Real.exp (-2 * m)) : Th m τ = 0 := by
  by_cases h0 : τ ≤ 0
  · simp [Th, h0]
  · have hpos : 0 < τ := not_le.1 h0
    rw [Th_eq_pos hm hpos]
    apply Real.smoothTransition.zero_of_nonpos
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
    have : Real.log τ ≤ -2 * m := (Real.log_le_iff_le_exp hpos).2 hτ
    have : Real.log τ / m ≤ -2 := by rw [div_le_iff₀ hmpos]; linarith
    linarith

theorem Th_one {τ : ℝ} (hτ : Real.exp (-(m : ℝ)) ≤ τ) : Th m τ = 1 := by
  have hpos : 0 < τ := lt_of_lt_of_le (Real.exp_pos _) hτ
  rw [Th_eq_pos hm hpos]
  apply Real.smoothTransition.one_of_one_le
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have : -(m : ℝ) ≤ Real.log τ := (Real.le_log_iff_exp_le hpos).2 hτ
  have : -1 ≤ Real.log τ / m := by rw [le_div_iff₀ hmpos]; linarith
  linarith

theorem Th_nonneg (τ : ℝ) : 0 ≤ Th m τ := by
  unfold Th; split_ifs
  · exact le_rfl
  · exact Real.smoothTransition.nonneg _

theorem Th_le_one (τ : ℝ) : Th m τ ≤ 1 := by
  unfold Th; split_ifs
  · exact zero_le_one
  · exact Real.smoothTransition.le_one _

theorem Th_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Th m) := by
  rw [contDiff_iff_contDiffAt]
  intro τ
  by_cases hτ : 0 < τ
  · have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun τ => Real.smoothTransition (Real.log τ / m + 2)) τ := by
      refine rho_smooth.contDiffAt.comp τ ?_
      exact ((Real.contDiffAt_log.2 hτ.ne').div_const _).add contDiffAt_const
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hτ] with y hy
    exact Th_eq_pos hm hy
  · have hτ' : τ < Real.exp (-2 * m) := lt_of_le_of_lt (not_lt.1 hτ) (Real.exp_pos _)
    have : Th m =ᶠ[𝓝 τ] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hτ'] with y hy
      exact Th_zero hm hy.le
    exact contDiffAt_const.congr_of_eventuallyEq this

theorem Th_hasDerivAt {τ : ℝ} (hτ : 0 < τ) :
    HasDerivAt (Th m) (deriv Real.smoothTransition (Real.log τ / m + 2) * (τ⁻¹ / m)) τ := by
  have h1 : HasDerivAt (fun τ => Real.log τ / m + 2) (τ⁻¹ / m) τ :=
    ((Real.hasDerivAt_log hτ.ne').div_const (m : ℝ)).add_const 2
  have h2 : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition (Real.log τ / m + 2))
      (Real.log τ / m + 2) :=
    ((rho_smooth.of_le (by exact_mod_cast le_top : (1 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))).differentiable
      one_ne_zero _).hasDerivAt
  have h3 := h2.comp τ h1
  refine h3.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hτ] with y hy
  exact Th_eq_pos hm hy

theorem Th_deriv_outside {τ : ℝ} (hτ : τ < Real.exp (-2 * m) ∨ Real.exp (-(m : ℝ)) < τ) :
    deriv (Th m) τ = 0 := by
  rcases hτ with h | h
  · have : Th m =ᶠ[𝓝 τ] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds h] with y hy
      exact Th_zero hm hy.le
    rw [this.deriv_eq]; simp
  · have : Th m =ᶠ[𝓝 τ] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds h] with y hy
      exact Th_one hm hy.le
    rw [this.deriv_eq]; simp

end Th

/-- The capacity weight `τ⁻¹ 1_{[e^{-2m}, e^{-m}]}(τ)`. -/
def Psi (m : ℕ) (τ : ℝ) : ℝ := if Real.exp (-2 * m) ≤ τ ∧ τ ≤ Real.exp (-(m : ℝ)) then τ⁻¹ else 0

theorem Th_deriv_sq {m : ℕ} (hm : 1 ≤ m) {A : ℝ} (hA : ∀ x, |deriv Real.smoothTransition x| ≤ A)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    (deriv (Th m) τ) ^ 2 * τ ≤ (A ^ 2 / (m : ℝ) ^ 2) * Psi m τ := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  by_cases hs : Real.exp (-2 * m) ≤ τ ∧ τ ≤ Real.exp (-(m : ℝ))
  · have hpos : 0 < τ := lt_of_lt_of_le (Real.exp_pos _) hs.1
    rw [(Th_hasDerivAt hm hpos).deriv]
    simp only [Psi, if_pos hs]
    have hd : |deriv Real.smoothTransition (Real.log τ / m + 2) * (τ⁻¹ / m)| ≤ A * (τ⁻¹ / m) := by
      rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ τ⁻¹ / m)]
      exact mul_le_mul_of_nonneg_right (hA _) (by positivity)
    have : (deriv Real.smoothTransition (Real.log τ / m + 2) * (τ⁻¹ / m)) ^ 2 ≤ (A * (τ⁻¹ / m)) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hd 2
    calc (deriv Real.smoothTransition (Real.log τ / m + 2) * (τ⁻¹ / m)) ^ 2 * τ
        ≤ (A * (τ⁻¹ / m)) ^ 2 * τ := by gcongr
      _ = A ^ 2 / (m : ℝ) ^ 2 * τ⁻¹ := by field_simp
  · have : τ < Real.exp (-2 * m) ∨ Real.exp (-(m : ℝ)) < τ := by
      by_contra h
      push Not at h
      exact hs ⟨h.1, h.2⟩
    rw [Th_deriv_outside hm this]
    simp only [Psi, if_neg hs]
    simp

end HRS.MD.EQLZ.Cap
