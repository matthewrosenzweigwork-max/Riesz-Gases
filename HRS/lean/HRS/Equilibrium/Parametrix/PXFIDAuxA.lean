import HRS.Equilibrium.PairCorrection

/-!
# Packet PX-FID, file A: smooth periodic cutoffs near a point of the torus

For `ã : ℝ^d` (the point `a = mk ã`) and `ε > 0` we build a smooth torus function `θ_ε` with
`0 ≤ θ_ε ≤ 1`, `θ_ε = 0` near `a`, `θ_ε = 1` where `|x - a| ≥ ε/2`, and `‖∇θ_ε‖ ≤ C / |x - a|`
(uniformly in `ε`), through the periodic function `q(x) = ∑ᵢ (1 - cos 2π(xᵢ - ãᵢ))` with
`8 |x-a|² ≤ q ≤ 2π² |x-a|²`.
-/

open MeasureTheory Filter Topology
open scoped ContDiff

noncomputable section

namespace HRS.Parx.PXFID

variable {d : ℕ}

/-! ### One-dimensional trigonometric bounds -/

theorem cos_eq_cos_frac (t : ℝ) : Real.cos (2 * Real.pi * t) =
    Real.cos (2 * Real.pi * (t - round t)) := by
  have : 2 * Real.pi * t = 2 * Real.pi * (t - round t) + (round t : ℤ) * (2 * Real.pi) := by ring
  rw [this, Real.cos_add_int_mul_two_pi]

theorem sin_eq_sin_frac (t : ℝ) : Real.sin (2 * Real.pi * t) =
    Real.sin (2 * Real.pi * (t - round t)) := by
  have : 2 * Real.pi * t = 2 * Real.pi * (t - round t) + (round t : ℤ) * (2 * Real.pi) := by ring
  rw [this, Real.sin_add_int_mul_two_pi]

theorem one_sub_cos_eq (δ : ℝ) : 1 - Real.cos (2 * Real.pi * δ) = 2 * Real.sin (Real.pi * δ) ^ 2 := by
  rw [show 2 * Real.pi * δ = 2 * (Real.pi * δ) by ring, Real.cos_two_mul, Real.cos_sq']
  ring

theorem two_abs_le_abs_sin {δ : ℝ} (h : |δ| ≤ 1 / 2) : 2 * |δ| ≤ |Real.sin (Real.pi * δ)| := by
  have hpi := Real.pi_pos
  have h1 := Real.mul_le_sin (x := Real.pi * |δ|) (by positivity)
    (by nlinarith [abs_nonneg δ])
  have e : 2 / Real.pi * (Real.pi * |δ|) = 2 * |δ| := by field_simp
  rw [e] at h1
  rcases le_total 0 δ with hδ | hδ
  · rw [abs_of_nonneg hδ] at h1 ⊢
    exact h1.trans (le_abs_self _)
  · rw [abs_of_nonpos hδ] at h1 ⊢
    have : Real.sin (Real.pi * -δ) = -Real.sin (Real.pi * δ) := by
      rw [mul_neg, Real.sin_neg]
    rw [this] at h1
    exact h1.trans (neg_le_abs _)

theorem trig_lower (t : ℝ) : 8 * |t - round t| ^ 2 ≤ 1 - Real.cos (2 * Real.pi * t) := by
  rw [cos_eq_cos_frac, one_sub_cos_eq]
  have hδ : |t - round t| ≤ 1 / 2 := abs_sub_round t
  have h := two_abs_le_abs_sin hδ
  have h2 : (2 * |t - round t|) ^ 2 ≤ Real.sin (Real.pi * (t - round t)) ^ 2 := by
    rw [← sq_abs (Real.sin _)]
    exact pow_le_pow_left₀ (by positivity) h 2
  nlinarith

theorem trig_upper (t : ℝ) : 1 - Real.cos (2 * Real.pi * t) ≤ 32 * |t - round t| ^ 2 := by
  rw [cos_eq_cos_frac, one_sub_cos_eq]
  have h := Real.abs_sin_le_abs (x := Real.pi * (t - round t))
  have h2 : Real.sin (Real.pi * (t - round t)) ^ 2 ≤ (Real.pi * (t - round t)) ^ 2 := by
    rw [← sq_abs (Real.sin _), ← sq_abs (Real.pi * (t - round t))]
    exact pow_le_pow_left₀ (abs_nonneg _) h 2
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hpi0 := Real.pi_pos
  have h3 : (Real.pi * (t - round t)) ^ 2 = Real.pi ^ 2 * |t - round t| ^ 2 := by
    rw [mul_pow, sq_abs]
  have h4 : Real.pi ^ 2 ≤ 16 := by nlinarith
  have h5 : 0 ≤ |t - round t| ^ 2 := by positivity
  nlinarith

theorem abs_sin_two_pi_le (t : ℝ) : |Real.sin (2 * Real.pi * t)| ≤ 8 * |t - round t| := by
  rw [sin_eq_sin_frac]
  have h := Real.abs_sin_le_abs (x := 2 * Real.pi * (t - round t))
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have : |2 * Real.pi * (t - round t)| = 2 * Real.pi * |t - round t| := by
    rw [abs_mul, abs_mul, abs_of_pos Real.pi_pos]; norm_num
  rw [this] at h
  nlinarith [abs_nonneg (t - round t)]

/-! ### The periodic function `q` and the distance -/

/-- The `i`-th unit lattice vector. -/
def ev (i : Fin d) : Lattice d := Pi.single i 1

theorem dot_ev (i : Fin d) (p : Euc d) : Lattice.dot (ev i) p = p i := by
  simp [Lattice.dot, ev, Pi.single_apply]

/-- `q(x) = ∑ᵢ (1 - cos 2π(xᵢ - ãᵢ))` as a function on the torus (through the modes). -/
def qfun (ã : Euc d) (x : Torus d) : ℝ :=
  ∑ i : Fin d, (1 - (Real.cos (2 * Real.pi * ã i) * Torus.cosMode (ev i) x +
    Real.sin (2 * Real.pi * ã i) * Torus.sinMode (ev i) x))

/-- The lift of `q`. -/
def qlift (ã p : Euc d) : ℝ := ∑ i : Fin d, (1 - Real.cos (2 * Real.pi * (p i - ã i)))

theorem lift_qfun (ã : Euc d) : Torus.lift (qfun ã) = qlift ã := by
  funext p
  simp only [Torus.lift, Function.comp, qfun, qlift, Torus.cosMode_mk, Torus.sinMode_mk, dot_ev]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_sub, Real.cos_sub]
  ring_nf

theorem contDiff_qlift (ã : Euc d) : ContDiff ℝ ∞ (qlift ã) := by
  unfold qlift
  refine ContDiff.sum fun i _ => ?_
  have h1 : ContDiff ℝ ∞ (fun p : Euc d => p i) :=
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff
  exact contDiff_const.sub (Real.contDiff_cos.comp (contDiff_const.mul (h1.sub contDiff_const)))

theorem eucDist_mk_sq (p ã : Euc d) : Torus.eucDist (Torus.mk p) (Torus.mk ã) ^ 2 =
    ∑ i : Fin d, |(p i - ã i) - round (p i - ã i)| ^ 2 := by
  unfold Torus.eucDist
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have : Torus.mk p i - Torus.mk ã i = (((p i - ã i : ℝ)) : UnitAddCircle) := by
    simp [Torus.mk, AddCircle.coe_sub]
  rw [this, UnitAddCircle.norm_eq]

theorem qlift_lower (p ã : Euc d) :
    8 * Torus.eucDist (Torus.mk p) (Torus.mk ã) ^ 2 ≤ qlift ã p := by
  rw [eucDist_mk_sq, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => by
    have := trig_lower (p i - ã i)
    rw [sq_abs] at this ⊢
    exact this

theorem qlift_upper (p ã : Euc d) :
    qlift ã p ≤ 32 * Torus.eucDist (Torus.mk p) (Torus.mk ã) ^ 2 := by
  rw [eucDist_mk_sq, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => by
    have := trig_upper (p i - ã i)
    rw [sq_abs] at this ⊢
    exact this

/-! ### The cutoff -/

/-- `G = 0` on `(-∞, 1]`, `G = 1` on `[2, ∞)`, smooth. -/
def Gcut (t : ℝ) : ℝ := Real.smoothTransition (t - 1)

theorem Gcut_zero {t : ℝ} (h : t ≤ 1) : Gcut t = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem Gcut_one {t : ℝ} (h : 2 ≤ t) : Gcut t = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem Gcut_nonneg (t : ℝ) : 0 ≤ Gcut t := Real.smoothTransition.nonneg _

theorem Gcut_le_one (t : ℝ) : Gcut t ≤ 1 := Real.smoothTransition.le_one _

theorem contDiff_Gcut : ContDiff ℝ ∞ Gcut :=
  Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)

theorem deriv_Gcut_eq_zero {t : ℝ} (h : t < 1 ∨ 2 < t) : deriv Gcut t = 0 := by
  rcases h with h | h
  · have : Gcut =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds h] with u hu using Gcut_zero (le_of_lt hu)
    rw [this.deriv_eq]; simp
  · have : Gcut =ᶠ[𝓝 t] fun _ => 1 := by
      filter_upwards [Ioi_mem_nhds h] with u hu using Gcut_one (le_of_lt hu)
    rw [this.deriv_eq]; simp

theorem exists_bound_deriv_Gcut : ∃ C : ℝ, 0 ≤ C ∧ ∀ t, |deriv Gcut t| ≤ C := by
  have hc : Continuous (deriv Gcut) := contDiff_Gcut.continuous_deriv (by simp)
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t => ?_⟩
  by_cases ht : t ∈ Set.Icc (1 : ℝ) 2
  · have h := hC t ht
    rw [Real.norm_eq_abs] at h
    exact h.trans (le_max_left _ _)
  · have : t < 1 ∨ 2 < t := by
      simp only [Set.mem_Icc, not_and_or, not_le] at ht
      exact ht
    rw [deriv_Gcut_eq_zero this]; simp

/-- The cutoff `θ_ε(x) = G(q(x)/ε²)`. -/
def theta (ε : ℝ) (ã : Euc d) (x : Torus d) : ℝ := Gcut (qfun ã x / ε ^ 2)

theorem lift_theta (ε : ℝ) (ã : Euc d) :
    Torus.lift (theta ε ã) = fun p => Gcut (qlift ã p / ε ^ 2) := by
  funext p
  simp only [Torus.lift, Function.comp, theta]
  rw [← lift_qfun]; rfl

theorem theta_isSmooth (ε : ℝ) (ã : Euc d) : Torus.IsSmooth (theta ε ã) := by
  unfold Torus.IsSmooth Torus.IsCk
  rw [lift_theta]
  exact contDiff_Gcut.comp ((contDiff_qlift ã).div_const _)

theorem theta_nonneg (ε : ℝ) (ã : Euc d) (x : Torus d) : 0 ≤ theta ε ã x := Gcut_nonneg _

theorem theta_le_one (ε : ℝ) (ã : Euc d) (x : Torus d) : theta ε ã x ≤ 1 := Gcut_le_one _

/-- `θ_ε = 1` where `|x - a| ≥ ε/2`. -/
theorem theta_eq_one {ε : ℝ} (hε : 0 < ε) (ã : Euc d) (p : Euc d)
    (h : ε / 2 ≤ Torus.eucDist (Torus.mk p) (Torus.mk ã)) : theta ε ã (Torus.mk p) = 1 := by
  have h1 := qlift_lower p ã
  apply Gcut_one
  rw [le_div_iff₀ (by positivity)]
  have : (ε / 2) ^ 2 ≤ Torus.eucDist (Torus.mk p) (Torus.mk ã) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h 2
  have hq : qfun ã (Torus.mk p) = qlift ã p := by rw [← lift_qfun]; rfl
  rw [hq]; nlinarith

/-- `θ_ε = 0` where `|x - a| < ε/6`. -/
theorem theta_eq_zero {ε : ℝ} (hε : 0 < ε) (ã : Euc d) (p : Euc d)
    (h : Torus.eucDist (Torus.mk p) (Torus.mk ã) < ε / 6) : theta ε ã (Torus.mk p) = 0 := by
  have h1 := qlift_upper p ã
  apply Gcut_zero
  rw [div_le_iff₀ (by positivity)]
  have h0 : 0 ≤ Torus.eucDist (Torus.mk p) (Torus.mk ã) := Real.sqrt_nonneg _
  have : Torus.eucDist (Torus.mk p) (Torus.mk ã) ^ 2 < (ε / 6) ^ 2 :=
    pow_lt_pow_left₀ h h0 (by norm_num)
  have hq : qfun ã (Torus.mk p) = qlift ã p := by rw [← lift_qfun]; rfl
  rw [hq]; nlinarith

theorem continuous_eucDist_mk (ã : Euc d) :
    Continuous fun p : Euc d => Torus.eucDist (Torus.mk p) (Torus.mk ã) := by
  unfold Torus.eucDist
  refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => ?_)
  refine (Continuous.pow ?_ 2)
  exact ((continuous_apply i).comp (Torus.continuous_mk (d := d)) |>.sub continuous_const).norm

/-! ### The gradient of the cutoff -/

theorem hasFDerivAt_qlift (ã p : Euc d) :
    HasFDerivAt (qlift ã)
      (∑ i : Fin d, (2 * Real.pi * Real.sin (2 * Real.pi * (p i - ã i))) •
        (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)) p := by
  unfold qlift
  have key : ∀ i ∈ (Finset.univ : Finset (Fin d)), HasFDerivAt
      (fun p : Euc d => 1 - Real.cos (2 * Real.pi * (p i - ã i)))
      ((2 * Real.pi * Real.sin (2 * Real.pi * (p i - ã i))) •
        (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)) p := by
    intro i _
    have hproj : HasFDerivAt (fun p : Euc d => p i) (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) p :=
      (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).hasFDerivAt
    have h1 := (hproj.sub_const (ã i)).const_mul (2 * Real.pi)
    have h2 := (Real.hasDerivAt_cos (2 * Real.pi * (p i - ã i))).comp_hasFDerivAt p h1
    have h3 := h2.const_sub 1
    refine h3.congr_fderiv ?_
    ext v
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply, smul_eq_mul]
    ring
  exact HasFDerivAt.fun_sum key

theorem abs_coord_le_eucDist (p ã : Euc d) (i : Fin d) :
    |(p i - ã i) - round (p i - ã i)| ≤ Torus.eucDist (Torus.mk p) (Torus.mk ã) := by
  have h0 : 0 ≤ Torus.eucDist (Torus.mk p) (Torus.mk ã) := Real.sqrt_nonneg _
  have h1 : |(p i - ã i) - round (p i - ã i)| ^ 2 ≤
      Torus.eucDist (Torus.mk p) (Torus.mk ã) ^ 2 := by
    rw [eucDist_mk_sq]
    exact Finset.single_le_sum (f := fun j => |(p j - ã j) - round (p j - ã j)| ^ 2)
      (fun j _ => by positivity) (Finset.mem_univ i)
  exact (pow_le_pow_iff_left₀ (abs_nonneg _) h0 (by norm_num)).1 h1

theorem norm_fderiv_qlift_le (ã p : Euc d) :
    ‖fderiv ℝ (qlift ã) p‖ ≤ 64 * d * Torus.eucDist (Torus.mk p) (Torus.mk ã) := by
  rw [(hasFDerivAt_qlift ã p).fderiv]
  set D := Torus.eucDist (Torus.mk p) (Torus.mk ã) with hD
  have hpi : Real.pi < 4 := Real.pi_lt_four
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  have hproj : ∀ i : Fin d, ‖(EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)‖ ≤ 1 := fun i =>
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by
      simpa using PiLp.norm_apply_le v i
  refine (norm_sum_le _ _).trans ?_
  calc ∑ i : Fin d, ‖(2 * Real.pi * Real.sin (2 * Real.pi * (p i - ã i))) •
        (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)‖
      ≤ ∑ _i : Fin d, 64 * D := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul, abs_two, abs_of_pos Real.pi_pos]
        have h1 := abs_sin_two_pi_le (p i - ã i)
        have h2 := abs_coord_le_eucDist p ã i
        have h3 := hproj i
        have h4 : 0 ≤ |Real.sin (2 * Real.pi * (p i - ã i))| := abs_nonneg _
        have h5 : 0 ≤ ‖(EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)‖ := norm_nonneg _
        have h6 : |Real.sin (2 * Real.pi * (p i - ã i))| ≤ 8 * D := h1.trans (by linarith)
        have h7 : 2 * Real.pi * |Real.sin (2 * Real.pi * (p i - ã i))| ≤ 64 * D := by
          nlinarith [Real.pi_pos]
        calc 2 * Real.pi * |Real.sin (2 * Real.pi * (p i - ã i))| *
              ‖(EuclideanSpace.proj i : Euc d →L[ℝ] ℝ)‖
            ≤ 64 * D * 1 := mul_le_mul h7 h3 h5 (by positivity)
          _ = 64 * D := by ring
    _ = 64 * d * D := by simp; ring

theorem fderiv_lift_theta (ε : ℝ) (ã p : Euc d) :
    fderiv ℝ (Torus.lift (theta ε ã)) p =
      (deriv Gcut (qlift ã p / ε ^ 2) * (ε ^ 2)⁻¹) • fderiv ℝ (qlift ã) p := by
  rw [lift_theta]
  have h1 : HasFDerivAt (fun p => qlift ã p / ε ^ 2) ((ε ^ 2)⁻¹ • fderiv ℝ (qlift ã) p) p := by
    have e : (fun p => qlift ã p / ε ^ 2) = fun p => (ε ^ 2)⁻¹ * qlift ã p := by
      funext p; ring
    rw [e]
    exact (((contDiff_qlift ã).differentiable (by simp) p).hasFDerivAt).const_mul _
  have h2 := (contDiff_Gcut.differentiable (by simp) (qlift ã p / ε ^ 2)).hasDerivAt.comp_hasFDerivAt
    p h1
  exact h2.fderiv.trans (by rw [smul_smul])

/-- The uniform gradient bound `‖∇θ_ε‖ ≤ Cθ / |x - a|`. -/
theorem exists_norm_fderiv_theta_le (d : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ), 0 < ε → ∀ (ã p : Euc d),
    ‖fderiv ℝ (Torus.lift (theta ε ã)) p‖ ≤ C / Torus.eucDist (Torus.mk p) (Torus.mk ã) := by
  obtain ⟨CG, hCG0, hCG⟩ := exists_bound_deriv_Gcut
  refine ⟨16 * d * CG, by positivity, fun ε hε ã p => ?_⟩
  set D := Torus.eucDist (Torus.mk p) (Torus.mk ã) with hD
  have hD0 : 0 ≤ D := Real.sqrt_nonneg _
  rw [fderiv_lift_theta, norm_smul, Real.norm_eq_abs, abs_mul]
  by_cases hc : deriv Gcut (qlift ã p / ε ^ 2) = 0
  · rw [hc]; simp only [abs_zero, zero_mul]
    exact div_nonneg (by positivity) hD0
  · have ht : ¬ (qlift ã p / ε ^ 2 < 1 ∨ 2 < qlift ã p / ε ^ 2) := fun h =>
      hc (deriv_Gcut_eq_zero h)
    simp only [not_or, not_lt] at ht
    obtain ⟨ht1, ht2⟩ := ht
    have hε2 : 0 < ε ^ 2 := by positivity
    have hq1 : ε ^ 2 ≤ qlift ã p := by rwa [le_div_iff₀ hε2, one_mul] at ht1
    have hq2 : qlift ã p ≤ 2 * ε ^ 2 := by rwa [div_le_iff₀ hε2] at ht2
    have hlow : 8 * D ^ 2 ≤ qlift ã p := qlift_lower p ã
    have hup : qlift ã p ≤ 32 * D ^ 2 := qlift_upper p ã
    have hDpos : 0 < D := by
      by_contra hneg
      have : D = 0 := le_antisymm (not_lt.mp hneg) hD0
      rw [this] at hup
      nlinarith
    have h4 : 4 * D ^ 2 ≤ ε ^ 2 := by nlinarith
    have h5 : (ε ^ 2)⁻¹ ≤ (4 * D ^ 2)⁻¹ := inv_anti₀ (by positivity) h4
    have h6 := norm_fderiv_qlift_le ã p
    rw [abs_of_nonneg (inv_nonneg.2 hε2.le)]
    calc |deriv Gcut (qlift ã p / ε ^ 2)| * (ε ^ 2)⁻¹ * ‖fderiv ℝ (qlift ã) p‖
        ≤ CG * (4 * D ^ 2)⁻¹ * (64 * d * D) := by
          refine mul_le_mul (mul_le_mul (hCG _) h5 (by positivity) hCG0) h6 (norm_nonneg _)
            (by positivity)
      _ = 16 * d * CG / D := by field_simp; ring

/-- `∇θ_ε = 0` where `|x - a| > ε/2`. -/
theorem fderiv_theta_eq_zero {ε : ℝ} (hε : 0 < ε) (ã p : Euc d)
    (h : ε / 2 < Torus.eucDist (Torus.mk p) (Torus.mk ã)) :
    fderiv ℝ (Torus.lift (theta ε ã)) p = 0 := by
  rw [fderiv_lift_theta]
  have hq := qlift_lower p ã
  have hε2 : 0 < ε ^ 2 := by positivity
  have h2 : (ε / 2) ^ 2 < Torus.eucDist (Torus.mk p) (Torus.mk ã) ^ 2 :=
    pow_lt_pow_left₀ h (by positivity) (by norm_num)
  have : 2 < qlift ã p / ε ^ 2 := by
    rw [lt_div_iff₀ hε2]; nlinarith
  rw [deriv_Gcut_eq_zero (Or.inr this)]; simp

end HRS.Parx.PXFID

end
