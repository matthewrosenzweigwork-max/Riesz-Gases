import HRS.MS.MovBridgeAux4

/-!
# MOVA3B2, part 2: the `H → Σ` Stein interpolation (`mo_interp_H_osc`)

Namespace `HRS.MS.MovOsc`, helpers `mova3b2_`.  Proves `mo_interp_H_osc_stmt d` (statement of
`MovInterpAux3`, unchanged).  Proof (three lines on the Hermite side): for a real Schwartz `f` put
`G = f_ℂ`, `φ_z = W(D)^{(θ-z)(r1-r0)/2} G` (Schwartz for every complex `z`, `MovBridgeAux4`),
`Λ_α φ = ⟨T Re φ, h_α⟩ + i ⟨T Im φ, h_α⟩` (complex-linear, bounded in `H^{r0}` by the endpoint
hypothesis) and
`F_S(z) = ∑_{α ∈ S} d_α λ_α^{(z-θ)(s1-s0)/2} Λ_α φ_z`, `d_α = λ_α^σ ⟨T f, h_α⟩`.
* `mova3b2_Lam_rot_hasDerivAt`: `c ↦ Λ(W(D)^c G)` is complex differentiable, from the `H^{r0}` remainder
  bound `|e^x - 1 - x| ≤ |x|² e^{|x|}`, `log W ≤ W`;
* `mova3b2_F_differentiable`, `mova3b2_F_bdd`: `F_S` is entire and bounded on `0 ≤ Re z ≤ 1`;
* `mova3b2_boundary`: `|F_S(j + it)| ≤ M_j ‖f‖_{H^ρ} (∑_{α∈S} λ_α^σ ⟨T f,h_α⟩²)^{1/2}` by Cauchy-Schwarz
  and `‖Re φ‖²_{H^r} + ‖Im φ‖²_{H^r} = ∫ W^r |𝓕 φ|²` (`mova3b2_sob`); `F_S(θ) = ∑_{α ∈ S} λ_α^σ ⟨T f,h_α⟩²`;
* `mova3b2_three_lines`, `mo_interp_H_osc`: Mathlib's three-lines theorem, then `S ↑ ∞`.
No density argument is needed: `T` is only evaluated on Schwartz functions.
-/

noncomputable section

open Filter MeasureTheory Topology
open scoped ContDiff FourierTransform ComplexConjugate

namespace HRS.MS.MovOsc

open HRS HRS.PDE.ToolboxRd HRS.MS.MovInterp

variable {d : ℕ}

local notation "𝓢C" => SchwartzMap (Euc d) ℂ
local notation "𝓢R" => SchwartzMap (Euc d) ℝ

/-- `𝓕` of a Fourier multiplier. -/
lemma mova3b2_fourier_fm {g : Euc d → ℂ} (hg : g.HasTemperateGrowth) (φ : 𝓢C) (ξ : Euc d) :
    (𝓕 (SchwartzMap.fourierMultiplierCLM ℂ g φ) : 𝓢C) ξ = g ξ * (𝓕 φ : 𝓢C) ξ := by
  rw [SchwartzMap.fourierMultiplierCLM_apply, FourierTransform.fourier_fourierInv_eq,
    SchwartzMap.smulLeftCLM_apply_apply hg]
  rfl

/-- The multiplier `W^c log W`, the `c`-derivative of `W^c`. -/
def mova3b2_gd (c : ℂ) : Euc d → ℂ := fun ξ =>
  mova3b2_gm c ξ * ((Real.log (mova3b1_W ξ) : ℝ) : ℂ)

lemma mova3b2_gd_tg (c : ℂ) : (mova3b2_gd (d := d) c).HasTemperateGrowth :=
  (mova3b2_g_tg c).mul (Complex.hasTemperateGrowth_ofReal.comp mova3b2_L_tg)

lemma mova3b2_gm_add (c h : ℂ) (ξ : Euc d) :
    mova3b2_gm (c + h) ξ =
      mova3b2_gm c ξ * Complex.exp (h * ((Real.log (mova3b1_W ξ) : ℝ) : ℂ)) := by
  unfold mova3b2_gm
  have hne : ((mova3b1_W ξ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (mova3b1_W_pos ξ).ne'
  rw [Complex.cpow_add _ _ hne, Complex.cpow_def_of_ne_zero hne c,
    Complex.cpow_def_of_ne_zero hne h,
    ← Complex.ofReal_log (mova3b1_W_pos ξ).le, mul_comm (((Real.log (mova3b1_W ξ) : ℝ)) : ℂ) h]

lemma mova3b2_L_nonneg (ξ : Euc d) : 0 ≤ Real.log (mova3b1_W ξ) :=
  Real.log_nonneg (mova3b1_W_ge ξ)

lemma mova3b2_L_le (ξ : Euc d) : Real.log (mova3b1_W ξ) ≤ mova3b1_W ξ := by
  have := Real.log_le_sub_one_of_pos (mova3b1_W_pos ξ); linarith

lemma mova3b2_exp_rem (h : ℂ) (hh : ‖h‖ ≤ 1) (ξ : Euc d) :
    ‖Complex.exp (h * ((Real.log (mova3b1_W ξ) : ℝ) : ℂ)) - 1 -
      h * ((Real.log (mova3b1_W ξ) : ℝ) : ℂ)‖ ≤ ‖h‖ ^ 2 * mova3b1_W ξ ^ 3 := by
  set L := Real.log (mova3b1_W ξ) with hL
  have hL0 : 0 ≤ L := mova3b2_L_nonneg ξ
  have hLW : L ≤ mova3b1_W ξ := mova3b2_L_le ξ
  have hW := mova3b1_W_pos ξ
  set x : ℂ := h * (L : ℂ) with hx
  have hxn : ‖x‖ = ‖h‖ * L := by
    rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hL0]
  have h1 := Complex.norm_exp_sub_sum_le_norm_mul_exp x 2
  have e : ∑ m ∈ Finset.range 2, x ^ m / (m.factorial : ℂ) = 1 + x := by
    simp [Finset.sum_range_succ]
  rw [e] at h1
  have e2 : Complex.exp x - 1 - x = Complex.exp x - (1 + x) := by ring
  rw [e2]
  refine h1.trans ?_
  rw [hxn]
  have hexp : Real.exp (‖h‖ * L) ≤ mova3b1_W ξ := by
    calc Real.exp (‖h‖ * L) ≤ Real.exp L :=
          Real.exp_le_exp.2 (mul_le_of_le_one_left hL0 hh)
      _ = mova3b1_W ξ := by rw [hL, Real.exp_log hW]
  have hsq : (‖h‖ * L) ^ 2 ≤ ‖h‖ ^ 2 * mova3b1_W ξ ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL0 hLW 2) (sq_nonneg _)
  calc (‖h‖ * L) ^ 2 * Real.exp (‖h‖ * L) ≤ (‖h‖ ^ 2 * mova3b1_W ξ ^ 2) * mova3b1_W ξ :=
        mul_le_mul hsq hexp (Real.exp_pos _).le (by positivity)
    _ = ‖h‖ ^ 2 * mova3b1_W ξ ^ 3 := by ring

lemma mova3b2_rem_bound (c h : ℂ) (hh : ‖h‖ ≤ 1) (ξ : Euc d) :
    ‖mova3b2_gm (c + h) ξ - mova3b2_gm c ξ - h * mova3b2_gd c ξ‖ ≤
      ‖h‖ ^ 2 * mova3b1_W ξ ^ (c.re + 3) := by
  have e : mova3b2_gm (c + h) ξ - mova3b2_gm c ξ - h * mova3b2_gd c ξ =
      mova3b2_gm c ξ * (Complex.exp (h * ((Real.log (mova3b1_W ξ) : ℝ) : ℂ)) - 1 -
        h * ((Real.log (mova3b1_W ξ) : ℝ) : ℂ)) := by
    rw [mova3b2_gm_add]; unfold mova3b2_gd; ring
  rw [e, norm_mul, mova3b2_norm_gm]
  have hW := mova3b1_W_pos ξ
  have h1 := mova3b2_exp_rem h hh ξ
  have e3 : mova3b1_W ξ ^ (c.re + 3) = mova3b1_W ξ ^ c.re * mova3b1_W ξ ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hW]; norm_num
  rw [e3]
  calc mova3b1_W ξ ^ c.re * ‖Complex.exp (h * ((Real.log (mova3b1_W ξ) : ℝ) : ℂ)) - 1 -
        h * ((Real.log (mova3b1_W ξ) : ℝ) : ℂ)‖
      ≤ mova3b1_W ξ ^ c.re * (‖h‖ ^ 2 * mova3b1_W ξ ^ 3) :=
        mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hW.le _)
    _ = _ := by ring

lemma mova3b2_rpow_sq (a : ℝ) (ξ : Euc d) : (mova3b1_W ξ ^ a) ^ 2 = mova3b1_W ξ ^ (2 * a) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (mova3b1_W_pos ξ).le]; norm_num; ring_nf


/-- Quantitative remainder bound for the `H^{r0}` seminorm. -/
lemma mova3b2_rem_norm (G : 𝓢C) (c0 h : ℂ) (hh : ‖h‖ ≤ 1) (r0 : ℝ) :
    let ψ : 𝓢C := mova3b2_rot (c0 + h) G + (-1 : ℂ) • mova3b2_rot c0 G +
      (-h) • SchwartzMap.fourierMultiplierCLM ℂ (mova3b2_gd c0) G
    ∫ ξ, mova3b1_W ξ ^ r0 * ‖(𝓕 ψ : 𝓢C) ξ‖ ^ 2 ≤
      ‖h‖ ^ 4 * ∫ ξ, mova3b1_W ξ ^ (r0 + 2 * (c0.re + 3)) * ‖(𝓕 G : 𝓢C) ξ‖ ^ 2 := by
  intro ψ
  have hF : ∀ ξ, (𝓕 ψ : 𝓢C) ξ = (mova3b2_gm (c0 + h) ξ - mova3b2_gm c0 ξ - h * mova3b2_gd c0 ξ) *
      (𝓕 G : 𝓢C) ξ := by
    intro ξ
    simp only [ψ, FourierTransform.fourier_add, FourierTransform.fourier_smul, SchwartzMap.add_apply,
      SchwartzMap.smul_apply, smul_eq_mul, mova3b2_fourier_rot,
      mova3b2_fourier_fm (mova3b2_gd_tg c0)]
    ring
  have hI := mova3b2_int_W (𝓕 G : 𝓢C) (r0 + 2 * (c0.re + 3))
  rw [← integral_const_mul]
  refine integral_mono (mova3b2_int_W _ r0) (hI.const_mul _) fun ξ => ?_
  have hW := mova3b1_W_pos ξ
  simp only [hF, norm_mul, mul_pow]
  have h1 := mova3b2_rem_bound c0 h hh ξ
  have h2 : ‖mova3b2_gm (c0 + h) ξ - mova3b2_gm c0 ξ - h * mova3b2_gd c0 ξ‖ ^ 2 ≤
      ‖h‖ ^ 4 * mova3b1_W ξ ^ (2 * (c0.re + 3)) := by
    calc _ ≤ (‖h‖ ^ 2 * mova3b1_W ξ ^ (c0.re + 3)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = ‖h‖ ^ 4 * mova3b1_W ξ ^ (2 * (c0.re + 3)) := by
          rw [mul_pow, mova3b2_rpow_sq]; ring
  have h3 : mova3b1_W ξ ^ (r0 + 2 * (c0.re + 3)) =
      mova3b1_W ξ ^ r0 * mova3b1_W ξ ^ (2 * (c0.re + 3)) := Real.rpow_add hW _ _
  rw [h3]
  have h4 := mul_le_mul_of_nonneg_right h2 (sq_nonneg ‖(𝓕 G : 𝓢C) ξ‖)
  have h5 := mul_le_mul_of_nonneg_left h4 (Real.rpow_nonneg hW.le r0)
  calc mova3b1_W ξ ^ r0 * (‖mova3b2_gm (c0 + h) ξ - mova3b2_gm c0 ξ - h * mova3b2_gd c0 ξ‖ ^ 2 *
        ‖(𝓕 G : 𝓢C) ξ‖ ^ 2) ≤ _ := h5
    _ = _ := by ring

/-- `c ↦ Λ (W(D)^c G)` is complex differentiable with the expected derivative. -/
theorem mova3b2_Lam_rot_hasDerivAt (Lin : 𝓢R →ₗ[ℝ] ℝ) {K r0 : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ u : 𝓢R, |Lin u| ≤ K * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq r0 (⇑u)))
    (G : 𝓢C) (c0 : ℂ) :
    HasDerivAt (fun c : ℂ => mova3b2_Lam Lin (mova3b2_rot c G))
      (mova3b2_Lam Lin (SchwartzMap.fourierMultiplierCLM ℂ (mova3b2_gd c0) G)) c0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  set φ' : 𝓢C := SchwartzMap.fourierMultiplierCLM ℂ (mova3b2_gd c0) G with hφ'
  set N0 : ℝ := ∫ ξ, mova3b1_W ξ ^ (r0 + 2 * (c0.re + 3)) * ‖(𝓕 G : 𝓢C) ξ‖ ^ 2 with hN0
  have hN0nn : 0 ≤ N0 := integral_nonneg fun ξ => mul_nonneg
    (Real.rpow_nonneg (mova3b1_W_pos ξ).le _) (sq_nonneg _)
  have key : ∀ h : ℂ, ‖h‖ ≤ 1 →
      ‖mova3b2_Lam Lin (mova3b2_rot (c0 + h) G) - mova3b2_Lam Lin (mova3b2_rot c0 G) -
        h • mova3b2_Lam Lin φ'‖ ≤ (K * Real.sqrt N0) * ‖h‖ ^ 2 := by
    intro h hh
    set ψ : 𝓢C := mova3b2_rot (c0 + h) G + (-1 : ℂ) • mova3b2_rot c0 G + (-h) • φ' with hψ
    have e : mova3b2_Lam Lin (mova3b2_rot (c0 + h) G) - mova3b2_Lam Lin (mova3b2_rot c0 G) -
        h • mova3b2_Lam Lin φ' = mova3b2_Lam Lin ψ := by
      simp only [hψ, map_add, map_smul, smul_eq_mul]; ring
    rw [e]
    refine (mova3b2_Lam_bound Lin hK0 hK ψ).trans ?_
    have hle := mova3b2_rem_norm G c0 h hh r0
    have hle' : ∫ ξ, mova3b1_W ξ ^ r0 * ‖(𝓕 ψ : 𝓢C) ξ‖ ^ 2 ≤ ‖h‖ ^ 4 * N0 := hle
    have : Real.sqrt (∫ ξ, mova3b1_W ξ ^ r0 * ‖(𝓕 ψ : 𝓢C) ξ‖ ^ 2) ≤ ‖h‖ ^ 2 * Real.sqrt N0 := by
      calc _ ≤ Real.sqrt (‖h‖ ^ 4 * N0) := Real.sqrt_le_sqrt hle'
        _ = ‖h‖ ^ 2 * Real.sqrt N0 := by
          rw [Real.sqrt_mul (by positivity), show ‖h‖ ^ 4 = (‖h‖ ^ 2) ^ 2 by ring,
            Real.sqrt_sq (by positivity)]
    calc K * Real.sqrt (∫ ξ, mova3b1_W ξ ^ r0 * ‖(𝓕 ψ : 𝓢C) ξ‖ ^ 2)
        ≤ K * (‖h‖ ^ 2 * Real.sqrt N0) := mul_le_mul_of_nonneg_left this hK0
      _ = _ := by ring
  have hO : (fun h : ℂ => mova3b2_Lam Lin (mova3b2_rot (c0 + h) G) -
      mova3b2_Lam Lin (mova3b2_rot c0 G) - h • mova3b2_Lam Lin φ') =O[𝓝 0] fun h : ℂ => h ^ 2 := by
    refine Asymptotics.IsBigO.of_bound (K * Real.sqrt N0) ?_
    filter_upwards [Metric.closedBall_mem_nhds (0 : ℂ) one_pos] with h hh
    have hh' : ‖h‖ ≤ 1 := by simpa using hh
    rw [norm_pow]
    exact (key h hh').trans (by rw [mul_comm])
  exact hO.trans_isLittleO (Asymptotics.isLittleO_pow_id (by norm_num))

theorem mova3b2_Lam_rot_differentiable (Lin : 𝓢R →ₗ[ℝ] ℝ) {K r0 : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ u : 𝓢R, |Lin u| ≤ K * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq r0 (⇑u)))
    (G : 𝓢C) : Differentiable ℂ (fun c : ℂ => mova3b2_Lam Lin (mova3b2_rot c G)) :=
  fun c0 => (mova3b2_Lam_rot_hasDerivAt Lin hK0 hK G c0).differentiableAt


/-! ## The real functional `u ↦ ⟨T u, h_α⟩` and its endpoint bound -/

section Lin

open HRS.Whole

variable {T : SchwartzMap (Euc d) ℝ → (Euc d → ℝ)}

lemma mova3b2_T_zero (hlin : ∀ f g : 𝓢R, ∀ a : ℝ, T (a • f + g) = a • T f + T g) : T 0 = 0 := by
  have h := hlin 0 0 1
  simp only [smul_zero, add_zero, one_smul] at h
  exact left_eq_add.1 h

lemma mova3b2_T_add (hlin : ∀ f g : 𝓢R, ∀ a : ℝ, T (a • f + g) = a • T f + T g) (u v : 𝓢R) :
    T (u + v) = T u + T v := by
  have h := hlin u v 1
  simpa using h

lemma mova3b2_T_smul (hlin : ∀ f g : 𝓢R, ∀ a : ℝ, T (a • f + g) = a • T f + T g) (a : ℝ)
    (u : 𝓢R) : T (a • u) = a • T u := by
  have h := hlin u 0 a
  simpa [mova3b2_T_zero hlin] using h

/-- The real-linear functional `u ↦ ⟨T u, h_α⟩`. -/
def mova3b2_Lin (hlin : ∀ f g : 𝓢R, ∀ a : ℝ, T (a • f + g) = a • T f + T g)
    (hL2 : ∀ f, MemLp (T f) 2 (volume : Measure (Euc d))) (α : MultiIndex d) : 𝓢R →ₗ[ℝ] ℝ where
  toFun u := hermiteCoeff (T u) α
  map_add' u v := by
    unfold hermiteCoeff
    rw [mova3b2_T_add hlin]
    simp only [Pi.add_apply, add_mul]
    exact integral_add ((hL2 u).integrable_mul (memLp_hermiteFunD α))
      ((hL2 v).integrable_mul (memLp_hermiteFunD α))
  map_smul' a u := by
    unfold hermiteCoeff
    rw [mova3b2_T_smul hlin]
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, RingHom.id_apply]
    rw [integral_const_mul]

lemma mova3b2_Lin_apply (hlin : ∀ f g : 𝓢R, ∀ a : ℝ, T (a • f + g) = a • T f + T g)
    (hL2 : ∀ f, MemLp (T f) 2 (volume : Measure (Euc d))) (α : MultiIndex d) (u : 𝓢R) :
    mova3b2_Lin hlin hL2 α u = hermiteCoeff (T u) α := rfl

/-- A single Hermite coefficient is controlled by the `Σ^s` norm. -/
lemma mova3b2_coeff_le {s : ℝ} {g : Euc d → ℝ} (hg : MemOsc s g) (α : MultiIndex d) :
    |hermiteCoeff g α| ≤ oscEigenvalue d α ^ (-(s / 2)) * oscNorm s g := by
  have hpos : 0 < oscEigenvalue d α := oscEv_pos α
  have h1 : oscEigenvalue d α ^ s * hermiteCoeff g α ^ 2 ≤ oscNorm s g ^ 2 := by
    rw [oscNorm, Real.sq_sqrt (tsum_nonneg fun β => mul_nonneg
      (Real.rpow_nonneg (oscEv_pos β).le _) (sq_nonneg _))]
    exact hg.2.le_tsum α (fun β _ => mul_nonneg (Real.rpow_nonneg (oscEv_pos β).le _)
      (sq_nonneg _))
  have h2 : (oscEigenvalue d α ^ (s / 2) * |hermiteCoeff g α|) ^ 2 ≤ oscNorm s g ^ 2 := by
    rw [mul_pow, mova3_rpow_half_sq hpos, sq_abs]; exact h1
  have hO : 0 ≤ oscNorm s g := Real.sqrt_nonneg _
  have h3 : oscEigenvalue d α ^ (s / 2) * |hermiteCoeff g α| ≤ oscNorm s g :=
    (sq_le_sq₀ (mul_nonneg (Real.rpow_nonneg hpos.le _) (abs_nonneg _)) hO).1 h2
  have h4 : oscEigenvalue d α ^ (-(s / 2)) * oscEigenvalue d α ^ (s / 2) = 1 := by
    rw [← Real.rpow_add hpos]; simp
  calc |hermiteCoeff g α| = oscEigenvalue d α ^ (-(s / 2)) *
        (oscEigenvalue d α ^ (s / 2) * |hermiteCoeff g α|) := by
        rw [← mul_assoc, h4, one_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hpos.le _)


lemma mova3b2_sum_le_osc {s : ℝ} {g : Euc d → ℝ} (hg : MemOsc s g) (S : Finset (MultiIndex d)) :
    ∑ α ∈ S, oscEigenvalue d α ^ s * hermiteCoeff g α ^ 2 ≤ oscNorm s g ^ 2 := by
  have hnn : ∀ β : MultiIndex d, 0 ≤ oscEigenvalue d β ^ s * hermiteCoeff g β ^ 2 := fun β =>
    mul_nonneg (Real.rpow_nonneg (oscEv_pos β).le _) (sq_nonneg _)
  rw [oscNorm, Real.sq_sqrt (tsum_nonneg hnn)]
  exact hg.2.sum_le_tsum S (fun β _ => hnn β)

lemma mova3b2_Lin_bound (hlin : ∀ f g : 𝓢R, ∀ a : ℝ, T (a • f + g) = a • T f + T g)
    (hL2 : ∀ f, MemLp (T f) 2 (volume : Measure (Euc d))) {s r M : ℝ}
    (h : ∀ u : 𝓢R, MemOsc s (T u) ∧
      oscNorm s (T u) ≤ M * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq r (⇑u)))
    (α : MultiIndex d) (u : 𝓢R) :
    |mova3b2_Lin hlin hL2 α u| ≤
      (oscEigenvalue d α ^ (-(s / 2)) * M) *
        Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq r (⇑u)) := by
  rw [mova3b2_Lin_apply]
  refine (mova3b2_coeff_le (h u).1 α).trans ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (h u).2 (Real.rpow_nonneg (oscEv_pos α).le _)

end Lin

/-! ## Rotation of the Sobolev integrals -/

lemma mova3b2_N_rot (G : 𝓢C) (c : ℂ) (r : ℝ) :
    ∫ ξ, mova3b1_W ξ ^ r * ‖(𝓕 (mova3b2_rot c G) : 𝓢C) ξ‖ ^ 2 =
      ∫ ξ, mova3b1_W ξ ^ (r + 2 * c.re) * ‖(𝓕 G : 𝓢C) ξ‖ ^ 2 := by
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  show mova3b1_W ξ ^ r * ‖(𝓕 (mova3b2_rot c G) : 𝓢C) ξ‖ ^ 2 =
    mova3b1_W ξ ^ (r + 2 * c.re) * ‖(𝓕 G : 𝓢C) ξ‖ ^ 2
  rw [mova3b2_fourier_rot, norm_mul, mova3b2_norm_gm, mul_pow, mova3b2_rpow_sq,
    Real.rpow_add (mova3b1_W_pos ξ)]
  ring

lemma mova3b2_sobNormSq_cx (f : 𝓢R) (r : ℝ) :
    HRS.PDE.ToolboxRd.sobolevNormSq r (⇑f) =
      ∫ ξ, mova3b1_W ξ ^ r * ‖(𝓕 (mova3b2_cx f) : 𝓢C) ξ‖ ^ 2 := by
  rw [mova3b1_sobolevNormSq_eq]
  refine integral_congr_ae ?_
  filter_upwards [mova3b2_fourierL2_eq f] with ξ h
  rw [h]

lemma mova3b2_re_cx (f : 𝓢R) : mova3b2_re (mova3b2_cx f) = f := by ext x; simp

lemma mova3b2_im_cx (f : 𝓢R) : mova3b2_im (mova3b2_cx f) = 0 := by ext x; simp

/-! ## The analytic family -/

section Main

open HRS.Whole

variable {T : SchwartzMap (Euc d) ℝ → (Euc d → ℝ)}

/-- The rotation parameter `(θ - z)(r1 - r0)/2`. -/
def mova3b2_cz (θ r0 r1 : ℝ) (z : ℂ) : ℂ := ((θ : ℂ) - z) * ((r1 : ℂ) - r0) / 2

/-- `F_S(z) = ∑_{α∈S} v_α(z) Λ_α(W(D)^{c(z)} f)`. -/
def mova3b2_F (hlin : ∀ f g : 𝓢R, ∀ a : ℝ, T (a • f + g) = a • T f + T g)
    (hL2 : ∀ f, MemLp (T f) 2 (volume : Measure (Euc d))) (f : 𝓢R) (θ r0 r1 s0 s1 : ℝ)
    (S : Finset (MultiIndex d)) (z : ℂ) : ℂ :=
  ∑ α ∈ S, mova3_vb (oscEigenvalue d)
      (fun β => oscEigenvalue d β ^ ((1 - θ) * s0 + θ * s1) * hermiteCoeff (T f) β) θ s0 s1 z α *
    mova3b2_Lam (mova3b2_Lin hlin hL2 α) (mova3b2_rot (mova3b2_cz θ r0 r1 z) (mova3b2_cx f))

lemma mova3b2_F_theta (hlin : ∀ f g : 𝓢R, ∀ a : ℝ, T (a • f + g) = a • T f + T g)
    (hL2 : ∀ f, MemLp (T f) 2 (volume : Measure (Euc d))) (f : 𝓢R) (θ r0 r1 s0 s1 : ℝ)
    (S : Finset (MultiIndex d)) :
    mova3b2_F hlin hL2 f θ r0 r1 s0 s1 S (θ : ℂ) =
      ((∑ α ∈ S, oscEigenvalue d α ^ ((1 - θ) * s0 + θ * s1) * hermiteCoeff (T f) α ^ 2 : ℝ) : ℂ) := by
  unfold mova3b2_F
  push_cast
  refine Finset.sum_congr rfl fun α _ => ?_
  have h0 : mova3b2_cz θ r0 r1 (θ : ℂ) = 0 := by simp [mova3b2_cz]
  rw [h0, mova3b2_rot_zero, mova3b2_Lam_apply, mova3b2_re_cx, mova3b2_im_cx, map_zero]
  simp only [mova3_vb, sub_self, zero_mul, zero_div, Complex.exp_zero, mul_one, Complex.ofReal_zero,
    mul_zero, add_zero, mova3b2_Lin_apply]
  push_cast; ring

lemma mova3b2_F_differentiable (hlin : ∀ f g : 𝓢R, ∀ a : ℝ, T (a • f + g) = a • T f + T g)
    (hL2 : ∀ f, MemLp (T f) 2 (volume : Measure (Euc d))) (f : 𝓢R) (θ r0 r1 s0 s1 : ℝ)
    (S : Finset (MultiIndex d)) {M0 : ℝ} (hM0 : 0 ≤ M0)
    (h0 : ∀ u : 𝓢R, MemOsc s0 (T u) ∧
      oscNorm s0 (T u) ≤ M0 * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq r0 (⇑u))) :
    Differentiable ℂ (mova3b2_F hlin hL2 f θ r0 r1 s0 s1 S) := by
  unfold mova3b2_F
  refine Differentiable.fun_sum fun α _ => ?_
  refine Differentiable.mul ?_ ?_
  · unfold mova3_vb; fun_prop
  · have hd := mova3b2_Lam_rot_differentiable (mova3b2_Lin hlin hL2 α)
      (K := oscEigenvalue d α ^ (-(s0 / 2)) * M0)
      (mul_nonneg (Real.rpow_nonneg (oscEv_pos α).le _) hM0)
      (mova3b2_Lin_bound hlin hL2 h0 α) (mova3b2_cx f)
    have hc : Differentiable ℂ (mova3b2_cz θ r0 r1) := by unfold mova3b2_cz; fun_prop
    exact hd.comp hc

lemma mova3b2_cz_re (θ r0 r1 : ℝ) (z : ℂ) :
    (mova3b2_cz θ r0 r1 z).re = (θ - z.re) * (r1 - r0) / 2 := by
  simp [mova3b2_cz, Complex.mul_re, Complex.sub_re, Complex.sub_im]

lemma mova3b2_F_bdd (hlin : ∀ f g : 𝓢R, ∀ a : ℝ, T (a • f + g) = a • T f + T g)
    (hL2 : ∀ f, MemLp (T f) 2 (volume : Measure (Euc d))) (f : 𝓢R) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (r0 r1 s0 s1 : ℝ) (S : Finset (MultiIndex d)) {M0 : ℝ} (hM0 : 0 ≤ M0)
    (h0 : ∀ u : 𝓢R, MemOsc s0 (T u) ∧
      oscNorm s0 (T u) ≤ M0 * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq r0 (⇑u))) :
    ∃ C : ℝ, ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 →
      ‖mova3b2_F hlin hL2 f θ r0 r1 s0 s1 S z‖ ≤ C := by
  set G : 𝓢C := mova3b2_cx f with hG
  set E : ℝ := |r0| + |r1 - r0| with hE
  set Nb : ℝ := ∫ ξ, mova3b1_W ξ ^ E * ‖(𝓕 G : 𝓢C) ξ‖ ^ 2 with hNb
  set dco : MultiIndex d → ℝ := fun β =>
    oscEigenvalue d β ^ ((1 - θ) * s0 + θ * s1) * hermiteCoeff (T f) β with hdco
  refine ⟨∑ α ∈ S, (|dco α| * Real.exp (|s1 - s0| * |Real.log (oscEigenvalue d α)| / 2)) *
      ((oscEigenvalue d α ^ (-(s0 / 2)) * M0) * Real.sqrt Nb), fun z hz0 hz1 => ?_⟩
  unfold mova3b2_F
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => ?_)
  rw [norm_mul]
  have hb : ‖mova3_vb (oscEigenvalue d) dco θ s0 s1 z α‖ ≤
      |dco α| * Real.exp (|s1 - s0| * |Real.log (oscEigenvalue d α)| / 2) := by
    rw [mova3_norm_vb]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 (mova3_exp_arg_le hθ0 hθ1 hz0 hz1).2) (abs_nonneg _)
  have hK0 : 0 ≤ oscEigenvalue d α ^ (-(s0 / 2)) * M0 :=
    mul_nonneg (Real.rpow_nonneg (oscEv_pos α).le _) hM0
  have hl := mova3b2_Lam_bound (mova3b2_Lin hlin hL2 α) hK0 (mova3b2_Lin_bound hlin hL2 h0 α)
    (mova3b2_rot (mova3b2_cz θ r0 r1 z) G)
  rw [mova3b2_N_rot, mova3b2_cz_re] at hl
  have hint : ∫ ξ, mova3b1_W ξ ^ (r0 + 2 * ((θ - z.re) * (r1 - r0) / 2)) * ‖(𝓕 G : 𝓢C) ξ‖ ^ 2 ≤ Nb := by
    refine integral_mono (mova3b2_int_W _ _) (mova3b2_int_W _ _) fun ξ => ?_
    refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    refine Real.rpow_le_rpow_of_exponent_le (mova3b1_W_ge ξ) ?_
    have h1 : |θ - z.re| ≤ 1 := abs_le.2 ⟨by linarith, by linarith⟩
    have h2 : (θ - z.re) * (r1 - r0) ≤ |r1 - r0| := by
      calc (θ - z.re) * (r1 - r0) ≤ |(θ - z.re) * (r1 - r0)| := le_abs_self _
        _ = |θ - z.re| * |r1 - r0| := abs_mul _ _
        _ ≤ 1 * |r1 - r0| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = _ := one_mul _
    have h3 := le_abs_self r0
    calc r0 + 2 * ((θ - z.re) * (r1 - r0) / 2) = r0 + (θ - z.re) * (r1 - r0) := by ring
      _ ≤ E := by rw [hE]; linarith
  refine mul_le_mul hb (hl.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hint) hK0))
    (norm_nonneg _) (by positivity)

lemma mova3b2_boundary (hlin : ∀ f g : 𝓢R, ∀ a : ℝ, T (a • f + g) = a • T f + T g)
    (hL2 : ∀ f, MemLp (T f) 2 (volume : Measure (Euc d))) (f : 𝓢R) {θ r0 r1 s0 s1 j M : ℝ}
    (hM : 0 ≤ M)
    (h : ∀ u : 𝓢R, MemOsc (s0 + j * (s1 - s0)) (T u) ∧
      oscNorm (s0 + j * (s1 - s0)) (T u) ≤
        M * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (r0 + j * (r1 - r0)) (⇑u)))
    (S : Finset (MultiIndex d)) {z : ℂ} (hz : z.re = j) :
    ‖mova3b2_F hlin hL2 f θ r0 r1 s0 s1 S z‖ ≤
      M * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq ((1 - θ) * r0 + θ * r1) (⇑f)) *
        Real.sqrt (∑ α ∈ S, oscEigenvalue d α ^ ((1 - θ) * s0 + θ * s1) *
          hermiteCoeff (T f) α ^ 2) := by
  set sj : ℝ := s0 + j * (s1 - s0) with hsj
  set rj : ℝ := r0 + j * (r1 - r0) with hrj
  set σ : ℝ := (1 - θ) * s0 + θ * s1 with hσ
  set ρ : ℝ := (1 - θ) * r0 + θ * r1 with hρ
  set G : 𝓢C := mova3b2_cx f with hG
  set φ : 𝓢C := mova3b2_rot (mova3b2_cz θ r0 r1 z) G with hφ
  set dco : MultiIndex d → ℝ := fun β => oscEigenvalue d β ^ σ * hermiteCoeff (T f) β with hdco
  set vb : MultiIndex d → ℂ := fun α => mova3_vb (oscEigenvalue d) dco θ s0 s1 z α with hvb
  set Λ : MultiIndex d → ℂ := fun α => mova3b2_Lam (mova3b2_Lin hlin hL2 α) φ with hΛ
  set Y : ℝ := ∑ α ∈ S, oscEigenvalue d α ^ σ * hermiteCoeff (T f) α ^ 2 with hY
  set Nρ : ℝ := HRS.PDE.ToolboxRd.sobolevNormSq ρ (⇑f) with hNρ
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun α _ => mul_nonneg
    (Real.rpow_nonneg (oscEv_pos α).le _) (sq_nonneg _)
  have hN0 : 0 ≤ Nρ := mova3b2_sobolevNormSq_nonneg _ _
  have hF : mova3b2_F hlin hL2 f θ r0 r1 s0 s1 S z = ∑ α ∈ S, vb α * Λ α := rfl
  -- Step 3: the `vb` side
  have hvbsq : ∑ α ∈ S, (‖vb α‖ * oscEigenvalue d α ^ (-sj / 2)) ^ 2 = Y := by
    refine Finset.sum_congr rfl fun α _ => ?_
    have hpos := oscEv_pos (d := d) α
    have h1 := mova3_hv (fun i => oscEv_pos (d := d) i) dco θ s0 s1 z α
    rw [hz] at h1
    rw [mul_pow, mova3_rpow_half_sq hpos, mul_comm]
    have e1 : -(s0 + j * (s1 - s0)) = -sj := by rw [hsj]
    rw [e1] at h1
    rw [h1, hdco]
    simp only
    rw [mul_pow, ← mul_assoc, ← Real.rpow_natCast, ← Real.rpow_mul hpos.le, ← Real.rpow_add hpos]
    have : -σ + σ * ((2 : ℕ) : ℝ) = σ := by push_cast; ring
    rw [this]
  -- Step 4: the `Λ` side
  have hΛsq : ∑ α ∈ S, (‖Λ α‖ * oscEigenvalue d α ^ (sj / 2)) ^ 2 ≤ M ^ 2 * Nρ := by
    have h1 : ∀ α ∈ S, (‖Λ α‖ * oscEigenvalue d α ^ (sj / 2)) ^ 2 =
        oscEigenvalue d α ^ sj * hermiteCoeff (T (mova3b2_re φ)) α ^ 2 +
          oscEigenvalue d α ^ sj * hermiteCoeff (T (mova3b2_im φ)) α ^ 2 := by
      intro α _
      have hpos := oscEv_pos (d := d) α
      rw [mul_pow, mova3_rpow_half_sq hpos, hΛ]
      simp only
      rw [mova3b2_norm_Lam_sq, mova3b2_Lin_apply, mova3b2_Lin_apply]
      ring
    rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib]
    obtain ⟨hu1, hu2⟩ := h (mova3b2_re φ)
    obtain ⟨hv1, hv2⟩ := h (mova3b2_im φ)
    have a1 := mova3b2_sum_le_osc hu1 S
    have a2 := mova3b2_sum_le_osc hv1 S
    have b1 : oscNorm sj (T (mova3b2_re φ)) ^ 2 ≤
        M ^ 2 * HRS.PDE.ToolboxRd.sobolevNormSq rj (⇑(mova3b2_re φ)) := by
      have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hu2 2
      rw [mul_pow, Real.sq_sqrt (mova3b2_sobolevNormSq_nonneg _ _)] at this
      exact this
    have b2 : oscNorm sj (T (mova3b2_im φ)) ^ 2 ≤
        M ^ 2 * HRS.PDE.ToolboxRd.sobolevNormSq rj (⇑(mova3b2_im φ)) := by
      have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hv2 2
      rw [mul_pow, Real.sq_sqrt (mova3b2_sobolevNormSq_nonneg _ _)] at this
      exact this
    obtain ⟨_, _, hsum⟩ := mova3b2_sob φ rj
    have hnn : HRS.PDE.ToolboxRd.sobolevNormSq rj (⇑(mova3b2_re φ)) +
        HRS.PDE.ToolboxRd.sobolevNormSq rj (⇑(mova3b2_im φ)) = Nρ := by
      have hexp : rj + 2 * ((θ - j) * (r1 - r0) / 2) = ρ := by simp only [hrj, hρ]; ring
      rw [hsum, hφ, mova3b2_N_rot, mova3b2_cz_re, hz, hexp, hNρ, mova3b2_sobNormSq_cx]
    calc _ ≤ oscNorm sj (T (mova3b2_re φ)) ^ 2 + oscNorm sj (T (mova3b2_im φ)) ^ 2 :=
          add_le_add a1 a2
      _ ≤ M ^ 2 * HRS.PDE.ToolboxRd.sobolevNormSq rj (⇑(mova3b2_re φ)) +
          M ^ 2 * HRS.PDE.ToolboxRd.sobolevNormSq rj (⇑(mova3b2_im φ)) := add_le_add b1 b2
      _ = M ^ 2 * Nρ := by rw [← mul_add, hnn]
  -- Cauchy-Schwarz
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq S (fun α => ‖vb α‖ * oscEigenvalue d α ^ (-sj / 2))
    (fun α => ‖Λ α‖ * oscEigenvalue d α ^ (sj / 2))
  have hprod : ∀ α ∈ S, (‖vb α‖ * oscEigenvalue d α ^ (-sj / 2)) *
      (‖Λ α‖ * oscEigenvalue d α ^ (sj / 2)) = ‖vb α‖ * ‖Λ α‖ := by
    intro α _
    have hpos := oscEv_pos (d := d) α
    have : oscEigenvalue d α ^ (-sj / 2) * oscEigenvalue d α ^ (sj / 2) = 1 := by
      rw [← Real.rpow_add hpos, show -sj / 2 + sj / 2 = 0 by ring, Real.rpow_zero]
    calc _ = (‖vb α‖ * ‖Λ α‖) * (oscEigenvalue d α ^ (-sj / 2) * oscEigenvalue d α ^ (sj / 2)) := by ring
      _ = _ := by rw [this, mul_one]
  rw [Finset.sum_congr rfl hprod, hvbsq] at hCS
  have hF1 : ‖mova3b2_F hlin hL2 f θ r0 r1 s0 s1 S z‖ ≤ ∑ α ∈ S, ‖vb α‖ * ‖Λ α‖ := by
    rw [hF]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun α _ => ?_)
    rw [norm_mul]
  have hsq : ‖mova3b2_F hlin hL2 f θ r0 r1 s0 s1 S z‖ ^ 2 ≤ (M * Real.sqrt Nρ * Real.sqrt Y) ^ 2 := by
    calc _ ≤ (∑ α ∈ S, ‖vb α‖ * ‖Λ α‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hF1 2
      _ ≤ Y * ∑ α ∈ S, (‖Λ α‖ * oscEigenvalue d α ^ (sj / 2)) ^ 2 := hCS
      _ ≤ Y * (M ^ 2 * Nρ) := mul_le_mul_of_nonneg_left hΛsq hY0
      _ = (M * Real.sqrt Nρ * Real.sqrt Y) ^ 2 := by
          rw [mul_pow, mul_pow, Real.sq_sqrt hN0, Real.sq_sqrt hY0]; ring
  exact le_of_sq_le_sq hsq (by positivity)

lemma mova3b2_three_lines (hlin : ∀ f g : 𝓢R, ∀ a : ℝ, T (a • f + g) = a • T f + T g)
    (hL2 : ∀ f, MemLp (T f) 2 (volume : Measure (Euc d))) (f : 𝓢R)
    {r0 r1 s0 s1 M0 M1 θ : ℝ} (hM0 : 0 ≤ M0) (hM1 : 0 ≤ M1) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (h0 : ∀ u : 𝓢R, MemOsc s0 (T u) ∧
      oscNorm s0 (T u) ≤ M0 * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq r0 (⇑u)))
    (h1 : ∀ u : 𝓢R, MemOsc s1 (T u) ∧
      oscNorm s1 (T u) ≤ M1 * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq r1 (⇑u)))
    (S : Finset (MultiIndex d)) :
    ∑ α ∈ S, oscEigenvalue d α ^ ((1 - θ) * s0 + θ * s1) * hermiteCoeff (T f) α ^ 2 ≤
      M0 ^ (1 - θ) * M1 ^ θ *
        Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq ((1 - θ) * r0 + θ * r1) (⇑f)) *
        Real.sqrt (∑ α ∈ S, oscEigenvalue d α ^ ((1 - θ) * s0 + θ * s1) *
          hermiteCoeff (T f) α ^ 2) := by
  set Y : ℝ := ∑ α ∈ S, oscEigenvalue d α ^ ((1 - θ) * s0 + θ * s1) * hermiteCoeff (T f) α ^ 2
    with hY
  set X : ℝ := Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq ((1 - θ) * r0 + θ * r1) (⇑f)) with hX
  set Y' : ℝ := Real.sqrt Y with hY'
  have hXn : 0 ≤ X := Real.sqrt_nonneg _
  have hYn : 0 ≤ Y' := Real.sqrt_nonneg _
  set F := mova3b2_F hlin hL2 f θ r0 r1 s0 s1 S with hF
  have hdiff : Differentiable ℂ F := mova3b2_F_differentiable hlin hL2 f θ r0 r1 s0 s1 S hM0 h0
  obtain ⟨C, hC⟩ := mova3b2_F_bdd hlin hL2 f hθ0 hθ1 r0 r1 s0 s1 S hM0 h0
  have hB : BddAbove ((norm ∘ F) '' Complex.HadamardThreeLines.verticalClosedStrip 0 1) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact hC z hz.1 hz.2
  have h0' : ∀ u : 𝓢R, MemOsc (s0 + 0 * (s1 - s0)) (T u) ∧
      oscNorm (s0 + 0 * (s1 - s0)) (T u) ≤
        M0 * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (r0 + 0 * (r1 - r0)) (⇑u)) := by
    intro u; simpa using h0 u
  have h1' : ∀ u : 𝓢R, MemOsc (s0 + 1 * (s1 - s0)) (T u) ∧
      oscNorm (s0 + 1 * (s1 - s0)) (T u) ≤
        M1 * Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (r0 + 1 * (r1 - r0)) (⇑u)) := by
    intro u; simpa using h1 u
  have ha : ∀ z ∈ Complex.re ⁻¹' {(0 : ℝ)}, ‖F z‖ ≤ M0 * X * Y' := fun z hz =>
    mova3b2_boundary hlin hL2 f hM0 h0' S (show z.re = 0 from hz)
  have hb : ∀ z ∈ Complex.re ⁻¹' {(1 : ℝ)}, ‖F z‖ ≤ M1 * X * Y' := fun z hz =>
    mova3b2_boundary hlin hL2 f hM1 h1' S (show z.re = 1 from hz)
  have hzmem : (θ : ℂ) ∈ Complex.HadamardThreeLines.verticalClosedStrip 0 1 := by
    simp only [Complex.HadamardThreeLines.verticalClosedStrip, Set.mem_preimage,
      Complex.ofReal_re, Set.mem_Icc]
    exact ⟨hθ0, hθ1⟩
  have key := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
    (f := F) (z := (θ : ℂ)) (a := M0 * X * Y') (b := M1 * X * Y') (l := 0) (u := 1)
    zero_lt_one hzmem hdiff.diffContOnCl hB ha hb
  have hFθ : F (θ : ℂ) = ((Y : ℝ) : ℂ) := mova3b2_F_theta hlin hL2 f θ r0 r1 s0 s1 S
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun α _ => mul_nonneg
    (Real.rpow_nonneg (oscEv_pos α).le _) (sq_nonneg _)
  rw [hFθ, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hY0] at key
  simp only [Complex.ofReal_re, sub_zero, div_one] at key
  refine key.trans (le_of_eq ?_)
  have hXY : 0 ≤ X * Y' := mul_nonneg hXn hYn
  rw [mul_assoc M0, mul_assoc M1, Real.mul_rpow hM0 hXY, Real.mul_rpow hM1 hXY]
  have : (X * Y') ^ (1 - θ) * (X * Y') ^ θ = X * Y' := by
    rw [← Real.rpow_add' hXY (by linarith : (1 - θ) + θ ≠ 0)]
    simp
  calc M0 ^ (1 - θ) * (X * Y') ^ (1 - θ) * (M1 ^ θ * (X * Y') ^ θ)
      = M0 ^ (1 - θ) * M1 ^ θ * ((X * Y') ^ (1 - θ) * (X * Y') ^ θ) := by ring
    _ = M0 ^ (1 - θ) * M1 ^ θ * X * Y' := by rw [this]; ring

end Main

open HRS.Whole in
/-- **`H → Σ` Stein interpolation** (statement `mo_interp_H_osc_stmt` of `MovInterpAux3`). -/
theorem mo_interp_H_osc (d : ℕ) : mo_interp_H_osc_stmt d := by
  intro T hlin hL2 r0 r1 s0 s1 M0 M1 hM0 hM1 h0 h1 θ hθ f
  set σ : ℝ := (1 - θ) * s0 + θ * s1 with hσ
  set X : ℝ := Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq ((1 - θ) * r0 + θ * r1) (⇑f)) with hX
  set B : ℝ := M0 ^ (1 - θ) * M1 ^ θ with hB
  have hBn : 0 ≤ B := mul_nonneg (Real.rpow_nonneg hM0 _) (Real.rpow_nonneg hM1 _)
  have hXn : 0 ≤ X := Real.sqrt_nonneg _
  set g : MultiIndex d → ℝ := fun α => oscEigenvalue d α ^ σ * hermiteCoeff (T f) α ^ 2 with hg
  have hg0 : ∀ α, 0 ≤ g α := fun α => mul_nonneg (Real.rpow_nonneg (oscEv_pos α).le _) (sq_nonneg _)
  have hbound : ∀ S : Finset (MultiIndex d), ∑ α ∈ S, g α ≤ (B * X) ^ 2 := by
    intro S
    have hl := mova3b2_three_lines hlin hL2 f hM0 hM1 hθ.1 hθ.2 h0 h1 S
    set Y := ∑ α ∈ S, g α with hY
    have hY0 : 0 ≤ Y := Finset.sum_nonneg fun α _ => hg0 α
    have hy : Real.sqrt Y ^ 2 = Y := Real.sq_sqrt hY0
    have hyn : 0 ≤ Real.sqrt Y := Real.sqrt_nonneg _
    have hle : Real.sqrt Y ≤ B * X := by
      by_contra hlt
      rw [not_le] at hlt
      have hpos : 0 < Real.sqrt Y := lt_of_le_of_lt (mul_nonneg hBn hXn) hlt
      nlinarith [hl, hy]
    calc Y = Real.sqrt Y ^ 2 := hy.symm
      _ ≤ (B * X) ^ 2 := pow_le_pow_left₀ hyn hle 2
  have hsum : Summable g := summable_of_sum_le hg0 hbound
  refine ⟨⟨hL2 f, hsum⟩, ?_⟩
  unfold oscNorm
  calc Real.sqrt (∑' α, oscEigenvalue d α ^ σ * hermiteCoeff (T f) α ^ 2)
      ≤ Real.sqrt ((B * X) ^ 2) := Real.sqrt_le_sqrt (Real.tsum_le_of_sum_le (fun α => hg0 α) hbound)
    _ = B * X := Real.sqrt_sq (mul_nonneg hBn hXn)

end HRS.MS.MovOsc
