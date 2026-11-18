import HRS.MS.R26T8AF02b

/-!
# S8.2 observed-time layer, packet T8A.F03: Euler commutator of the critical convolution

`E(T_i h) = T_i(E h) + (s-1) T_i h` with `E h = x ⬝ ∇h`, `s = d/2`.  Route: the Fourier representation of F02a, the exact
dilation law `T_i(h(l·))(x) = l^{1-s} T_i h (l x)` obtained by scaling the Fourier integral, and differentiation in the dilation
parameter at `l = 1` under the integral (dominated by Schwartz tails).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set SchwartzMap
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}


theorem r26t8a_f03_schw_decay {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : 𝓢(E, F)) (N : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ ζ : E, (1 + ‖ζ‖) ^ N * ‖f ζ‖ ≤ C := by
  refine ⟨2 ^ N * (Finset.Iic (N, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) f, by positivity, fun ζ => ?_⟩
  have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N, 0)) (k := N) (n := 0) le_rfl le_rfl f ζ
  simpa using this

/-- tail bound of a Schwartz function at a dilated point, `0 < l < 2` -/
theorem r26t8a_f03_tail_dil {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] (f : 𝓢(E, F)) (N : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ (l : ℝ), 0 < l → l < 2 → ∀ ξ : E,
      ‖f (l⁻¹ • ξ)‖ ≤ C * ((1 + ‖ξ‖) ^ N)⁻¹ := by
  obtain ⟨C, hC, h⟩ := r26t8a_f03_schw_decay f N
  refine ⟨2 ^ N * C, by positivity, fun l hl0 hl2 ξ => ?_⟩
  have hz : 1 + ‖ξ‖ ≤ 2 * (1 + ‖l⁻¹ • ξ‖) := by
    rw [norm_smul, norm_inv, Real.norm_of_nonneg hl0.le]
    have : ‖ξ‖ = l * (l⁻¹ * ‖ξ‖) := by field_simp
    nlinarith [norm_nonneg ξ, mul_nonneg (inv_nonneg.2 hl0.le) (norm_nonneg ξ)]
  have hp : (0 : ℝ) < (1 + ‖ξ‖) ^ N := by positivity
  have hq : (0 : ℝ) < (1 + ‖l⁻¹ • ξ‖) ^ N := by positivity
  have h2 : (1 + ‖ξ‖) ^ N ≤ 2 ^ N * (1 + ‖l⁻¹ • ξ‖) ^ N := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) hz N
  rw [le_mul_inv_iff₀ hp]
  calc ‖f (l⁻¹ • ξ)‖ * (1 + ‖ξ‖) ^ N ≤ ‖f (l⁻¹ • ξ)‖ * (2 ^ N * (1 + ‖l⁻¹ • ξ‖) ^ N) :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = 2 ^ N * ((1 + ‖l⁻¹ • ξ‖) ^ N * ‖f (l⁻¹ • ξ)‖) := by ring
    _ ≤ 2 ^ N * C := by gcongr; exact h _

/-- pointwise derivative in the dilation parameter -/
theorem r26t8a_f03_phi_pt (ψ : 𝓢(Euc d, ℂ)) (ξ : Euc d) {l : ℝ} (hl : 0 < l) :
    HasDerivAt (fun l : ℝ => (((l ^ d)⁻¹ : ℝ) : ℂ) * ψ (l⁻¹ • ξ))
      ((((-(d : ℝ) * ((l ^ d)⁻¹ * l⁻¹) : ℝ)) : ℂ) * ψ (l⁻¹ • ξ) +
        (((l ^ d)⁻¹ : ℝ) : ℂ) * (fderiv ℝ ψ (l⁻¹ • ξ)) ((-(l⁻¹ * l⁻¹)) • ξ)) l := by
  have h1 : HasDerivAt (fun l : ℝ => (l ^ d)⁻¹) (-(d : ℝ) * ((l ^ d)⁻¹ * l⁻¹)) l := by
    have := (hasDerivAt_pow d l).inv (pow_pos hl d).ne'
    convert this using 1
    rcases d with _ | d
    · simp
    · simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
      field_simp
      ring
  have h2 : HasDerivAt (fun l : ℝ => l⁻¹ • ξ) ((-(l⁻¹ * l⁻¹)) • ξ) l := by
    have := (hasDerivAt_inv hl.ne').smul_const ξ
    convert this using 2
    simp [pow_two]
  have h3 : HasDerivAt (fun l : ℝ => ψ (l⁻¹ • ξ)) ((fderiv ℝ ψ (l⁻¹ • ξ)) ((-(l⁻¹ * l⁻¹)) • ξ)) l :=
    (ψ.differentiableAt.hasFDerivAt).comp_hasDerivAt l h2
  exact (h1.ofReal_comp).mul h3

theorem r26t8a_f03_phi_bound (ψ : 𝓢(Euc d, ℂ)) (N : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (l : ℝ), 1/2 < l → l < 3/2 → ∀ ξ : Euc d,
      ‖(((-(d : ℝ) * ((l ^ d)⁻¹ * l⁻¹) : ℝ)) : ℂ) * ψ (l⁻¹ • ξ) +
        (((l ^ d)⁻¹ : ℝ) : ℂ) * (fderiv ℝ ψ (l⁻¹ • ξ)) ((-(l⁻¹ * l⁻¹)) • ξ)‖ ≤
        K * ((1 + ‖ξ‖) ^ N)⁻¹ ∧
      ‖(((l ^ d)⁻¹ : ℝ) : ℂ) * ψ (l⁻¹ • ξ)‖ ≤ K * ((1 + ‖ξ‖) ^ N)⁻¹ := by
  obtain ⟨C0, hC0, h0⟩ := r26t8a_f03_tail_dil ψ N
  obtain ⟨C1, hC1, h1⟩ := r26t8a_f03_tail_dil (SchwartzMap.fderivCLM ℝ _ _ ψ) (N + 1)
  refine ⟨(d + 1) * 2 ^ d * 2 * C0 + 2 ^ d * 4 * C1, by positivity, fun l hl1 hl2 ξ => ?_⟩
  have hl0 : 0 < l := by linarith
  have hld : (l ^ d)⁻¹ ≤ 2 ^ d := by
    rw [inv_le_comm₀ (pow_pos hl0 d) (by positivity)]
    calc ((2:ℝ) ^ d)⁻¹ = (2⁻¹) ^ d := by rw [inv_pow]
      _ ≤ l ^ d := pow_le_pow_left₀ (by norm_num) (by linarith) d
  have hli : l⁻¹ ≤ 2 := by
    rw [inv_le_comm₀ hl0 (by norm_num)]; linarith
  have hli0 : 0 ≤ l⁻¹ := inv_nonneg.2 hl0.le
  have hldp : 0 ≤ (l ^ d)⁻¹ := by positivity
  have hW : (0 : ℝ) < ((1 + ‖ξ‖) ^ N)⁻¹ := by positivity
  have hψ := h0 l hl0 (by linarith) ξ
  have hDψ := h1 l hl0 (by linarith) ξ
  have h1x : (0:ℝ) < 1 + ‖ξ‖ := by positivity
  have hDψ' : ‖fderiv ℝ ψ (l⁻¹ • ξ)‖ * (1 + ‖ξ‖) ≤ C1 * ((1 + ‖ξ‖) ^ N)⁻¹ := by
    have : ((1 + ‖ξ‖) ^ (N + 1))⁻¹ = ((1 + ‖ξ‖) ^ N)⁻¹ * (1 + ‖ξ‖)⁻¹ := by
      rw [pow_succ, mul_inv]
    have h2 : ‖(SchwartzMap.fderivCLM ℝ _ _ ψ) (l⁻¹ • ξ)‖ = ‖fderiv ℝ ψ (l⁻¹ • ξ)‖ := by simp
    rw [h2, this] at hDψ
    calc ‖fderiv ℝ ψ (l⁻¹ • ξ)‖ * (1 + ‖ξ‖) ≤ C1 * (((1 + ‖ξ‖) ^ N)⁻¹ * (1 + ‖ξ‖)⁻¹) * (1 + ‖ξ‖) :=
          by gcongr
      _ = C1 * ((1 + ‖ξ‖) ^ N)⁻¹ := by field_simp
  have hξl : ‖(-(l⁻¹ * l⁻¹)) • ξ‖ ≤ 4 * (1 + ‖ξ‖) := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg (mul_nonneg hli0 hli0)]
    have : l⁻¹ * l⁻¹ ≤ 4 := by nlinarith
    nlinarith [norm_nonneg ξ, mul_nonneg hli0 hli0]
  have hterm0 : ‖(((l ^ d)⁻¹ : ℝ) : ℂ) * ψ (l⁻¹ • ξ)‖ ≤ 2 ^ d * C0 * ((1 + ‖ξ‖) ^ N)⁻¹ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hldp]
    calc (l ^ d)⁻¹ * ‖ψ (l⁻¹ • ξ)‖ ≤ 2 ^ d * (C0 * ((1 + ‖ξ‖) ^ N)⁻¹) := by gcongr
      _ = _ := by ring
  have hterm1 : ‖(((-(d : ℝ) * ((l ^ d)⁻¹ * l⁻¹) : ℝ)) : ℂ) * ψ (l⁻¹ • ξ)‖ ≤
      d * 2 ^ d * 2 * C0 * ((1 + ‖ξ‖) ^ N)⁻¹ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg (Nat.cast_nonneg d),
      abs_of_nonneg (mul_nonneg hldp hli0)]
    calc (d : ℝ) * ((l ^ d)⁻¹ * l⁻¹) * ‖ψ (l⁻¹ • ξ)‖ ≤ d * (2 ^ d * 2) * (C0 * ((1 + ‖ξ‖) ^ N)⁻¹) := by
          gcongr
      _ = _ := by ring
  have hterm2 : ‖(((l ^ d)⁻¹ : ℝ) : ℂ) * (fderiv ℝ ψ (l⁻¹ • ξ)) ((-(l⁻¹ * l⁻¹)) • ξ)‖ ≤
      2 ^ d * 4 * C1 * ((1 + ‖ξ‖) ^ N)⁻¹ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hldp]
    have e1 : ‖(fderiv ℝ ψ (l⁻¹ • ξ)) ((-(l⁻¹ * l⁻¹)) • ξ)‖ ≤ ‖fderiv ℝ ψ (l⁻¹ • ξ)‖ * (4 * (1 + ‖ξ‖)) :=
      (ContinuousLinearMap.le_opNorm _ _).trans (by gcongr)
    calc (l ^ d)⁻¹ * ‖(fderiv ℝ ψ (l⁻¹ • ξ)) ((-(l⁻¹ * l⁻¹)) • ξ)‖
        ≤ 2 ^ d * (‖fderiv ℝ ψ (l⁻¹ • ξ)‖ * (4 * (1 + ‖ξ‖))) := by gcongr
      _ = 2 ^ d * 4 * (‖fderiv ℝ ψ (l⁻¹ • ξ)‖ * (1 + ‖ξ‖)) := by ring
      _ ≤ 2 ^ d * 4 * (C1 * ((1 + ‖ξ‖) ^ N)⁻¹) := by gcongr
      _ = _ := by ring
  refine ⟨?_, ?_⟩
  · refine (norm_add_le _ _).trans ?_
    have : ((d : ℝ) + 1) * 2 ^ d * 2 * C0 ≥ d * 2 ^ d * 2 * C0 := by
      nlinarith [pow_pos (two_pos : (0:ℝ) < 2) d, hC0, Nat.cast_nonneg (α := ℝ) d]
    nlinarith [mul_le_mul_of_nonneg_right this hW.le]
  · refine hterm0.trans ?_
    have : (2:ℝ) ^ d * C0 ≤ ((d : ℝ) + 1) * 2 ^ d * 2 * C0 + 2 ^ d * 4 * C1 := by
      nlinarith [pow_pos (two_pos : (0:ℝ) < 2) d, hC0, hC1, Nat.cast_nonneg (α := ℝ) d,
        mul_nonneg (pow_pos (two_pos : (0:ℝ) < 2) d).le hC1, mul_nonneg (pow_pos (two_pos : (0:ℝ) < 2) d).le hC0,
        mul_nonneg (Nat.cast_nonneg (α := ℝ) d) (mul_nonneg (pow_pos (two_pos : (0:ℝ) < 2) d).le hC0)]
    exact mul_le_mul_of_nonneg_right this hW.le

theorem r26t8a_f03_norm_expI (x ξ : Euc d) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x ξ : ℝ))‖ = 1 := by
  have : (2 * (Real.pi : ℂ) * Complex.I * ((inner ℝ x ξ : ℝ) : ℂ)) =
      ((2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

theorem r26t8a_f03_phi_deriv (Mc : Euc d → ℂ) (hMm : AEStronglyMeasurable Mc volume)
    (ψ : 𝓢(Euc d, ℂ)) (x : Euc d) (N : ℕ)
    (hW : Integrable (fun ξ : Euc d => ‖Mc ξ‖ * ((1 + ‖ξ‖) ^ N)⁻¹) volume) :
    HasDerivAt (fun l : ℝ => ∫ ξ : Euc d, Mc ξ * (((l ^ d)⁻¹ : ℝ) : ℂ) * ψ (l⁻¹ • ξ) *
        Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x ξ : ℝ)))
      (∫ ξ : Euc d, Mc ξ * (-(d : ℂ) * ψ ξ - fderiv ℝ ψ ξ ξ) *
        Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x ξ : ℝ))) 1 := by
  obtain ⟨K, hK, hKb⟩ := r26t8a_f03_phi_bound ψ N
  have hcD : Continuous (fderiv ℝ ψ) := (ψ.smooth 1).continuous_fderiv (by norm_num)
  have hcE : Continuous (fun ξ : Euc d => Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x ξ : ℝ))) := by
    fun_prop
  set F : ℝ → Euc d → ℂ := fun l ξ => Mc ξ * (((l ^ d)⁻¹ : ℝ) : ℂ) * ψ (l⁻¹ • ξ) *
        Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x ξ : ℝ)) with hF
  set F' : ℝ → Euc d → ℂ := fun l ξ => Mc ξ *
      ((((-(d : ℝ) * ((l ^ d)⁻¹ * l⁻¹) : ℝ)) : ℂ) * ψ (l⁻¹ • ξ) +
        (((l ^ d)⁻¹ : ℝ) : ℂ) * (fderiv ℝ ψ (l⁻¹ • ξ)) ((-(l⁻¹ * l⁻¹)) • ξ)) *
        Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x ξ : ℝ)) with hF'
  have hmeasF : ∀ l, AEStronglyMeasurable (F l) volume := fun l =>
    ((hMm.mul aestronglyMeasurable_const).mul
      (ψ.continuous.comp (continuous_const_smul l⁻¹)).aestronglyMeasurable).mul hcE.aestronglyMeasurable
  have hmeasF' : ∀ l, AEStronglyMeasurable (F' l) volume := fun l =>
    (hMm.mul ((continuous_const.mul (ψ.continuous.comp (continuous_const_smul l⁻¹))).add
      (continuous_const.mul ((hcD.comp (continuous_const_smul l⁻¹)).clm_apply
        (continuous_const_smul _)))).aestronglyMeasurable).mul hcE.aestronglyMeasurable
  have hball : Metric.ball (1 : ℝ) (1 / 2) ∈ 𝓝 (1 : ℝ) := Metric.ball_mem_nhds _ (by norm_num)
  have hmem : ∀ l ∈ Metric.ball (1 : ℝ) (1 / 2), 1 / 2 < l ∧ l < 3 / 2 := fun l hl => by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hl
    constructor <;> linarith [hl.1, hl.2]
  have hE1 : ∀ ξ, ‖Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x ξ : ℝ))‖ = 1 :=
    r26t8a_f03_norm_expI x
  have hbnd : Integrable (fun ξ : Euc d => K * (‖Mc ξ‖ * ((1 + ‖ξ‖) ^ N)⁻¹)) volume :=
    hW.const_mul K
  have hint : Integrable (F 1) volume := by
    refine hbnd.mono' (hmeasF 1) (Eventually.of_forall fun ξ => ?_)
    have := (hKb 1 (by norm_num) (by norm_num) ξ).2
    show ‖F 1 ξ‖ ≤ K * (‖Mc ξ‖ * ((1 + ‖ξ‖) ^ N)⁻¹)
    calc ‖F 1 ξ‖ = ‖Mc ξ‖ * ‖(((1 ^ d)⁻¹ : ℝ) : ℂ) * ψ ((1:ℝ)⁻¹ • ξ)‖ := by
          simp only [hF, norm_mul, hE1, mul_one]; ring
      _ ≤ ‖Mc ξ‖ * (K * ((1 + ‖ξ‖) ^ N)⁻¹) := by gcongr
      _ = _ := by ring
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := F) (F' := F')
    (x₀ := 1) (s := Metric.ball (1 : ℝ) (1 / 2)) (bound := fun ξ => K * (‖Mc ξ‖ * ((1 + ‖ξ‖) ^ N)⁻¹))
    hball (Eventually.of_forall hmeasF) hint (hmeasF' 1) ?_ hbnd ?_
  · have e : (∫ ξ : Euc d, Mc ξ * (-(d : ℂ) * ψ ξ - fderiv ℝ ψ ξ ξ) *
        Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x ξ : ℝ))) = ∫ ξ, F' 1 ξ := by
      refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
      simp only [hF', one_pow, inv_one, one_smul, neg_smul, map_neg, Complex.ofReal_one, one_mul, mul_one]
      push_cast
      ring_nf
    rw [e]
    exact key.2
  · refine Eventually.of_forall fun ξ l hl => ?_
    obtain ⟨h1, h2⟩ := hmem l hl
    have := (hKb l h1 h2 ξ).1
    show ‖F' l ξ‖ ≤ K * (‖Mc ξ‖ * ((1 + ‖ξ‖) ^ N)⁻¹)
    calc ‖F' l ξ‖ = ‖Mc ξ‖ * ‖(((-(d : ℝ) * ((l ^ d)⁻¹ * l⁻¹) : ℝ)) : ℂ) * ψ (l⁻¹ • ξ) +
        (((l ^ d)⁻¹ : ℝ) : ℂ) * (fderiv ℝ ψ (l⁻¹ • ξ)) ((-(l⁻¹ * l⁻¹)) • ξ)‖ := by
          simp only [hF', norm_mul, hE1, mul_one]
      _ ≤ ‖Mc ξ‖ * (K * ((1 + ‖ξ‖) ^ N)⁻¹) := by gcongr
      _ = _ := by ring
  · refine Eventually.of_forall fun ξ l hl => ?_
    obtain ⟨h1, h2⟩ := hmem l hl
    have hl0 : 0 < l := by linarith
    have := ((r26t8a_f03_phi_pt ψ ξ hl0).const_mul (Mc ξ)).mul_const
      (Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x ξ : ℝ)))
    have hfun : (fun l => F l ξ) = fun y : ℝ => Mc ξ * ((((y ^ d)⁻¹ : ℝ) : ℂ) * ψ (y⁻¹ • ξ)) *
        Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x ξ : ℝ)) := by
      funext y; simp only [hF]; ring
    show HasDerivAt (fun l => F l ξ) (F' l ξ) l
    rw [hfun]
    exact this

theorem r26t8a_f03_fourier_dil (h : Euc d → ℝ) {l : ℝ} (hl : 0 < l) (ξ : Euc d) :
    𝓕 (fun y : Euc d => ((h (l • y) : ℝ) : ℂ)) ξ =
      (((l ^ d)⁻¹ : ℝ) : ℂ) * 𝓕 (fun y : Euc d => ((h y : ℝ) : ℂ)) (l⁻¹ • ξ) := by
  rw [Real.fourier_eq, Real.fourier_eq]
  have := Measure.integral_comp_smul (μ := (volume : Measure (Euc d)))
    (fun z : Euc d => (Real.fourierChar (-inner ℝ (l⁻¹ • z) ξ)) • ((h z : ℝ) : ℂ)) l
  simp only [finrank_euclideanSpace, Fintype.card_fin] at this
  have e1 : (fun y : Euc d => (Real.fourierChar (-inner ℝ y ξ)) • ((h (l • y) : ℝ) : ℂ)) =
      fun y => (Real.fourierChar (-inner ℝ (l⁻¹ • (l • y)) ξ)) • ((h (l • y) : ℝ) : ℂ) := by
    ext y; rw [inv_smul_smul₀ hl.ne']
  rw [e1, this]
  have e2 : (fun z : Euc d => (Real.fourierChar (-inner ℝ (l⁻¹ • z) ξ)) • ((h z : ℝ) : ℂ)) =
      fun z => (Real.fourierChar (-inner ℝ z (l⁻¹ • ξ))) • ((h z : ℝ) : ℂ) := by
    ext z; rw [real_inner_smul_left, real_inner_smul_right]
  rw [e2, abs_of_pos (inv_pos.2 (pow_pos hl d))]
  simp [Complex.real_smul]

theorem r26t8a_f03_scale_int (Mc ψ : Euc d → ℂ) (a : ℝ)
    (hMc : ∀ (l : ℝ), 0 < l → ∀ η, Mc (l • η) = ((l ^ a : ℝ) : ℂ) * Mc η)
    {l : ℝ} (hl : 0 < l) (x : Euc d) :
    ∫ ξ : Euc d, Mc ξ * (((l ^ d)⁻¹ : ℝ) : ℂ) * ψ (l⁻¹ • ξ) *
        Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x ξ : ℝ)) =
      ((l ^ a : ℝ) : ℂ) * ∫ η : Euc d, Mc η * ψ η *
        Complex.exp (2 * Real.pi * Complex.I * (inner ℝ (l • x) η : ℝ)) := by
  have := Measure.integral_comp_inv_smul (μ := (volume : Measure (Euc d)))
    (fun η : Euc d => Mc (l • η) * (((l ^ d)⁻¹ : ℝ) : ℂ) * ψ η *
        Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x (l • η) : ℝ))) l
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_smul, mul_inv_cancel₀ hl.ne', one_smul] at this
  rw [this, abs_of_pos (pow_pos hl d), Complex.real_smul]
  have e2 : ∀ η : Euc d, Mc (l • η) * (((l ^ d)⁻¹ : ℝ) : ℂ) * ψ η *
        Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x (l • η) : ℝ)) =
      (((l ^ d)⁻¹ : ℝ) : ℂ) * (((l ^ a : ℝ) : ℂ) * (Mc η * ψ η *
        Complex.exp (2 * Real.pi * Complex.I * (inner ℝ (l • x) η : ℝ)))) := by
    intro η
    rw [hMc l hl η, real_inner_smul_right, real_inner_smul_left]
    ring_nf
  simp_rw [e2]
  rw [integral_const_mul, integral_const_mul]
  have : ((l ^ d : ℝ) : ℂ) * (((l ^ d)⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ (pow_pos hl d).ne']; simp
  rw [← mul_assoc, this, one_mul]

/-- derivative of the Fourier transform of a dilate -/
theorem r26t8a_f03_fourier_dil_deriv (h g : 𝓢(Euc d, ℝ)) (hg : ∀ x, g x = fderiv ℝ h x x) (ξ : Euc d) :
    HasDerivAt (fun l : ℝ => 𝓕 (fun y : Euc d => ((h (l • y) : ℝ) : ℂ)) ξ)
      (𝓕 (fun y : Euc d => ((g y : ℝ) : ℂ)) ξ) 1 := by
  obtain ⟨C, hC, hCb⟩ := r26t8a_f03_tail_dil (SchwartzMap.fderivCLM ℝ _ _ h) (d + 2)
  have hcD : Continuous (fderiv ℝ h) := (h.smooth 1).continuous_fderiv (by norm_num)
  simp only [Real.fourier_eq, Circle.smul_def, smul_eq_mul]
  set F : ℝ → Euc d → ℂ := fun l y =>
    (Real.fourierChar (-inner ℝ y ξ) : ℂ) * ((h (l • y) : ℝ) : ℂ) with hF
  set F' : ℝ → Euc d → ℂ := fun l y =>
    (Real.fourierChar (-inner ℝ y ξ) : ℂ) * (((fderiv ℝ h (l • y)) y : ℝ) : ℂ) with hF'
  have hcE : Continuous (fun y : Euc d => (Real.fourierChar (-inner ℝ y ξ) : ℂ)) := by
    fun_prop
  have hne : ∀ y : Euc d, ‖(Real.fourierChar (-inner ℝ y ξ) : ℂ)‖ = 1 := fun y => by
    simp
  have hmeasF : ∀ l, AEStronglyMeasurable (F l) volume := fun l =>
    (hcE.mul (Complex.continuous_ofReal.comp (h.continuous.comp (continuous_const_smul l)))).aestronglyMeasurable
  have hmeasF' : ∀ l, AEStronglyMeasurable (F' l) volume := fun l =>
    (hcE.mul (Complex.continuous_ofReal.comp ((hcD.comp (continuous_const_smul l)).clm_apply
      continuous_id))).aestronglyMeasurable
  have hball : Metric.ball (1 : ℝ) (1 / 2) ∈ 𝓝 (1 : ℝ) := Metric.ball_mem_nhds _ (by norm_num)
  have hmem : ∀ l ∈ Metric.ball (1 : ℝ) (1 / 2), 1 / 2 < l ∧ l < 3 / 2 := fun l hl => by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hl
    constructor <;> linarith [hl.1, hl.2]
  have hbnd : Integrable (fun y : Euc d => C * (1 + ‖y‖) ^ (-((d + 1 : ℕ) : ℝ))) volume := by
    refine (integrable_one_add_norm ?_).const_mul C
    simp
  have hint : Integrable (F 1) volume := by
    refine (h.integrable (μ := volume)).norm.mono' (hmeasF 1) (Eventually.of_forall fun y => ?_)
    simp [hF, hne]
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (F := F) (F' := F')
    (x₀ := 1) (s := Metric.ball (1 : ℝ) (1 / 2)) (bound := fun y => C * (1 + ‖y‖) ^ (-((d + 1 : ℕ) : ℝ)))
    hball (Eventually.of_forall hmeasF) hint (hmeasF' 1) ?_ hbnd ?_
  · have e : (∫ y : Euc d, (Real.fourierChar (-inner ℝ y ξ) : ℂ) * ((g y : ℝ) : ℂ)) =
        ∫ y, F' 1 y := by
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      simp only [hF', hg, one_smul]
    rw [e]
    exact key.2
  · refine Eventually.of_forall fun y l hl => ?_
    obtain ⟨h1, h2⟩ := hmem l hl
    have hl0 : 0 < l := by linarith
    have hl2 : l⁻¹ < 2 := by rw [inv_lt_comm₀ hl0 (by norm_num)]; linarith
    have := hCb l⁻¹ (inv_pos.2 hl0) hl2 y
    rw [inv_inv] at this
    simp only [fderivCLM_apply] at this
    show ‖F' l y‖ ≤ C * (1 + ‖y‖) ^ (-((d + 1 : ℕ) : ℝ))
    have e1 : ‖F' l y‖ ≤ ‖fderiv ℝ h (l • y)‖ * ‖y‖ := by
      simp only [hF', norm_mul, hne, one_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (fderiv ℝ h (l • y)).le_opNorm y
    have hp : (0 : ℝ) < 1 + ‖y‖ := by positivity
    calc ‖F' l y‖ ≤ ‖fderiv ℝ h (l • y)‖ * ‖y‖ := e1
      _ ≤ (C * ((1 + ‖y‖) ^ (d + 2))⁻¹) * (1 + ‖y‖) := by
          gcongr
          · linarith [norm_nonneg y]
      _ = C * (1 + ‖y‖) ^ (-((d + 1 : ℕ) : ℝ)) := by
          rw [Real.rpow_neg hp.le, Real.rpow_natCast]
          field_simp
          ring
  · refine Eventually.of_forall fun y l hl => ?_
    have h1 : HasDerivAt (fun l : ℝ => l • y) y l := by
      simpa using (hasDerivAt_id l).smul_const y
    have hd : DifferentiableAt ℝ (⇑h) (l • y) := (h.smooth 1).differentiable (by norm_num) _
    have h2 : HasDerivAt (fun l : ℝ => h (l • y)) ((fderiv ℝ h (l • y)) y) l :=
      hd.hasFDerivAt.comp_hasDerivAt l h1
    exact (h2.ofReal_comp).const_mul (Real.fourierChar (-inner ℝ y ξ) : ℂ)

theorem r26t8a_f03_euler_schw (h : 𝓢(Euc d, ℝ)) : ∃ g : 𝓢(Euc d, ℝ), ∀ x, g x = fderiv ℝ h x x := by
  have hg : (id : Euc d → Euc d).HasTemperateGrowth := Function.HasTemperateGrowth.id
  refine ⟨bilinLeftCLM (ContinuousLinearMap.id ℝ (Euc d →L[ℝ] ℝ)) hg (SchwartzMap.fderivCLM ℝ _ _ h),
    fun x => ?_⟩
  simp [bilinLeftCLM_apply]

theorem r26t8a_f03_fourier_schw (h : 𝓢(Euc d, ℝ)) :
    ∃ ψ : 𝓢(Euc d, ℂ), ∀ ξ, ψ ξ = 𝓕 (fun y : Euc d => ((h y : ℝ) : ℂ)) ξ := by
  set φ : 𝓢(Euc d, ℂ) := h.postcompCLM (𝕜 := ℝ) Complex.ofRealCLM with hφ
  refine ⟨𝓕 φ, fun ξ => ?_⟩
  have : ⇑φ = fun y => ((h y : ℝ) : ℂ) := rfl
  rw [SchwartzMap.fourier_coe, this]

theorem r26t8a_f03_fourier_euler (h g : 𝓢(Euc d, ℝ)) (hg : ∀ x, g x = fderiv ℝ h x x)
    (ψ : 𝓢(Euc d, ℂ)) (hψ : ∀ ξ, ψ ξ = 𝓕 (fun y : Euc d => ((h y : ℝ) : ℂ)) ξ) (ξ : Euc d) :
    𝓕 (fun y : Euc d => ((g y : ℝ) : ℂ)) ξ = -(d : ℂ) * ψ ξ - fderiv ℝ ψ ξ ξ := by
  have d1 := r26t8a_f03_fourier_dil_deriv h g hg ξ
  have d2 := (r26t8a_f03_phi_pt ψ ξ (one_pos : (0:ℝ) < 1)).congr_of_eventuallyEq
    (f₁ := fun l : ℝ => 𝓕 (fun y : Euc d => ((h (l • y) : ℝ) : ℂ)) ξ) ?_
  · have := d1.unique d2
    rw [this]
    simp only [one_pow, inv_one, mul_one, one_smul, neg_smul, map_neg, Complex.ofReal_neg, Complex.ofReal_natCast]
    push_cast
    ring
  · filter_upwards [Ioi_mem_nhds (one_pos : (0:ℝ) < 1)] with l hl
    rw [r26t8a_f03_fourier_dil h hl, hψ]

/-- the symbol of the critical convolution (without the datum) -/
def r26t8a_f03_Mc (c : ℝ) (i : Fin d) (ξ : Euc d) : ℂ :=
  ((c * (2 * Real.pi * ξ i) * ‖ξ‖ ^ (-criticalS d) : ℝ) : ℂ) * Complex.I

theorem r26t8a_f03_Mc_hom (c : ℝ) (i : Fin d) {l : ℝ} (hl : 0 < l) (η : Euc d) :
    r26t8a_f03_Mc c i (l • η) = ((l ^ (1 - criticalS d) : ℝ) : ℂ) * r26t8a_f03_Mc c i η := by
  unfold r26t8a_f03_Mc
  have h1 : ‖l • η‖ = l * ‖η‖ := by rw [norm_smul, Real.norm_of_nonneg hl.le]
  have h2 : (l • η) i = l * η i := by simp
  have h3 : l ^ (1 - criticalS d) = l * l ^ (-criticalS d) := by
    rw [sub_eq_add_neg, Real.rpow_add hl, Real.rpow_one]
  rw [h1, h2, Real.mul_rpow hl.le (norm_nonneg _), h3]
  push_cast
  ring

theorem r26t8a_f03_Mc_meas (c : ℝ) (i : Fin d) : Measurable (r26t8a_f03_Mc c i) := by
  unfold r26t8a_f03_Mc
  refine Measurable.mul (Complex.measurable_ofReal.comp ?_) measurable_const
  exact (measurable_const.mul (measurable_const.mul
    (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.measurable)).mul (measurable_norm.pow_const _)

theorem r26t8a_f03_ball_int (hd : 2 ≤ d) :
    IntegrableOn (fun ξ : Euc d => ‖ξ‖ ^ (2 - (d : ℝ))) (Metric.ball (0 : Euc d) 1) volume := by
  rcases Nat.eq_or_lt_of_le hd with h2 | h3
  · subst h2
    have : (fun ξ : Euc 2 => ‖ξ‖ ^ (2 - ((2 : ℕ) : ℝ))) = fun _ => 1 := by
      funext ξ; simp
    rw [this]
    exact integrableOn_const measure_ball_lt_top.ne
  · have hdR : (2 : ℝ) < d := by exact_mod_cast h3
    have h0 := HRS.Whole.u2_integrableOn_ball_rpow (d := d) (by omega) (a := (d : ℝ) - 2) (by linarith)
      (by linarith)
    have e : -((d : ℝ) - 2) = 2 - (d : ℝ) := by ring
    simp_rw [e] at h0
    exact h0

theorem r26t8a_f03_Mc_int (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) (i : Fin d) :
    Integrable (fun ξ : Euc d => ‖r26t8a_f03_Mc c i ξ‖ * ((1 + ‖ξ‖) ^ (d + 1))⁻¹) volume := by
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs1 : (1 : ℝ) ≤ criticalS d := by unfold criticalS; linarith
  have hfar : Integrable (fun ξ : Euc d => ((1 + ‖ξ‖) ^ (d + 1))⁻¹) volume := by
    have := integrable_one_add_norm (E := Euc d) (μ := volume) (r := ((d + 1 : ℕ) : ℝ)) (by simp)
    refine this.congr (Eventually.of_forall fun ξ => ?_)
    have hp : (0 : ℝ) < 1 + ‖ξ‖ := by positivity
    show (1 + ‖ξ‖) ^ (-((d + 1 : ℕ) : ℝ)) = ((1 + ‖ξ‖) ^ (d + 1))⁻¹
    rw [Real.rpow_neg hp.le, Real.rpow_natCast]
  have hnear : Integrable ((Metric.ball (0 : Euc d) 1).indicator (fun ξ : Euc d => ‖ξ‖ ^ (2 - (d : ℝ)))) volume :=
    (r26t8a_f03_ball_int hd).integrable_indicator Metric.isOpen_ball.measurableSet
  have hbd : Integrable (fun ξ : Euc d => c * (2 * Real.pi) *
      ((Metric.ball (0 : Euc d) 1).indicator (fun ξ : Euc d => ‖ξ‖ ^ (2 - (d : ℝ))) ξ +
        ((1 + ‖ξ‖) ^ (d + 1))⁻¹)) volume := (hnear.add hfar).const_mul _
  refine hbd.mono' ((r26t8a_f03_Mc_meas c i).norm.mul
    (((measurable_const.add measurable_norm).pow_const _).inv)).aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  show ‖‖r26t8a_f03_Mc c i ξ‖ * ((1 + ‖ξ‖) ^ (d + 1))⁻¹‖ ≤ _
  have hW0 : (0 : ℝ) < ((1 + ‖ξ‖) ^ (d + 1))⁻¹ := by positivity
  have hW1 : ((1 + ‖ξ‖) ^ (d + 1))⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]
    exact one_le_pow₀ (by linarith [norm_nonneg ξ])
  rw [Real.norm_of_nonneg (by positivity)]
  by_cases hξ : ξ = 0
  · subst hξ
    simp [r26t8a_f03_Mc]
    positivity
  have hp : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have hM : ‖r26t8a_f03_Mc c i ξ‖ ≤ c * (2 * Real.pi) * ‖ξ‖ ^ (1 - criticalS d) := by
    unfold r26t8a_f03_Mc
    rw [norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
      abs_of_pos hc, abs_of_pos (Real.rpow_pos_of_pos hp _), abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    have h1 : |ξ i| ≤ ‖ξ‖ := HRS.MS.UniqN0.n0_coord_le ξ i
    have h2 : ‖ξ‖ ^ (-criticalS d) * ‖ξ‖ = ‖ξ‖ ^ (1 - criticalS d) := by
      rw [← Real.rpow_add_one hp.ne']; congr 1; ring
    calc c * (2 * Real.pi * |ξ i|) * ‖ξ‖ ^ (-criticalS d)
        ≤ c * (2 * Real.pi * ‖ξ‖) * ‖ξ‖ ^ (-criticalS d) := by gcongr
      _ = c * (2 * Real.pi) * (‖ξ‖ ^ (-criticalS d) * ‖ξ‖) := by ring
      _ = _ := by rw [h2]
  by_cases hb : ξ ∈ Metric.ball (0 : Euc d) 1
  · rw [Set.indicator_of_mem hb]
    have hn : ‖ξ‖ < 1 := by simpa using hb
    have h3 : ‖ξ‖ ^ (1 - criticalS d) ≤ ‖ξ‖ ^ (2 - (d : ℝ)) := by
      refine Real.rpow_le_rpow_of_exponent_ge hp hn.le ?_
      unfold criticalS; linarith
    calc ‖r26t8a_f03_Mc c i ξ‖ * ((1 + ‖ξ‖) ^ (d + 1))⁻¹
        ≤ (c * (2 * Real.pi) * ‖ξ‖ ^ (2 - (d : ℝ))) * 1 := by
          gcongr
          exact hM.trans (by gcongr)
      _ ≤ _ := by
          rw [mul_one, mul_add]
          have : 0 ≤ c * (2 * Real.pi) * ((1 + ‖ξ‖) ^ (d + 1))⁻¹ := by positivity
          linarith
  · rw [Set.indicator_of_notMem hb, zero_add]
    have hn : 1 ≤ ‖ξ‖ := by simpa using hb
    have h3 : ‖ξ‖ ^ (1 - criticalS d) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hn (by linarith)
    calc ‖r26t8a_f03_Mc c i ξ‖ * ((1 + ‖ξ‖) ^ (d + 1))⁻¹
        ≤ (c * (2 * Real.pi) * 1) * ((1 + ‖ξ‖) ^ (d + 1))⁻¹ := by
          gcongr
          exact hM.trans (by gcongr)
      _ = _ := by ring

/-- **T8A.F03**: Euler commutator of the actual critical first-convolution operator -/
theorem r26t8a_forceConv_euler (d : ℕ) (hd : 2 ≤ d) (i : Fin d)
    (h : SchwartzMap (Euc d) ℝ) :
    r26t8a_Euler (r26t8a_forceConv i h) = fun x =>
      r26t8a_forceConv i (r26t8a_Euler h) x + (criticalS d-1)*r26t8a_forceConv i h x := by
  obtain ⟨c, hc, H⟩ := r26t8a_forceConv_fourier_int d hd
  have hd1 : 1 ≤ d := by omega
  obtain ⟨g, hg⟩ := r26t8a_f03_euler_schw h
  obtain ⟨ψ, hψ⟩ := r26t8a_f03_fourier_schw h
  obtain ⟨ψg, hψg⟩ := r26t8a_f03_fourier_schw g
  have hEh : r26t8a_Euler (⇑h) = ⇑g := funext fun x => (hg x).symm
  funext x
  rw [hEh]
  have rep : ∀ (k : SchwartzMap (Euc d) ℝ) (ψk : 𝓢(Euc d, ℂ)),
      (∀ ξ, ψk ξ = 𝓕 (fun y : Euc d => ((k y : ℝ) : ℂ)) ξ) → ∀ y : Euc d,
      ((r26t8a_forceConv i k y : ℝ) : ℂ) = ∫ ξ : Euc d, r26t8a_f03_Mc c i ξ * ψk ξ *
        Complex.exp (2 * Real.pi * Complex.I * (inner ℝ y ξ : ℝ)) := by
    intro k ψk hψk y
    rw [(H i k).2 y]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [r26t8a_f03_Mc, hψk]
  have hsm : ContDiff ℝ ∞ (r26t8a_forceConv i h) := by
    have := HRS.MS.Ul.tail_conv hd (s := criticalS d) (HRS.MS.S82R.s82r_criticalS_pos hd1).le
      (HRS.MS.S82R.s82r_criticalS_lt hd1) h
    exact (EuclideanSpace.proj i).contDiff.comp this.2.1
  set T : Euc d → ℝ := r26t8a_forceConv i h with hT
  set Φ : ℝ → ℂ := fun l => ∫ ξ : Euc d, r26t8a_f03_Mc c i ξ * (((l ^ d)⁻¹ : ℝ) : ℂ) * ψ (l⁻¹ • ξ) *
      Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x ξ : ℝ)) with hΦ
  have hΦ1 := r26t8a_f03_phi_deriv (r26t8a_f03_Mc c i) (r26t8a_f03_Mc_meas c i).aestronglyMeasurable ψ x
    (d + 1) (r26t8a_f03_Mc_int hd c hc i)
  -- the other expression of `Φ`
  have hΦ2 : ∀ l : ℝ, 0 < l → Φ l = ((l ^ (1 - criticalS d) : ℝ) : ℂ) * ((T (l • x) : ℝ) : ℂ) := by
    intro l hl
    rw [hΦ]
    beta_reduce
    rw [r26t8a_f03_scale_int (r26t8a_f03_Mc c i) ψ (1 - criticalS d)
      (fun l hl η => r26t8a_f03_Mc_hom c i hl η) hl x, hT, rep h ψ hψ (l • x)]
  have hd1' : HasDerivAt (fun l : ℝ => l • x) x 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
  have hdT : DifferentiableAt ℝ T x := (hsm.differentiable (by simp)) x
  have hT1 : HasDerivAt (fun l : ℝ => T (l • x)) (fderiv ℝ T x x) 1 := by
    have hdT' : HasFDerivAt T (fderiv ℝ T x) ((1 : ℝ) • x) := by
      rw [one_smul]; exact hdT.hasFDerivAt
    exact hdT'.comp_hasDerivAt (1 : ℝ) hd1'
  have hp1 : HasDerivAt (fun l : ℝ => l ^ (1 - criticalS d)) ((1 - criticalS d) * (1 : ℝ) ^ (1 - criticalS d - 1)) 1 :=
    Real.hasDerivAt_rpow_const (Or.inl one_ne_zero)
  have hR := (hp1.ofReal_comp).mul hT1.ofReal_comp
  have hΦ3 : HasDerivAt Φ _ 1 := hR.congr_of_eventuallyEq (by
    filter_upwards [Ioi_mem_nhds (one_pos : (0:ℝ) < 1)] with l hl using hΦ2 l hl)
  have hun := hΦ1.unique hΦ3
  -- the datum `g`
  have hKg : ((r26t8a_forceConv i g x : ℝ) : ℂ) = ∫ ξ : Euc d, r26t8a_f03_Mc c i ξ *
      (-(d : ℂ) * ψ ξ - fderiv ℝ ψ ξ ξ) * Complex.exp (2 * Real.pi * Complex.I * (inner ℝ x ξ : ℝ)) := by
    rw [rep g ψg hψg x]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    beta_reduce
    rw [hψg, r26t8a_f03_fourier_euler h g hg ψ hψ ξ]
  rw [← hKg] at hun
  apply Complex.ofReal_injective
  simp only [one_smul, Real.one_rpow, mul_one, Complex.ofReal_one, one_mul] at hun
  unfold r26t8a_Euler
  push_cast at hun ⊢
  linear_combination (-1 : ℂ) * hun

end HRS.MS.R26T8A

end
