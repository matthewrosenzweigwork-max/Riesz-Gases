import HRS.MH.AdjointRdDefs
import HRS.MH.AdjointRdSpec
import HRS.MS.Ker1Aux4

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

/-!
# E3-R3 : `euc_nl_R3` (scouting-by-proof, PARTIAL)

Equation-level proof (real space, no Fourier analysis).  Write `theta = s+2-d in (0,2)`, `K = rieszKernel d s`
(`K(x) = c|x|^{-s}` up to the Riesz normalisation; `|K| ~ |x|^{-s}`, `|D^2 K| ~ |x|^{-s-2}`, locally integrable for `s<d`).
Write `w^ = advCutoff chi Psi tau c`, `Xi = w^ F` and `Theta = jets of w^ F`.

1.  Reduction.  The cell pairing of `eucNonlocal s M (w^ mu) F` against `partial^a F` is a finite sum (Leibniz for the
    tuple, `m` fixed) of pairings `int phi * partial_w (K * partial_u psi)` with `phi, psi` jets of `w^ F` of order `<= m`
    (and cutoff-commutator terms of lower order, same shape).  Each is bounded by Step 2 with `|u|,|w| <= 1`.
2.  Cell interpolation (`r3_core1`, PROVED here).  For `r > 0`, splitting `K = Kn + Kf` at scale `r`
    (`Kn = K - K*bump-free part` supported near `0`, `Kf` smooth, `Kf = 0` near `0` by `r3F1_zero_near`):
      |int phi * d_w (K * d_u psi)|
        <= (int |Kn|) (int (d_w phi)^2 + int (d_u psi)^2)/2 + (int |D^2 Kf|) (int phi^2 + int psi^2)/2   (Schur/AM-GM),
    with `int |Kn| = Cn r^{d-s} = Cn r^{2-theta}` and `int |D^2 Kf| = Cf r^{d-s-2} = Cf r^{-theta}`.
3.  Choice of `r`.  Summing over the finitely many cells `k in E` and jets of order `<= m`:
    `sum <= Cn r^{2-theta} * Dissip + Cf r^{-theta} * Energy`, so with `Cn r^{2-theta} = nu0/(8|E|)` i.e.
    `r^{-theta} = (Cn' nu0)^{-theta/(2-theta)}` one gets `kappa = nu0/(8|E|)` and `A = C(1 + nu0^{-theta/(2-theta)})`.
    (`1` accounts for the lower-order cutoff commutators.)

Status: Step 2 is fully proved (0 sorry).  Missing (see report): jets of `w^` up to order `m` (flow derivative bounds,
`C^{m+1}` flow already in `flow_inv_contDiff`), the LOWER first-order far-field pairing, the `eucNonlocal` to convolution /
tuple-Leibniz reduction (Step 1), cell bookkeeping over `E` and the choice of `r` (Step 3), and the corner `d = 1, s < 0`
(`r3_core1` needs `0 <= s`, via `ker1_E_bound`; the statement has no `0 <= s`).
-/

namespace HRS.MH.AdjointRdP
open HRS HRS.Whole HRS.MH.AdjointRd
variable {d : ℕ}

theorem r3_amgm (a b k : ℝ) :
    ENNReal.ofReal (|a|) * (ENNReal.ofReal |k| * ENNReal.ofReal |b|) ≤
      (ENNReal.ofReal |k| * ENNReal.ofReal (a ^ 2) + ENNReal.ofReal |k| * ENNReal.ofReal (b ^ 2)) / 2 := by
  have h : |a| * (|k| * |b|) ≤ (|k| * a ^ 2 + |k| * b ^ 2) / 2 := by
    nlinarith [abs_nonneg k, abs_nonneg a, abs_nonneg b, sq_abs a, sq_abs b,
      mul_nonneg (abs_nonneg k) (sq_nonneg (|a| - |b|))]
  have e1 : ENNReal.ofReal (|a|) * (ENNReal.ofReal |k| * ENNReal.ofReal |b|) =
      ENNReal.ofReal (|a| * (|k| * |b|)) := by
    rw [ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_mul (abs_nonneg _)]
  have e2 : (ENNReal.ofReal |k| * ENNReal.ofReal (a ^ 2) + ENNReal.ofReal |k| * ENNReal.ofReal (b ^ 2)) / 2 =
      ENNReal.ofReal ((|k| * a ^ 2 + |k| * b ^ 2) / 2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_add (by positivity) (by positivity),
      ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_mul (abs_nonneg _)]
    simp
  rw [e1, e2]
  exact ENNReal.ofReal_le_ofReal h

/-- Schur/AM-GM bound for a convolution pairing in `ℝ≥0∞`. -/
theorem r3_pair_lintegral {K A B : Euc d → ℝ} (hK : Measurable K) (hA : Measurable A)
    (hB : Measurable B) :
    ∫⁻ x, ENNReal.ofReal |A x| * ∫⁻ y, ENNReal.ofReal |K (x - y)| * ENNReal.ofReal |B y| ≤
      (∫⁻ h, ENNReal.ofReal |K h|) *
        ((∫⁻ x, ENNReal.ofReal (A x ^ 2)) + ∫⁻ y, ENNReal.ofReal (B y ^ 2)) / 2 := by
  set u : Euc d → ℝ≥0∞ := fun h => ENNReal.ofReal |K h| with hu
  set a : Euc d → ℝ≥0∞ := fun x => ENNReal.ofReal (A x ^ 2) with ha
  set b : Euc d → ℝ≥0∞ := fun y => ENNReal.ofReal (B y ^ 2) with hb
  have hum : Measurable u := (hK.abs).ennreal_ofReal
  have ham : Measurable a := ((hA.pow_const 2)).ennreal_ofReal
  have hbm : Measurable b := ((hB.pow_const 2)).ennreal_ofReal
  have h1 : ∀ x, ENNReal.ofReal |A x| * ∫⁻ y, ENNReal.ofReal |K (x - y)| * ENNReal.ofReal |B y| ≤
      ∫⁻ y, (u (x - y) * a x + u (x - y) * b y) / 2 := by
    intro x
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact lintegral_mono fun y => r3_amgm _ _ _
  refine (lintegral_mono h1).trans ?_
  have h2 : ∀ x, ∫⁻ y, (u (x - y) * a x + u (x - y) * b y) / 2 =
      ((∫⁻ h, u h) * a x + ∫⁻ y, u (x - y) * b y) / 2 := by
    intro x
    simp_rw [ENNReal.div_eq_inv_mul]
    rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 two_ne_zero),
      lintegral_add_left (by fun_prop), lintegral_mul_const _ (by fun_prop),
      lintegral_sub_left_eq_self u x]
  simp_rw [h2]
  have hmu2 : Measurable (fun p : Euc d × Euc d => u (p.1 - p.2) * b p.2) :=
    (hum.comp (measurable_fst.sub measurable_snd)).mul (hbm.comp measurable_snd)
  have h3 : ∫⁻ x, ∫⁻ y, u (x - y) * b y = (∫⁻ h, u h) * ∫⁻ y, b y := by
    rw [lintegral_lintegral_swap hmu2.aemeasurable]
    have : ∀ y, ∫⁻ x, u (x - y) * b y = (∫⁻ h, u h) * b y := by
      intro y
      have hm : Measurable (fun x : Euc d => u (x - y)) := hum.comp (measurable_id.sub_const y)
      rw [lintegral_mul_const _ hm]
      congr 1
      exact lintegral_sub_right_eq_self u y
    simp_rw [this]
    rw [lintegral_const_mul _ hbm]
  have h4 : ∫⁻ x, (((∫⁻ h, u h) * a x + ∫⁻ y, u (x - y) * b y) / 2) =
      (∫⁻ h, u h) * ((∫⁻ x, a x) + ∫⁻ y, b y) / 2 := by
    simp_rw [ENNReal.div_eq_inv_mul]
    rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 two_ne_zero),
      lintegral_add_left (ham.const_mul _), lintegral_const_mul _ ham, h3]
    ring
  exact h4.le

/-- Real form of the Schur/AM-GM bound: `|∫ A (K ⋆ B)| ≤ ½ ‖K‖₁ (‖A‖₂² + ‖B‖₂²)`. -/
theorem r3_pair_le {K A B : Euc d → ℝ} (hK : Measurable K) (hA : Measurable A)
    (hB : Measurable B) (hK1 : Integrable K) (hA2 : Integrable (fun x => A x ^ 2))
    (hB2 : Integrable (fun x => B x ^ 2)) :
    |∫ x, A x * ∫ y, K (x - y) * B y| ≤
      (∫ h, |K h|) * ((∫ x, A x ^ 2) + ∫ y, B y ^ 2) / 2 := by
  have key := r3_pair_lintegral hK hA hB
  have e1 : ∫⁻ h, ENNReal.ofReal |K h| = ENNReal.ofReal (∫ h, |K h|) :=
    (ofReal_integral_eq_lintegral_ofReal hK1.abs (Eventually.of_forall fun _ => abs_nonneg _)).symm
  have e2 : ∫⁻ x, ENNReal.ofReal (A x ^ 2) = ENNReal.ofReal (∫ x, A x ^ 2) :=
    (ofReal_integral_eq_lintegral_ofReal hA2 (Eventually.of_forall fun _ => sq_nonneg _)).symm
  have e3 : ∫⁻ x, ENNReal.ofReal (B x ^ 2) = ENNReal.ofReal (∫ x, B x ^ 2) :=
    (ofReal_integral_eq_lintegral_ofReal hB2 (Eventually.of_forall fun _ => sq_nonneg _)).symm
  rw [e1, e2, e3] at key
  have n1 : 0 ≤ ∫ h, |K h| := integral_nonneg fun _ => abs_nonneg _
  have n2 : 0 ≤ ∫ x, A x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have n3 : 0 ≤ ∫ x, B x ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hR : ENNReal.ofReal (∫ h, |K h|) * (ENNReal.ofReal (∫ x, A x ^ 2) + ENNReal.ofReal (∫ x, B x ^ 2)) / 2 =
      ENNReal.ofReal ((∫ h, |K h|) * ((∫ x, A x ^ 2) + ∫ y, B y ^ 2) / 2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_mul n1, ENNReal.ofReal_add n2 n3]
    simp
  rw [hR] at key
  have hle : ∫⁻ x, ‖A x * ∫ y, K (x - y) * B y‖ₑ ≤
      ∫⁻ x, ENNReal.ofReal |A x| * ∫⁻ y, ENNReal.ofReal |K (x - y)| * ENNReal.ofReal |B y| := by
    refine lintegral_mono fun x => ?_
    rw [enorm_mul, Real.enorm_eq_ofReal_abs]
    gcongr
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
    refine lintegral_congr fun y => ?_
    rw [enorm_mul, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
  have h2 := hle.trans key
  have h3 := norm_integral_le_lintegral_norm (μ := volume) (fun x => A x * ∫ y, K (x - y) * B y)
  rw [Real.norm_eq_abs] at h3
  refine h3.trans ?_
  have : (∫⁻ x, ENNReal.ofReal ‖A x * ∫ y, K (x - y) * B y‖) =
      ∫⁻ x, ‖A x * ∫ y, K (x - y) * B y‖ₑ := by
    refine lintegral_congr fun x => ?_
    rw [ofReal_norm_eq_enorm]
  rw [this]
  calc (∫⁻ x, ‖A x * ∫ y, K (x - y) * B y‖ₑ).toReal
      ≤ (ENNReal.ofReal ((∫ h, |K h|) * ((∫ x, A x ^ 2) + ∫ y, B y ^ 2) / 2)).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
    _ = _ := ENNReal.toReal_ofReal (by positivity)

open Convolution in
theorem r3_hasFDerivAt_conv {K Ξ : Euc d → ℝ} (hK : LocallyIntegrable K) (hΞ : ContDiff ℝ 1 Ξ)
    (hc : HasCompactSupport Ξ) (x : Euc d) :
    HasFDerivAt (fun x => ∫ y, K (x - y) * Ξ y)
      ((fderiv ℝ Ξ ⋆[(ContinuousLinearMap.mul ℝ ℝ).precompL (Euc d), volume] K) x) x := by
  have := hc.hasFDerivAt_convolution_left (ContinuousLinearMap.mul ℝ ℝ) hΞ hK x
  convert this using 1
  funext x
  simp only [convolution_def, ContinuousLinearMap.mul_apply']
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp [mul_comm]

open Convolution in
theorem r3_fderiv_conv_apply {K Ξ : Euc d → ℝ} (hK : LocallyIntegrable K) (hΞ : ContDiff ℝ 1 Ξ)
    (hc : HasCompactSupport Ξ) (x e : Euc d) :
    fderiv ℝ (fun x => ∫ y, K (x - y) * Ξ y) x e = ∫ y, K (x - y) * fderiv ℝ Ξ y e := by
  rw [(r3_hasFDerivAt_conv hK hΞ hc x).fderiv, convolution_def]
  have hint := (hc.fderiv ℝ).convolutionExists_left
    ((ContinuousLinearMap.mul ℝ ℝ).precompL (Euc d)) (hΞ.continuous_fderiv one_ne_zero) hK x
  rw [ContinuousLinearMap.integral_apply hint]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp [mul_comm]

/-- Integration by parts for `C¹` functions, one of which has compact support. -/
theorem r3_ibp_cs {f g : Euc d → ℝ} (v : Euc d) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hcf : HasCompactSupport f) :
    ∫ x, f x * fderiv ℝ g x v = -∫ x, fderiv ℝ f x v * g x := by
  have hf' : Continuous (fun x => fderiv ℝ f x v) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hg' : Continuous (fun x => fderiv ℝ g x v) :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact (hf'.mul hg.continuous).integrable_of_hasCompactSupport
      ((hcf.fderiv_apply ℝ v).mul_right)
  · exact (hf.continuous.mul hg').integrable_of_hasCompactSupport (hcf.mul_right)
  · exact (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport (hcf.mul_right)
  · exact fun x _ => (hf.differentiable one_ne_zero) x
  · exact fun x _ => (hg.differentiable one_ne_zero) x

theorem r3_sq_int {f : Euc d → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable (fun x => f x ^ 2) := by
  have : (fun x => f x ^ 2) = fun x => f x * f x := by funext x; ring
  rw [this]
  exact (hf.mul hf).integrable_of_hasCompactSupport hc.mul_right

open Convolution in
theorem r3_contDiff_conv {K Ξ : Euc d → ℝ} (hK : LocallyIntegrable K) {n : ℕ∞}
    (hΞ : ContDiff ℝ n Ξ) (hc : HasCompactSupport Ξ) :
    ContDiff ℝ n (fun x => ∫ y, K (x - y) * Ξ y) := by
  have := hc.contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℝ) hΞ hK
  convert this using 1
  funext x
  simp only [convolution_def, ContinuousLinearMap.mul_apply']
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp [mul_comm]

/-- Near-field pairing: `|∫ φ ∂_i (K ⋆ Θ)| ≤ ½ ‖K‖₁ (‖∂_iφ‖² + ‖Θ‖²)`. -/
theorem r3_near {K φ Θ : Euc d → ℝ} (hK : Measurable K) (hK1 : Integrable K)
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (hΘ : ContDiff ℝ 1 Θ)
    (hΘc : HasCompactSupport Θ) (v : Euc d) :
    |∫ x, φ x * fderiv ℝ (fun x => ∫ y, K (x - y) * Θ y) x v| ≤
      (∫ h, |K h|) * ((∫ x, (fderiv ℝ φ x v) ^ 2) + ∫ y, Θ y ^ 2) / 2 := by
  have hH : ContDiff ℝ 1 (fun x => ∫ y, K (x - y) * Θ y) :=
    r3_contDiff_conv hK1.locallyIntegrable (n := 1) hΘ hΘc
  rw [r3_ibp_cs v hφ hH hφc, abs_neg]
  have hA : Continuous (fun x => fderiv ℝ φ x v) :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  exact r3_pair_le hK hA.measurable hΘ.continuous.measurable hK1
    (r3_sq_int hA (hφc.fderiv_apply ℝ v)) (r3_sq_int hΘ.continuous hΘc)

/-- Integration by parts for `C¹` functions, the second one with compact support. -/
theorem r3_ibp_cs' {f g : Euc d → ℝ} (v : Euc d) (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hcg : HasCompactSupport g) :
    ∫ x, f x * fderiv ℝ g x v = -∫ x, fderiv ℝ f x v * g x := by
  have hf' : Continuous (fun x => fderiv ℝ f x v) :=
    (hf.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hg' : Continuous (fun x => fderiv ℝ g x v) :=
    (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact (hf'.mul hg.continuous).integrable_of_hasCompactSupport hcg.mul_left
  · exact (hf.continuous.mul hg').integrable_of_hasCompactSupport ((hcg.fderiv_apply ℝ v).mul_left)
  · exact (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hcg.mul_left
  · exact fun x _ => (hf.differentiable one_ne_zero) x
  · exact fun x _ => (hg.differentiable one_ne_zero) x

theorem r3_fderiv_reflect {K : Euc d → ℝ} (hK : ContDiff ℝ 1 K) (x v y : Euc d) :
    fderiv ℝ (fun y => K (x - y)) y v = -fderiv ℝ K (x - y) v := by
  have h1 : HasFDerivAt (fun y => K (x - y)) ((fderiv ℝ K (x - y)).comp (-(ContinuousLinearMap.id ℝ _))) y :=
    ((hK.differentiable one_ne_zero (x - y)).hasFDerivAt).comp y ((hasFDerivAt_id y).const_sub x)
  rw [h1.fderiv]
  simp

/-- Integration by parts in the convolution variable. -/
theorem r3_ibp_conv {K Ξ : Euc d → ℝ} (hK : ContDiff ℝ 1 K) (hΞ : ContDiff ℝ 1 Ξ)
    (hc : HasCompactSupport Ξ) (x v : Euc d) :
    ∫ y, K (x - y) * fderiv ℝ Ξ y v = ∫ y, fderiv ℝ K (x - y) v * Ξ y := by
  have hf : ContDiff ℝ 1 (fun y => K (x - y)) := hK.comp (contDiff_const.sub contDiff_id)
  have := r3_ibp_cs' v hf hΞ hc
  simp only [r3_fderiv_reflect hK x v] at this
  rw [this, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp

/-- Far-field pairing for a smooth kernel with integrable second derivative:
`∫ φ ∂_w (K ⋆ ∂_u ψ) = ∫ φ ((∂_u ∂_w K) ⋆ ψ)`, bounded by `½ ‖∂_u∂_w K‖₁ (‖φ‖² + ‖ψ‖²)`. -/
theorem r3_far {Kf φ ψ : Euc d → ℝ} (u w : Euc d) (hKf : ContDiff ℝ 2 Kf)
    (hK2m : Measurable (fun h => fderiv ℝ (fun h' => fderiv ℝ Kf h' w) h u))
    (hK2 : Integrable (fun h => fderiv ℝ (fun h' => fderiv ℝ Kf h' w) h u))
    (hφ : Continuous φ) (hφc : HasCompactSupport φ) (hψ : ContDiff ℝ 2 ψ)
    (hψc : HasCompactSupport ψ) :
    |∫ x, φ x * fderiv ℝ (fun x => ∫ y, Kf (x - y) * fderiv ℝ ψ y u) x w| ≤
      (∫ h, |fderiv ℝ (fun h' => fderiv ℝ Kf h' w) h u|) * ((∫ x, φ x ^ 2) + ∫ y, ψ y ^ 2) / 2 := by
  have hψ1 : ContDiff ℝ 1 (fun y => fderiv ℝ ψ y u) :=
    ((hψ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const)
  have hψ1c : HasCompactSupport (fun y => fderiv ℝ ψ y u) := hψc.fderiv_apply ℝ u
  have hKf1 : ContDiff ℝ 1 Kf := hKf.of_le (by norm_num)
  have hKw : ContDiff ℝ 1 (fun h' => fderiv ℝ Kf h' w) :=
    ((hKf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const)
  have h1 : ∀ x, fderiv ℝ (fun x => ∫ y, Kf (x - y) * fderiv ℝ ψ y u) x w =
      ∫ y, fderiv ℝ (fun h' => fderiv ℝ Kf h' w) (x - y) u * ψ y := by
    intro x
    rw [r3_fderiv_conv_apply hKf.continuous.locallyIntegrable hψ1 hψ1c x w,
      r3_ibp_conv hKf1 hψ1 hψ1c x w, r3_ibp_conv hKw (hψ.of_le (by norm_num)) hψc x u]
  simp_rw [h1]
  exact r3_pair_le hK2m hφ.measurable (hψ.continuous.measurable) hK2
    (r3_sq_int hφ hφc) (r3_sq_int hψ.continuous hψc)

/-! ### Kernel splitting at scale `r` -/

/-- Cutoff bump: `1` on `B̄(0,1)`, `0` off `B(0,2)`. -/
def r3Bump (d : ℕ) : ContDiffBump (0 : Euc d) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The value of the profile of the Riesz kernel at radius `r`. -/
def r3gp (s r : ℝ) : ℝ := if s = 0 then -Real.log r else r ^ (-s)

/-- The profile constant at radius `1`. -/
def r3c1 (s : ℝ) : ℝ := if s = 0 then 0 else 1

theorem r3_scale_id (s : ℝ) {r : ℝ} (hr : 0 < r) {h : Euc d} (hh : h ≠ 0) :
    rieszKernel d s h - r3gp s r = r ^ (-s) * (rieszKernel d s (r⁻¹ • h) - r3c1 s) := by
  have hn : 0 < ‖h‖ := norm_pos_iff.mpr hh
  have hnr : ‖r⁻¹ • h‖ = r⁻¹ * ‖h‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hr)]
  unfold rieszKernel r3gp r3c1
  rw [hnr]
  by_cases hs : s = 0
  · simp only [hs, if_true, neg_zero, Real.rpow_zero, one_mul]
    rw [Real.log_mul (inv_pos.2 hr).ne' hn.ne', Real.log_inv]
    ring
  · simp only [hs, if_false]
    have hp : 0 < r ^ (-s) := Real.rpow_pos_of_pos hr _
    rw [Real.mul_rpow (inv_pos.2 hr).le hn.le, Real.inv_rpow hr.le]
    field_simp

theorem r3_meas_g (s : ℝ) : Measurable (rieszKernel d s) := by
  unfold rieszKernel
  by_cases hs : s = 0
  · simp only [hs, if_true]; fun_prop
  · simp only [hs, if_false]; fun_prop

theorem r3Bump_contDiff : ContDiff ℝ ∞ (r3Bump d) := (r3Bump d).contDiff

theorem r3Bump_one {k : Euc d} (hk : ‖k‖ ≤ 1) : r3Bump d k = 1 :=
  (r3Bump d).one_of_mem_closedBall (by simpa [r3Bump] using hk)

theorem r3Bump_zero {k : Euc d} (hk : 2 ≤ ‖k‖) : r3Bump d k = 0 :=
  (r3Bump d).zero_of_le_dist (by simpa [r3Bump] using hk)

theorem r3Bump_mem (k : Euc d) : r3Bump d k ∈ Icc (0 : ℝ) 1 := ⟨(r3Bump d).nonneg, (r3Bump d).le_one⟩

theorem r3Bump_hasCompactSupport : HasCompactSupport (r3Bump d) := (r3Bump d).hasCompactSupport

/-- Unit-scale near kernel. -/
def r3N1 (d : ℕ) (s : ℝ) (k : Euc d) : ℝ := (rieszKernel d s k - r3c1 s) * r3Bump d k

/-- Unit-scale far kernel. -/
def r3F1 (d : ℕ) (s : ℝ) (k : Euc d) : ℝ := (rieszKernel d s k - r3c1 s) * (1 - r3Bump d k)

theorem r3N1_integrable {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    Integrable (r3N1 d s) := by
  have hg := rieszKernel_locallyIntegrable (d := d) hs0 hsd
  have hg' : LocallyIntegrable (fun k => rieszKernel d s k - r3c1 s) volume :=
    hg.sub (continuous_const.locallyIntegrable)
  exact hg'.integrable_smul_right_of_hasCompactSupport (r3Bump_contDiff.continuous)
    r3Bump_hasCompactSupport

/-- Near kernel at scale `r`. -/
def r3Kn (d : ℕ) (s r : ℝ) (h : Euc d) : ℝ := (rieszKernel d s h - r3gp s r) * r3Bump d (r⁻¹ • h)

/-- Far kernel at scale `r`. -/
def r3Kf (d : ℕ) (s r : ℝ) (h : Euc d) : ℝ := (rieszKernel d s h - r3gp s r) * (1 - r3Bump d (r⁻¹ • h))

theorem r3_Kn_add_Kf (s r : ℝ) (h : Euc d) :
    r3Kn d s r h + r3Kf d s r h = rieszKernel d s h - r3gp s r := by
  unfold r3Kn r3Kf; ring

theorem r3_ae_ne_zero (hd : 1 ≤ d) : ∀ᵐ h : Euc d ∂(volume : Measure (Euc d)), h ≠ 0 := by
  haveI : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  simpa using (Set.countable_singleton (0 : Euc d)).ae_notMem (volume : Measure (Euc d))

theorem r3Kn_ae (hd : 1 ≤ d) (s : ℝ) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ h : Euc d ∂(volume : Measure (Euc d)), r3Kn d s r h = r ^ (-s) * r3N1 d s (r⁻¹ • h) := by
  filter_upwards [r3_ae_ne_zero hd] with h hh
  unfold r3Kn r3N1
  rw [← mul_assoc, ← r3_scale_id s hr hh]

theorem r3Kn_integrable (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {r : ℝ} (hr : 0 < r) :
    Integrable (r3Kn d s r) := by
  have h1 : Integrable (fun h : Euc d => r3N1 d s (r⁻¹ • h)) :=
    (integrable_comp_smul_iff volume (r3N1 d s) (inv_ne_zero hr.ne')).2 (r3N1_integrable hs0 hsd)
  refine (h1.const_mul (r ^ (-s))).congr ?_
  filter_upwards [r3Kn_ae hd s hr] with h hh using hh.symm

theorem r3Kn_meas (s r : ℝ) : Measurable (r3Kn d s r) := by
  unfold r3Kn
  exact ((r3_meas_g s).sub measurable_const).mul
    (r3Bump_contDiff.continuous.measurable.comp (measurable_const_smul _))

theorem r3Kn_l1 (hd : 1 ≤ d) (s : ℝ) {r : ℝ} (hr : 0 < r) :
    ∫ h, |r3Kn d s r h| = (∫ k, |r3N1 d s k|) * r ^ ((d : ℝ) - s) := by
  have h1 : ∫ h, |r3Kn d s r h| = ∫ h, r ^ (-s) * |r3N1 d s (r⁻¹ • h)| := by
    refine integral_congr_ae ?_
    filter_upwards [r3Kn_ae hd s hr] with h hh
    rw [hh, abs_mul, abs_of_pos (Real.rpow_pos_of_pos hr _)]
  rw [h1, integral_const_mul, Measure.integral_comp_inv_smul volume (fun k => |r3N1 d s k|) r]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul, abs_pow, abs_of_pos hr]
  rw [Real.rpow_sub hr, Real.rpow_natCast, Real.rpow_neg hr.le]
  field_simp

theorem r3F1_zero_near {s : ℝ} {k : Euc d} (hk : ‖k‖ ≤ 1) : r3F1 d s k = 0 := by
  unfold r3F1; rw [r3Bump_one hk]; simp

theorem r3F1_contDiff {s : ℝ} : ContDiff ℝ ∞ (r3F1 d s) := by
  rw [contDiff_iff_contDiffAt]
  intro k
  by_cases hk : k = 0
  · subst hk
    have : r3F1 d s =ᶠ[𝓝 (0 : Euc d)] fun _ => (0 : ℝ) := by
      filter_upwards [Metric.ball_mem_nhds (0 : Euc d) one_pos] with y hy
      exact r3F1_zero_near (by simpa using (mem_ball_zero_iff.mp hy).le)
    exact contDiffAt_const.congr_of_eventuallyEq this
  · have hg : ContDiffAt ℝ ∞ (rieszKernel d s) k :=
      rieszKernel_contDiffOn.contDiffAt (isOpen_ne.mem_nhds hk)
    exact (hg.sub contDiffAt_const).mul (contDiffAt_const.sub r3Bump_contDiff.contDiffAt)

theorem r3Kf_eq (s : ℝ) {r : ℝ} (hr : 0 < r) (h : Euc d) :
    r3Kf d s r h = r ^ (-s) * r3F1 d s (r⁻¹ • h) := by
  by_cases hh : h = 0
  · subst hh
    unfold r3Kf r3F1
    rw [smul_zero, r3Bump_one (by simp)]; simp
  · unfold r3Kf r3F1
    rw [← mul_assoc, ← r3_scale_id s hr hh]

theorem r3Kf_contDiff (s : ℝ) {r : ℝ} (hr : 0 < r) : ContDiff ℝ ∞ (r3Kf d s r) := by
  have : r3Kf d s r = fun h => r ^ (-s) * r3F1 d s (r⁻¹ • h) := funext (r3Kf_eq s hr)
  rw [this]
  exact contDiff_const.mul (r3F1_contDiff.comp (contDiff_const_smul _))

theorem r3_le_infty (n : ℕ) : ((n : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast le_top

theorem r3F1_D2_eq {s : ℝ} {k : Euc d} (hk : 2 < ‖k‖) :
    iteratedFDeriv ℝ 2 (r3F1 d s) k = iteratedFDeriv ℝ 2 (rieszKernel d s) k := by
  have hk0 : k ≠ 0 := by
    intro h; rw [h] at hk; simp at hk; linarith
  have hev : r3F1 d s =ᶠ[𝓝 k] fun y => rieszKernel d s y + (-r3c1 s) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hk] with y hy
    unfold r3F1
    rw [r3Bump_zero hy.le]; ring
  rw [(hev.iteratedFDeriv ℝ 2).eq_of_nhds]
  have hg : ContDiffAt ℝ 2 (rieszKernel d s) k :=
    (rieszKernel_contDiffOn.contDiffAt (isOpen_ne.mem_nhds hk0)).of_le (by exact_mod_cast r3_le_infty 2)
  have := iteratedFDeriv_add_apply (i := 2) (f := rieszKernel d s) (g := fun _ : Euc d => -r3c1 s)
    hg contDiffAt_const (x := k)
  rw [show (fun y => rieszKernel d s y + (-r3c1 s)) = rieszKernel d s + fun _ => -r3c1 s from rfl,
    this, iteratedFDeriv_const_of_ne (by omega)]
  simp

theorem r3F1_D2_integrable {s : ℝ} (hs0 : 0 ≤ s) (hs2 : (d : ℝ) < s + 2) :
    Integrable (fun k => ‖iteratedFDeriv ℝ 2 (r3F1 d s) k‖) := by
  obtain ⟨C, hC0, hC⟩ := HRS.MS.Ker1.ker1_E_bound (d := d) hs0 2 (by positivity)
  have hcont : Continuous (iteratedFDeriv ℝ 2 (r3F1 d s)) :=
    r3F1_contDiff.continuous_iteratedFDeriv (m := 2) (by exact_mod_cast r3_le_infty 2)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Euc d) 2).exists_bound_of_continuousOn
    hcont.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0 (by simp))
  have hint : Integrable (fun k : Euc d => (1 + ‖k‖) ^ (-(s + 2))) := by
    have := integrable_one_add_norm (E := Euc d) (μ := volume) (r := s + 2) (by simpa using hs2)
    exact this
  refine Integrable.mono' (hint.const_mul (max (M * 3 ^ (s + 2)) (C * (3 / 2) ^ (s + 2))))
    (hcont.norm.aestronglyMeasurable) (Eventually.of_forall fun k => ?_)
  have hk1 : 0 < 1 + ‖k‖ := by positivity
  have hpow : 0 < (1 + ‖k‖) ^ (-(s + 2)) := Real.rpow_pos_of_pos hk1 _
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  by_cases hk : ‖k‖ ≤ 2
  · have h1 := hM k (by simpa using hk)
    have h3 : (3 : ℝ) ^ (-(s + 2)) ≤ (1 + ‖k‖) ^ (-(s + 2)) :=
      Real.rpow_le_rpow_of_nonpos hk1 (by linarith) (by linarith)
    have h4 : (3 : ℝ) ^ (s + 2) * 3 ^ (-(s + 2)) = 1 := by
      rw [← Real.rpow_add (by norm_num)]; simp
    calc ‖iteratedFDeriv ℝ 2 (r3F1 d s) k‖ ≤ M := h1
      _ = M * 3 ^ (s + 2) * 3 ^ (-(s + 2)) := by rw [mul_assoc, h4, mul_one]
      _ ≤ M * 3 ^ (s + 2) * (1 + ‖k‖) ^ (-(s + 2)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hpow.le
  · have hk := not_le.mp hk
    have hk0 : k ≠ 0 := by
      intro h; rw [h] at hk; simp at hk; linarith
    rw [r3F1_D2_eq hk]
    have h1 := hC k hk0
    have hn : 0 < ‖k‖ := norm_pos_iff.mpr hk0
    have h2 : ‖k‖ ^ (-s - ((2 : ℕ) : ℝ)) ≤ (3 / 2) ^ (s + 2) * (1 + ‖k‖) ^ (-(s + 2)) := by
      have e : -s - ((2 : ℕ) : ℝ) = -(s + 2) := by push_cast; ring
      rw [e]
      have hle : (2 / 3) * (1 + ‖k‖) ≤ ‖k‖ := by linarith
      have := Real.rpow_le_rpow_of_nonpos (by positivity) hle (show -(s + 2) ≤ 0 by linarith)
      rw [Real.mul_rpow (by norm_num) hk1.le] at this
      have h5 : ((2 : ℝ) / 3) ^ (-(s + 2)) = (3 / 2) ^ (s + 2) := by
        rw [Real.rpow_neg (by norm_num), ← Real.inv_rpow (by norm_num)]; norm_num
      rw [h5] at this
      exact this
    calc ‖iteratedFDeriv ℝ 2 (rieszKernel d s) k‖ ≤ C * ‖k‖ ^ (-s - ((2 : ℕ) : ℝ)) := h1
      _ ≤ C * ((3 / 2) ^ (s + 2) * (1 + ‖k‖) ^ (-(s + 2))) := mul_le_mul_of_nonneg_left h2 hC0
      _ = C * (3 / 2) ^ (s + 2) * (1 + ‖k‖) ^ (-(s + 2)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hpow.le

theorem r3Kf_D2_scaling (s : ℝ) {r : ℝ} (hr : 0 < r) (h : Euc d) :
    iteratedFDeriv ℝ 2 (r3Kf d s r) h =
      (r ^ (-s) * (r⁻¹) ^ 2) • iteratedFDeriv ℝ 2 (r3F1 d s) (r⁻¹ • h) := by
  have e : r3Kf d s r = fun y => r ^ (-s) • (fun y => r3F1 d s (r⁻¹ • y)) y := by
    funext y; rw [r3Kf_eq s hr]; rfl
  have hc : ContDiffAt ℝ 2 (fun y : Euc d => r3F1 d s (r⁻¹ • y)) h :=
    ((r3F1_contDiff.comp (contDiff_const_smul (r⁻¹))).contDiffAt).of_le
      (by exact_mod_cast r3_le_infty 2)
  rw [e]
  refine (iteratedFDeriv_const_smul_apply (a := r ^ (-s)) hc).trans ?_
  rw [HRS.MS.Ker1.ker1_iteratedFDeriv_comp_smul _ (inv_ne_zero hr.ne'), smul_smul]

theorem r3Kf_D2_l1 (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs2 : (d : ℝ) < s + 2) {r : ℝ} (hr : 0 < r) :
    Integrable (fun h => ‖iteratedFDeriv ℝ 2 (r3Kf d s r) h‖) ∧
    ∫ h, ‖iteratedFDeriv ℝ 2 (r3Kf d s r) h‖ =
      (∫ k, ‖iteratedFDeriv ℝ 2 (r3F1 d s) k‖) * r ^ ((d : ℝ) - s - 2) := by
  have hI := r3F1_D2_integrable (d := d) hs0 hs2
  have e : (fun h => ‖iteratedFDeriv ℝ 2 (r3Kf d s r) h‖) =
      fun h => (r ^ (-s) * (r⁻¹) ^ 2) * ‖iteratedFDeriv ℝ 2 (r3F1 d s) (r⁻¹ • h)‖ := by
    funext h
    rw [r3Kf_D2_scaling s hr, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by have := Real.rpow_pos_of_pos hr (-s); positivity)]
  rw [e]
  refine ⟨((integrable_comp_smul_iff volume (fun k => ‖iteratedFDeriv ℝ 2 (r3F1 d s) k‖)
    (inv_ne_zero hr.ne')).2 hI).const_mul _, ?_⟩
  rw [integral_const_mul, Measure.integral_comp_inv_smul volume
    (fun k => ‖iteratedFDeriv ℝ 2 (r3F1 d s) k‖) r]
  simp only [finrank_euclideanSpace_fin, smul_eq_mul, abs_pow, abs_of_pos hr]
  have : r ^ ((d : ℝ) - s - 2) = r ^ (-s) * (r⁻¹) ^ 2 * r ^ d := by
    rw [Real.rpow_sub hr, Real.rpow_sub hr, Real.rpow_two, Real.rpow_natCast, Real.rpow_neg hr.le]
    field_simp
  rw [this]; ring

open Convolution in
theorem r3_conv_integrable {K Ξ : Euc d → ℝ} (hK : LocallyIntegrable K) (hΞ : Continuous Ξ)
    (hc : HasCompactSupport Ξ) (x : Euc d) : Integrable (fun y => K (x - y) * Ξ y) := by
  have := hc.convolutionExists_left (ContinuousLinearMap.mul ℝ ℝ) hΞ hK x
  refine this.congr (Eventually.of_forall fun y => ?_)
  simp [mul_comm]

/-- If `g = Kn + Kf + c` then the convolution derivative splits. -/
theorem r3_fderiv_split {g Kn Kf : Euc d → ℝ} {c : ℝ} {Ξ : Euc d → ℝ}
    (hg : ∀ h, g h = Kn h + Kf h + c) (hKn : LocallyIntegrable Kn) (hKf : LocallyIntegrable Kf)
    (hΞ : ContDiff ℝ 1 Ξ) (hc : HasCompactSupport Ξ) (x w : Euc d) :
    fderiv ℝ (fun x => ∫ y, g (x - y) * Ξ y) x w =
      fderiv ℝ (fun x => ∫ y, Kn (x - y) * Ξ y) x w +
        fderiv ℝ (fun x => ∫ y, Kf (x - y) * Ξ y) x w := by
  have hG : (fun x => ∫ y, g (x - y) * Ξ y) =
      fun x => (∫ y, Kn (x - y) * Ξ y) + (∫ y, Kf (x - y) * Ξ y) + c * ∫ y, Ξ y := by
    funext x
    have h1 := r3_conv_integrable hKn hΞ.continuous hc x
    have h2 := r3_conv_integrable hKf hΞ.continuous hc x
    have h3 : Integrable Ξ := hΞ.continuous.integrable_of_hasCompactSupport hc
    simp_rw [hg, add_mul]
    rw [integral_add (f := fun y => Kn (x - y) * Ξ y + Kf (x - y) * Ξ y) (g := fun y => c * Ξ y)
      (h1.add h2) (h3.const_mul c), integral_add h1 h2, integral_const_mul]
  rw [hG]
  have d1 : DifferentiableAt ℝ (fun x => ∫ y, Kn (x - y) * Ξ y) x :=
    (r3_hasFDerivAt_conv hKn hΞ hc x).differentiableAt
  have d2 : DifferentiableAt ℝ (fun x => ∫ y, Kf (x - y) * Ξ y) x :=
    (r3_hasFDerivAt_conv hKf hΞ hc x).differentiableAt
  rw [fderiv_add_const, fderiv_fun_add d1 d2]
  rfl

theorem r3_D_eq {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (u w h : Euc d) :
    fderiv ℝ (fun h' => fderiv ℝ f h' w) h u = iteratedFDeriv ℝ 2 f h ![u, w] := by
  have hd1 : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable one_ne_zero
  rw [iteratedFDeriv_two_apply]
  have := fderiv_clm_apply (c := fderiv ℝ f) (u := fun _ : Euc d => w) (x := h) (hd1 h)
    (differentiableAt_const w)
  rw [this]
  simp

theorem r3_D_bound {f : Euc d → ℝ} (u w h : Euc d) (hu : ‖u‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    |iteratedFDeriv ℝ 2 f h ![u, w]| ≤ ‖iteratedFDeriv ℝ 2 f h‖ := by
  rw [← Real.norm_eq_abs]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  have h0 : 0 ≤ ‖iteratedFDeriv ℝ 2 f h‖ := norm_nonneg _
  calc ‖iteratedFDeriv ℝ 2 f h‖ * (‖u‖ * ‖w‖) ≤ ‖iteratedFDeriv ℝ 2 f h‖ * (1 * 1) := by
        gcongr
    _ = _ := by ring

/-- **Core pairing estimate (cell interpolation, real-space form).**  For the Riesz kernel `g` with
`0 ≤ s < d < s + 2` and every scale `r > 0`:
`|∫ φ ∂_w (g ⋆ ∂_u ψ)| ≤ ½ Cn r^{d-s} (‖∂_wφ‖² + ‖∂_uψ‖²) + ½ Cf r^{d-s-2} (‖φ‖² + ‖ψ‖²)`,
with `d - s = 2 - θ` and `d - s - 2 = -θ`, `θ = s + 2 - d`. -/
theorem r3_core1 (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hs2 : (d : ℝ) < s + 2) :
    ∃ Cn Cf : ℝ, 0 ≤ Cn ∧ 0 ≤ Cf ∧ ∀ r : ℝ, 0 < r → ∀ (φ ψ : Euc d → ℝ), ContDiff ℝ 1 φ →
      HasCompactSupport φ → ContDiff ℝ 2 ψ → HasCompactSupport ψ → ∀ u w : Euc d, ‖u‖ ≤ 1 → ‖w‖ ≤ 1 →
      |∫ x, φ x * fderiv ℝ (fun x => ∫ y, rieszKernel d s (x - y) * fderiv ℝ ψ y u) x w| ≤
        (Cn * r ^ ((d : ℝ) - s)) * ((∫ x, (fderiv ℝ φ x w) ^ 2) + ∫ y, (fderiv ℝ ψ y u) ^ 2) / 2 +
        (Cf * r ^ ((d : ℝ) - s - 2)) * ((∫ x, φ x ^ 2) + ∫ y, ψ y ^ 2) / 2 := by
  refine ⟨∫ k, |r3N1 d s k|, ∫ k, ‖iteratedFDeriv ℝ 2 (r3F1 d s) k‖,
    integral_nonneg fun _ => abs_nonneg _, integral_nonneg fun _ => norm_nonneg _, ?_⟩
  intro r hr φ ψ hφ hφc hψ hψc u w hu hw
  have hψ1 : ContDiff ℝ 1 (fun y => fderiv ℝ ψ y u) :=
    ((hψ.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const)
  have hΞc : HasCompactSupport (fun y => fderiv ℝ ψ y u) := hψc.fderiv_apply ℝ u
  have hKn1 := r3Kn_integrable hd hs0 hsd hr
  have hKfc := r3Kf_contDiff (d := d) s hr
  have hKf2 : ContDiff ℝ 2 (r3Kf d s r) := hKfc.of_le (by exact_mod_cast r3_le_infty 2)
  have hsplit := r3_fderiv_split (g := rieszKernel d s) (Kn := r3Kn d s r) (Kf := r3Kf d s r)
    (c := r3gp s r) (Ξ := fun y => fderiv ℝ ψ y u)
    (fun h => by have := r3_Kn_add_Kf s r h; linarith) hKn1.locallyIntegrable
    hKfc.continuous.locallyIntegrable hψ1 hΞc
  simp_rw [hsplit]
  -- continuity of the two derivative integrands
  have hA : Continuous (fun x => fderiv ℝ (fun x => ∫ y, r3Kn d s r (x - y) * fderiv ℝ ψ y u) x w) :=
    ((r3_contDiff_conv hKn1.locallyIntegrable (n := 1) hψ1 hΞc).continuous_fderiv one_ne_zero).clm_apply
      continuous_const
  have hB : Continuous (fun x => fderiv ℝ (fun x => ∫ y, r3Kf d s r (x - y) * fderiv ℝ ψ y u) x w) :=
    ((r3_contDiff_conv hKfc.continuous.locallyIntegrable (n := 1) hψ1 hΞc).continuous_fderiv
      one_ne_zero).clm_apply continuous_const
  have hφ0 : Continuous φ := hφ.continuous
  have hI1 : Integrable (fun x => φ x *
      fderiv ℝ (fun x => ∫ y, r3Kn d s r (x - y) * fderiv ℝ ψ y u) x w) :=
    (hφ0.mul hA).integrable_of_hasCompactSupport hφc.mul_right
  have hI2 : Integrable (fun x => φ x *
      fderiv ℝ (fun x => ∫ y, r3Kf d s r (x - y) * fderiv ℝ ψ y u) x w) :=
    (hφ0.mul hB).integrable_of_hasCompactSupport hφc.mul_right
  have hsum : ∫ x, φ x * (fderiv ℝ (fun x => ∫ y, r3Kn d s r (x - y) * fderiv ℝ ψ y u) x w +
        fderiv ℝ (fun x => ∫ y, r3Kf d s r (x - y) * fderiv ℝ ψ y u) x w) =
      (∫ x, φ x * fderiv ℝ (fun x => ∫ y, r3Kn d s r (x - y) * fderiv ℝ ψ y u) x w) +
        ∫ x, φ x * fderiv ℝ (fun x => ∫ y, r3Kf d s r (x - y) * fderiv ℝ ψ y u) x w := by
    simp_rw [mul_add]; exact integral_add hI1 hI2
  rw [hsum]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · have h1 := r3_near (r3Kn_meas s r) hKn1 hφ hφc hψ1 hΞc w
    rw [r3Kn_l1 hd s hr] at h1
    exact h1
  · have hD : ∀ h, fderiv ℝ (fun h' => fderiv ℝ (r3Kf d s r) h' w) h u =
        iteratedFDeriv ℝ 2 (r3Kf d s r) h ![u, w] := fun h => r3_D_eq hKf2 u w h
    obtain ⟨hI, hE⟩ := r3Kf_D2_l1 hd hs0 hs2 hr
    have hcont : Continuous (iteratedFDeriv ℝ 2 (r3Kf d s r)) :=
      hKfc.continuous_iteratedFDeriv (m := 2) (by exact_mod_cast r3_le_infty 2)
    have hDc : Continuous (fun h => fderiv ℝ (fun h' => fderiv ℝ (r3Kf d s r) h' w) h u) := by
      simp_rw [hD]
      exact (continuous_eval_const (![u, w])).comp hcont
    have hDint : Integrable (fun h => fderiv ℝ (fun h' => fderiv ℝ (r3Kf d s r) h' w) h u) := by
      refine Integrable.mono' hI hDc.aestronglyMeasurable (Eventually.of_forall fun h => ?_)
      rw [hD h, Real.norm_eq_abs]
      exact r3_D_bound u w h hu hw
    have h2 := r3_far (Kf := r3Kf d s r) u w hKf2 hDc.measurable hDint hφ0 hφc hψ hψc
    refine h2.trans ?_
    have hle : ∫ h, |fderiv ℝ (fun h' => fderiv ℝ (r3Kf d s r) h' w) h u| ≤
        ∫ h, ‖iteratedFDeriv ℝ 2 (r3Kf d s r) h‖ := by
      refine integral_mono hDint.abs hI fun h => ?_
      rw [hD h]
      exact r3_D_bound u w h hu hw
    rw [hE] at hle
    have h0 : 0 ≤ (∫ x, φ x ^ 2) + ∫ y, ψ y ^ 2 :=
      add_nonneg (integral_nonneg fun _ => sq_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
    have := mul_le_mul_of_nonneg_right hle h0
    linarith

theorem euc_nl_R3 (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hs2 : (d : ℝ) - 2 < s) (m : ℕ) (hm : 1 ≤ m)
    (MB Λ Cb T : ℝ) (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh) :
    ∃ (E : Finset (Fin d → ℤ)) (C : ℝ), CoversBall8 E ∧ 0 ≤ C ∧ ∀ ν₀ : ℝ, 0 < ν₀ →
      EucNlBound s m Λ Cb T χ χh E (C * (1 + ν₀ ^ (-(PDE.thetaOrder d s / (2 - PDE.thetaOrder d s)))))
        (ν₀ / (8 * E.card)) (fun M => PDE.MatBound MB M) := by
  sorry

end HRS.MH.AdjointRdP
