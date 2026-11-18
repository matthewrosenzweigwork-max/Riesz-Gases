import HRS.MS.ThCorrSobAux2
import HRS.MS.PsdHeatAux2

/-!
# TC-3: local Sobolev gain for the Riesz / logarithmic kernel (S4.4 chain)

Namespace `HRS.MS.Tc3`.  Fourier convention `û(ξ) = ∫ e^{-2πi⟨x,ξ⟩} u(x) dx`; Sobolev norms are those of
`HRS.PDE.ToolboxRd` (`MemSobolev t`, `sobolevNormSq t = ∫ (1 + 4π²|ξ|²)^t |û|²`) and
`HRS.Whole.sobolevNormE` (`⊤` outside `H^t`), the ones used by `HRS.MS.SobMul`.

## Statements (`0 ≤ s < d`, `θ ∈ C_c^∞(ℝ^d)`, `α = d - s`, kernel `θ g` with `g = rieszKernel d s`)

* generic (`ThCorrSobAux1`): `tc3_sobolev_gain`.  `G ∈ L¹` measurable with `‖Ĝ(ξ)‖ ≤ A ⟨ξ⟩^{-α}`
  (`⟨ξ⟩² = wt ξ = 1 + 4π²|ξ|²`) and `f ∈ H^t` give `G * f ∈ H^{t+α}` and
  `‖G * f‖²_{H^{t+α}} ≤ A² ‖f‖²_{H^t}`, for every real `t` (`G * f = HRS.Whole.convFun G f`; the
  proof establishes the convolution theorem `\widehat{G * f} = Ĝ f̂`, `tc3_fourierL2_conv`).
  `tc3_sobolevNormE_gain` is the same in extended-norm form (`A > 0`, no hypothesis on `f`).
* Fourier decay of the localised kernel: `tc3_riesz_loc_decay` (`0 < s < d`, `ThCorrSobAux2`) and
  `tc3_log_loc_decay` (`s = 0`, this file): `‖\widehat{θ g}(ξ)‖ ≤ A ⟨ξ⟩^{-(d-s)}`.
  `0 < s < d`: heat-kernel subordination `|x|^{-s} = ∫_0^∞ a_{d,s} t^{(d-s)/2-1} p_t(x) dt`
  (`HRS.MS.Psd.psd3_cov`, `riesz_heat`), Fubini, the product formula `\widehat{T h} = T̂ ⋆ ĥ`,
  the Gaussian transform, the Gamma integral and a Peetre-type bound.
  `s = 0`: `-log|x| = q_1(x) + F(|x|²) - c₀` (`HRS.MS.Psd.riesz_log_heat_split`, `τ = 1`) with `F`
  smooth (`tc3_F_contDiff_top`, differentiation under the integral), so `θ(F(|·|²) - c₀)` is
  `C_c^∞` with Schwartz Fourier transform, and the singular part `q_1 = ½ ∫_{u>1} e^{-u|x|²} du/u`
  is the heat-kernel integral with the weight `½ (4π)^{d/2} t^{d/2-1} 1_{t<1/4}`
  (`tc3_cwlog`, change of variables `tc3_cov`), whose transform is bounded by the same Fubini
  scheme (`tc3_Ghat_enorm_gen`).
* Main results of this file:
  `tc3_riesz_loc_sobolev_gain`: `∃ C > 0, ∀ t f, f ∈ H^t → θ g * f ∈ H^{t+d-s}` and
  `‖θ g * f‖²_{H^{t+d-s}} ≤ C² ‖f‖²_{H^t}`;
  `tc3_riesz_loc_sobolevNormE_gain`: `sobolevNormE (t + (d-s)) (θ g * f) ≤ C * sobolevNormE t f`.
  The constant `C` depends on `d, s, θ` only (not on `t`).  For the logarithmic kernel the gain is
  the full `α = d` (not only `α = 1`).

Remarks.  "`θ = 1` near `0`" is not needed for the gain (only for `g - θ g` being smooth).  `MemSobolev t`
includes `f ∈ L²`, so for `t < 0` the statement concerns `L²` functions with the `H^t` weight.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal ComplexConjugate FourierTransform Convolution ContDiff

namespace HRS.MS.Tc3
open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.Whole HRS.Whole.Q34 HRS.MS.SobMul HRS.MS.Psd

variable {d : ℕ}

/-! ### The smooth part of the logarithm -/

theorem tc3_abs_exp_sub_one (x : ℝ) : |Real.exp x - 1| ≤ |x| * Real.exp |x| := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx, abs_of_nonneg (by linarith [Real.add_one_le_exp x])]
    have h1 := Real.add_one_le_exp (-x)
    have h2 : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos x]
  · rw [abs_of_nonpos hx, abs_of_nonpos (by linarith [Real.exp_le_one_iff.2 hx])]
    have h1 := Real.add_one_le_exp x
    have : 0 < Real.exp (-x) := Real.exp_pos _
    have h3 : 1 ≤ Real.exp (-x) := Real.one_le_exp (by linarith)
    nlinarith

theorem tc3_psi_bound (v : ℝ) {u : ℝ} (hu : 0 < u) (hu1 : u ≤ 1) :
    |(Real.exp (-(v * u)) - Real.exp (-u)) / u| ≤ |v - 1| * Real.exp |v - 1| := by
  rw [abs_div, abs_of_pos hu, div_le_iff₀ hu]
  have e : Real.exp (-(v * u)) - Real.exp (-u) = Real.exp (-u) * (Real.exp (-((v - 1) * u)) - 1) := by
    rw [mul_sub, ← Real.exp_add]; ring_nf
  rw [e, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 := tc3_abs_exp_sub_one (-((v - 1) * u))
  have h2 : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have h3 : |-((v - 1) * u)| ≤ |v - 1| := by
    rw [abs_neg, abs_mul, abs_of_pos hu]
    nlinarith [abs_nonneg (v - 1)]
  have h4 : |-((v - 1) * u)| * Real.exp |-((v - 1) * u)| ≤ |v - 1| * u * Real.exp |v - 1| := by
    rw [abs_neg, abs_mul, abs_of_pos hu]
    have : Real.exp (|v - 1| * u) ≤ Real.exp |v - 1| := Real.exp_le_exp.2 (by nlinarith [abs_nonneg (v - 1)])
    exact mul_le_mul_of_nonneg_left this (by positivity)
  calc Real.exp (-u) * |Real.exp (-((v - 1) * u)) - 1|
      ≤ 1 * |Real.exp (-((v - 1) * u)) - 1| := by gcongr
    _ ≤ |-((v - 1) * u)| * Real.exp |-((v - 1) * u)| := by rw [one_mul]; exact h1
    _ ≤ |v - 1| * u * Real.exp |v - 1| := h4
    _ = |v - 1| * Real.exp |v - 1| * u := by ring

theorem tc3_exp_bound (m : ℕ) (v x u : ℝ) (hu : u ∈ Ioc (0 : ℝ) 1) (hx : x ∈ Metric.ball v 1) :
    ‖(-u) ^ m * Real.exp (-(x * u))‖ ≤ Real.exp (|v| + 1) := by
  rw [Metric.mem_ball, Real.dist_eq] at hx
  have h1 : |(-u) ^ m| ≤ 1 := by
    rw [abs_pow, abs_neg, abs_of_pos hu.1]
    exact pow_le_one₀ hu.1.le hu.2
  have h2 : Real.exp (-(x * u)) ≤ Real.exp (|v| + 1) := by
    refine Real.exp_le_exp.2 ?_
    have : |x| ≤ |v| + 1 := by
      have := abs_sub_abs_le_abs_sub x v
      linarith
    have h3 : -(x * u) ≤ |x| * u := by
      have := neg_abs_le x
      nlinarith [hu.1]
    nlinarith [hu.1, hu.2, abs_nonneg x, abs_nonneg v]
  rw [norm_mul, Real.norm_eq_abs, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc |(-u) ^ m| * Real.exp (-(x * u)) ≤ 1 * Real.exp (|v| + 1) := by gcongr
    _ = _ := one_mul _

/-- `φ_k(v) = ∫_0^1 (-u)^k e^{-vu} du` -/
def tc3_phi (k : ℕ) (v : ℝ) : ℝ := ∫ u in Ioc (0 : ℝ) 1, (-u) ^ k * Real.exp (-(v * u))

theorem tc3_phi_hasDerivAt (k : ℕ) (v : ℝ) :
    HasDerivAt (tc3_phi k) (tc3_phi (k + 1) v) v := by
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1))
    (F := fun x u => (-u) ^ k * Real.exp (-(x * u)))
    (F' := fun x u => (-u) ^ (k + 1) * Real.exp (-(x * u))) (x₀ := v)
    (bound := fun _ => Real.exp (|v| + 1)) (s := Metric.ball v 1) (Metric.ball_mem_nhds v one_pos)
    (Filter.Eventually.of_forall fun x => (by fun_prop : Continuous
      fun u : ℝ => (-u) ^ k * Real.exp (-(x * u))).aestronglyMeasurable)
    (Integrable.mono' (integrable_const (Real.exp (|v| + 1)))
      (by fun_prop : Continuous fun u : ℝ => (-u) ^ k * Real.exp (-(v * u))).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu =>
        tc3_exp_bound k v v u hu (Metric.mem_ball_self one_pos))))
    (by fun_prop : Continuous fun u : ℝ => (-u) ^ (k + 1) * Real.exp (-(v * u))).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu x hx =>
      tc3_exp_bound (k + 1) v x u hu hx))
    (integrable_const _)
    (Filter.Eventually.of_forall fun u x _ => by
      have h1 : HasDerivAt (fun y : ℝ => -(y * u)) (-u) x := by
        simpa using ((hasDerivAt_id x).mul_const u).fun_neg
      exact (h1.exp.const_mul ((-u) ^ k)).congr_deriv (by ring))
  exact key.2

theorem tc3_phi_contDiff : ∀ (n k : ℕ), ContDiff ℝ (n : WithTop ℕ∞) (tc3_phi k)
  | 0, k => by
      rw [Nat.cast_zero, contDiff_zero]
      exact continuous_iff_continuousAt.2 fun v => (tc3_phi_hasDerivAt k v).continuousAt
  | n + 1, k => by
      rw [Nat.cast_succ, contDiff_succ_iff_deriv]
      refine ⟨fun v => (tc3_phi_hasDerivAt k v).differentiableAt, by simp, ?_⟩
      have : deriv (tc3_phi k) = tc3_phi (k + 1) := funext fun v => (tc3_phi_hasDerivAt k v).deriv
      rw [this]
      exact tc3_phi_contDiff n (k + 1)

/-- the smooth part `F(v) = ½ ∫_0^1 (e^{-vu} - e^{-u}) du/u` of `-log |x|` -/
def tc3_F (v : ℝ) : ℝ := (1 / 2) * ∫ u in Ioc (0 : ℝ) 1, (Real.exp (-(v * u)) - Real.exp (-u)) / u

theorem tc3_F_hasDerivAt (v : ℝ) : HasDerivAt tc3_F (-(1 / 2) * tc3_phi 0 v) v := by
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure ℝ).restrict (Ioc (0 : ℝ) 1))
    (F := fun x u => (Real.exp (-(x * u)) - Real.exp (-u)) / u)
    (F' := fun x u => -(Real.exp (-(x * u)))) (x₀ := v)
    (bound := fun _ => Real.exp (|v| + 1)) (s := Metric.ball v 1) (Metric.ball_mem_nhds v one_pos)
    (Filter.Eventually.of_forall fun x =>
      (by fun_prop : Measurable fun u : ℝ => (Real.exp (-(x * u)) - Real.exp (-u)) / u).aestronglyMeasurable)
    (Integrable.mono' (integrable_const (|v - 1| * Real.exp |v - 1|))
      (by fun_prop : Measurable fun u : ℝ =>
        (Real.exp (-(v * u)) - Real.exp (-u)) / u).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu => by
        rw [Real.norm_eq_abs]; exact tc3_psi_bound v hu.1 hu.2)))
    (by fun_prop : Continuous fun u : ℝ => -(Real.exp (-(v * u)))).aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu x hx => by
      have := tc3_exp_bound 0 v x u hu hx
      simpa using this))
    (integrable_const _)
    ((ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu x _ => by
      have h1 : HasDerivAt (fun y : ℝ => -(y * u)) (-u) x := by
        simpa using ((hasDerivAt_id x).mul_const u).fun_neg
      have h2 := ((h1.exp.sub_const (Real.exp (-u))).div_const u)
      refine h2.congr_deriv ?_
      have : u ≠ 0 := hu.1.ne'
      field_simp))
  have h3 := key.2.const_mul (1 / 2 : ℝ)
  refine h3.congr_deriv ?_
  unfold tc3_phi
  simp only [pow_zero, one_mul, integral_neg]
  ring

theorem tc3_F_contDiff : ∀ n : ℕ, ContDiff ℝ (n : WithTop ℕ∞) tc3_F
  | 0 => by
      rw [Nat.cast_zero, contDiff_zero]
      exact continuous_iff_continuousAt.2 fun v => (tc3_F_hasDerivAt v).continuousAt
  | n + 1 => by
      rw [Nat.cast_succ, contDiff_succ_iff_deriv]
      refine ⟨fun v => (tc3_F_hasDerivAt v).differentiableAt, by simp, ?_⟩
      have : deriv tc3_F = fun v => -(1 / 2) * tc3_phi 0 v :=
        funext fun v => (tc3_F_hasDerivAt v).deriv
      rw [this]
      exact contDiff_const.mul (tc3_phi_contDiff n 0)

theorem tc3_F_contDiff_top : ContDiff ℝ ∞ tc3_F := contDiff_infty.2 tc3_F_contDiff

/-- Fourier decay of a `C_c^∞` function: `‖Ŝ(ξ)‖ ≤ A ⟨ξ⟩^{-γ}` for every `γ > 0`. -/
theorem tc3_smooth_decay {S : Euc d → ℝ} (hS : ContDiff ℝ ∞ S) (hc : HasCompactSupport S)
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ A : ℝ, 0 < A ∧ ∀ ξ : Euc d, ‖tc3_Ghat S ξ‖ ≤ A * wt ξ ^ (-γ / 2) := by
  set T : SchwartzMap (Euc d) ℂ :=
    (hc.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp hS) with hT
  have hTa : ∀ x, T x = ((S x : ℝ) : ℂ) := fun x => rfl
  obtain ⟨⟨K1, hK1⟩, _⟩ := tc3_schwartz_weight (𝓕 T : SchwartzMap (Euc d) ℂ) hγ.le
  have hK10 : 0 ≤ K1 := le_trans (by positivity) (hK1 0)
  refine ⟨(K1 + 1) * (2 * Real.pi) ^ γ, by positivity, fun ξ => ?_⟩
  have e : tc3_Ghat S ξ = (𝓕 T : SchwartzMap (Euc d) ℂ) ξ := by
    unfold tc3_Ghat
    rw [SchwartzMap.fourier_coe]
    rfl
  rw [e]
  have h1 := hK1 ξ
  have hA : 0 < (1 + ‖ξ‖) ^ γ := by positivity
  have h2 : ‖(𝓕 T : SchwartzMap (Euc d) ℂ) ξ‖ ≤ K1 * (1 + ‖ξ‖) ^ (-γ) := by
    rw [Real.rpow_neg (by positivity), ← div_eq_mul_inv, le_div_iff₀ hA]
    exact h1
  refine h2.trans ?_
  have h3 := tc3_peetre_wt hγ ξ
  calc K1 * (1 + ‖ξ‖) ^ (-γ) ≤ (K1 + 1) * (1 + ‖ξ‖) ^ (-γ) := by gcongr; linarith
    _ ≤ (K1 + 1) * ((2 * Real.pi) ^ γ * wt ξ ^ (-γ / 2)) := by gcongr
    _ = _ := by ring

/-! ### The singular part of the logarithm -/

/-- change of variables `t = (4u)⁻¹`, `(1,∞) → (0,1/4)` -/
theorem tc3_cov (g : ℝ → ℝ) :
    (IntegrableOn g (Ioo (0 : ℝ) (1 / 4)) ↔
      IntegrableOn (fun u : ℝ => |(-4 / (4 * u) ^ 2)| • g ((4 * u)⁻¹)) (Ioi (1 : ℝ))) ∧
    ∫ t in Ioo (0 : ℝ) (1 / 4), g t =
      ∫ u in Ioi (1 : ℝ), |(-4 / (4 * u) ^ 2)| • g ((4 * u)⁻¹) := by
  have hder : ∀ l ∈ Ioi (1 : ℝ),
      HasDerivWithinAt (fun l : ℝ => (4 * l)⁻¹) (-4 / (4 * l) ^ 2) (Ioi (1 : ℝ)) l := by
    intro l hl
    have hl' : (1 : ℝ) < l := hl
    have h : HasDerivAt (fun l : ℝ => 4 * l) 4 l := by
      simpa using (hasDerivAt_id l).const_mul (4 : ℝ)
    exact (h.inv (by positivity)).hasDerivWithinAt
  have hinj : InjOn (fun l : ℝ => (4 * l)⁻¹) (Ioi (1 : ℝ)) := by
    intro a ha b hb hab
    have ha' : (1 : ℝ) < a := ha
    have hb' : (1 : ℝ) < b := hb
    simp only [inv_inj] at hab
    linarith
  have himg : (fun l : ℝ => (4 * l)⁻¹) '' Ioi (1 : ℝ) = Ioo (0 : ℝ) (1 / 4) := by
    ext t
    constructor
    · rintro ⟨l, hl, rfl⟩
      have hl' : (1 : ℝ) < l := hl
      refine ⟨inv_pos.2 (by positivity), ?_⟩
      rw [one_div]
      exact inv_strictAnti₀ (by norm_num) (by linarith)
    · intro ht
      refine ⟨(4 * t)⁻¹, ?_, ?_⟩
      · have h0 : 0 < t := ht.1
        have h1 : t < 1 / 4 := ht.2
        show (1 : ℝ) < (4 * t)⁻¹
        rw [lt_inv_comm₀ one_pos (by positivity)]
        linarith
      · have h0 : 0 < t := ht.1
        simp only
        field_simp
  have hI := integrableOn_image_iff_integrableOn_abs_deriv_smul measurableSet_Ioi hder hinj g
  have hV := integral_image_eq_integral_abs_deriv_smul measurableSet_Ioi hder hinj g
  rw [himg] at hI hV
  exact ⟨hI, hV⟩

/-- the heat-kernel weight of the singular part `q_1` of `-log`: `½ (4π)^{d/2} t^{d/2-1} 1_{t<1/4}` -/
def tc3_cwlog (d : ℕ) : ℝ → ℝ :=
  (Iio (1 / 4 : ℝ)).indicator fun t => (1 / 2) * (4 * Real.pi) ^ ((d : ℝ) / 2) * t ^ ((d : ℝ) / 2 - 1)

theorem tc3_cwlog_nonneg (d : ℕ) {t : ℝ} (ht : 0 < t) : 0 ≤ tc3_cwlog d t := by
  unfold tc3_cwlog
  by_cases h : t < 1 / 4
  · rw [Set.indicator_of_mem (show t ∈ Iio (1 / 4 : ℝ) from h)]
    positivity
  · rw [Set.indicator_of_notMem (show t ∉ Iio (1 / 4 : ℝ) from h)]

theorem tc3_cwlog_meas (d : ℕ) : Measurable (tc3_cwlog d) :=
  (measurable_const.mul (measurable_id.pow_const _)).indicator measurableSet_Iio

theorem tc3_cwlog_heat (d : ℕ) (x : Euc d) {t : ℝ} (ht : 0 < t) :
    tc3_cwlog d t * heatKerE d t x =
      (Iio (1 / 4 : ℝ)).indicator (fun t => (1 / 2) * t⁻¹ * Real.exp (-(‖x‖ ^ 2 / (4 * t)))) t := by
  unfold tc3_cwlog
  by_cases h : t < 1 / 4
  · rw [Set.indicator_of_mem (show t ∈ Iio (1 / 4 : ℝ) from h),
      Set.indicator_of_mem (show t ∈ Iio (1 / 4 : ℝ) from h)]
    unfold heatKerE
    have e1 : (4 * Real.pi * t) ^ (-(d : ℝ) / 2) = (4 * Real.pi) ^ (-(d : ℝ) / 2) * t ^ (-(d : ℝ) / 2) :=
      Real.mul_rpow (by positivity) ht.le
    have e2 : (4 * Real.pi) ^ ((d : ℝ) / 2) * (4 * Real.pi) ^ (-(d : ℝ) / 2) = 1 := by
      rw [← Real.rpow_add (by positivity)]
      have : (d : ℝ) / 2 + -(d : ℝ) / 2 = 0 := by ring
      rw [this, Real.rpow_zero]
    have e3 : t ^ ((d : ℝ) / 2 - 1) * t ^ (-(d : ℝ) / 2) = t⁻¹ := by
      rw [← Real.rpow_add ht, ← Real.rpow_neg_one]
      congr 1; ring
    calc (1 / 2 * (4 * Real.pi) ^ ((d : ℝ) / 2) * t ^ ((d : ℝ) / 2 - 1)) *
          ((4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-‖x‖ ^ 2 / (4 * t)))
        = (1 / 2) * ((4 * Real.pi) ^ ((d : ℝ) / 2) * (4 * Real.pi) ^ (-(d : ℝ) / 2)) *
            (t ^ ((d : ℝ) / 2 - 1) * t ^ (-(d : ℝ) / 2)) * Real.exp (-‖x‖ ^ 2 / (4 * t)) := by
          rw [e1]; ring
      _ = _ := by rw [e2, e3, neg_div]; ring
  · rw [Set.indicator_of_notMem (show t ∉ Iio (1 / 4 : ℝ) from h),
      Set.indicator_of_notMem (show t ∉ Iio (1 / 4 : ℝ) from h)]
    simp

theorem tc3_logQ_rep {x : Euc d} (hx : x ≠ 0) :
    qTauLog d 1 x = ∫ t in Ioi (0 : ℝ), tc3_cwlog d t * heatKerE d t x := by
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have e1 : ∫ t in Ioi (0 : ℝ), tc3_cwlog d t * heatKerE d t x =
      ∫ t in Ioo (0 : ℝ) (1 / 4), (1 / 2) * t⁻¹ * Real.exp (-(‖x‖ ^ 2 / (4 * t))) := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t ht => tc3_cwlog_heat d x ht),
      setIntegral_indicator measurableSet_Iio, Set.Ioi_inter_Iio]
  rw [e1, (tc3_cov _).2]
  unfold qTauLog
  rw [one_div_one, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
  have hu' : (1 : ℝ) < u := hu
  have hu0 : 0 < u := by linarith
  simp only [smul_eq_mul]
  have e5 : |(-4 / (4 * u) ^ 2)| = 4 / (4 * u) ^ 2 := by
    rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 4), abs_of_pos (by positivity)]
  rw [e5, inv_inv]
  have e6 : ‖x‖ ^ 2 / (4 * (4 * u)⁻¹) = ‖x‖ ^ 2 * u := by field_simp
  rw [e6]
  field_simp

theorem tc3_integrableOn_indicator_Iio {f : ℝ → ℝ} (h : IntegrableOn f (Ioo (0 : ℝ) (1 / 4))) :
    IntegrableOn ((Iio (1 / 4 : ℝ)).indicator f) (Ioi (0 : ℝ)) := by
  have h1 : IntegrableOn f (Iio (1 / 4 : ℝ)) (volume.restrict (Ioi (0 : ℝ))) := by
    unfold IntegrableOn at h ⊢
    rw [Measure.restrict_restrict measurableSet_Iio, Set.Iio_inter_Ioi]
    exact h
  exact (integrable_indicator_iff measurableSet_Iio).2 h1

theorem tc3_cwlog_integrableOn (d : ℕ) (hd : 0 < d) : IntegrableOn (tc3_cwlog d) (Ioi (0 : ℝ)) := by
  unfold tc3_cwlog
  refine tc3_integrableOn_indicator_Iio (Integrable.const_mul ?_ _)
  refine (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num)).2 ?_
  have : (0 : ℝ) < d := by exact_mod_cast hd
  linarith

theorem tc3_logQ_integrableOn {x : Euc d} (hx : x ≠ 0) :
    IntegrableOn (fun t : ℝ => tc3_cwlog d t * heatKerE d t x) (Ioi (0 : ℝ)) := by
  have hn : 0 < ‖x‖ := norm_pos_iff.2 hx
  have h1 : IntegrableOn (fun t : ℝ => (1 / 2) * t⁻¹ * Real.exp (-(‖x‖ ^ 2 / (4 * t))))
      (Ioo (0 : ℝ) (1 / 4)) := by
    rw [(tc3_cov _).1]
    have h := psd3_tail_integrableOn (a := ‖x‖ ^ 2) (by positivity) (τ := 1) one_pos
    rw [one_div_one] at h
    have h2 : IntegrableOn (fun u : ℝ => (1 / 2) * (Real.exp (-(‖x‖ ^ 2 * u)) / u)) (Ioi (1 : ℝ)) :=
      h.const_mul (1 / 2 : ℝ)
    refine IntegrableOn.congr_fun h2 (fun u hu => ?_) measurableSet_Ioi
    have hu' : (1 : ℝ) < u := hu
    have hu0 : 0 < u := by linarith
    simp only [smul_eq_mul]
    have e5 : |(-4 / (4 * u) ^ 2)| = 4 / (4 * u) ^ 2 := by
      rw [abs_div, abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 4), abs_of_pos (by positivity)]
    rw [e5, inv_inv]
    have e6 : ‖x‖ ^ 2 / (4 * (4 * u)⁻¹) = ‖x‖ ^ 2 * u := by field_simp
    rw [e6]
    field_simp
  exact (tc3_integrableOn_indicator_Iio h1).congr_fun (fun t ht => (tc3_cwlog_heat d x ht).symm)
    measurableSet_Ioi

theorem tc3_log_weight_bound (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ w : Euc d, w ≠ 0 →
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (tc3_cwlog d t) *
        ENNReal.ofReal (Real.exp (-((4 * Real.pi ^ 2 * ‖w‖ ^ 2) * t))) ≤
          ENNReal.ofReal (C * (1 + ‖w‖) ^ (-(d : ℝ))) := by
  set β : ℝ := (d : ℝ) / 2 with hβdef
  have hβ : 0 < β := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    rw [hβdef]; positivity
  set c1 : ℝ := (1 / 2) * (4 * Real.pi) ^ β with hc1
  have hc10 : 0 < c1 := by rw [hc1]; positivity
  set Mc : ℝ := ∫ t in Ioi (0 : ℝ), tc3_cwlog d t with hMc
  have hMc0 : 0 ≤ Mc := setIntegral_nonneg measurableSet_Ioi fun t ht => tc3_cwlog_nonneg d ht
  set M2 : ℝ := c1 * (Real.Gamma β * (4 * Real.pi ^ 2) ^ (-β)) with hM2
  have hM20 : 0 ≤ M2 := by
    rw [hM2]; have := Real.Gamma_pos_of_pos hβ; positivity
  set C : ℝ := (2 : ℝ) ^ (d : ℝ) * (Mc + M2 + 1) with hC
  have hC0 : 0 < C := by rw [hC]; positivity
  refine ⟨C, hC0, fun w hw => ?_⟩
  have hn : 0 < ‖w‖ := norm_pos_iff.2 hw
  have hr : 0 < 4 * Real.pi ^ 2 * ‖w‖ ^ 2 := by positivity
  -- bound (i)
  have h1 : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (tc3_cwlog d t) *
      ENNReal.ofReal (Real.exp (-((4 * Real.pi ^ 2 * ‖w‖ ^ 2) * t))) ≤ ENNReal.ofReal Mc := by
    calc _ ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (tc3_cwlog d t) := by
          refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
          have ht' : 0 < t := ht
          calc ENNReal.ofReal (tc3_cwlog d t) *
                ENNReal.ofReal (Real.exp (-((4 * Real.pi ^ 2 * ‖w‖ ^ 2) * t)))
              ≤ ENNReal.ofReal (tc3_cwlog d t) * 1 := by
                gcongr
                exact ENNReal.ofReal_le_one.2 (Real.exp_le_one_iff.2 (by nlinarith))
            _ = _ := mul_one _
      _ = ENNReal.ofReal Mc := by
          rw [hMc]
          exact (ofReal_integral_eq_lintegral_ofReal (tc3_cwlog_integrableOn d hd)
            ((ae_restrict_iff' measurableSet_Ioi).2
              (Filter.Eventually.of_forall fun t ht => tc3_cwlog_nonneg d ht))).symm
  -- bound (ii)
  have hcw_le : ∀ t : ℝ, 0 < t → tc3_cwlog d t ≤ c1 * t ^ (β - 1) := by
    intro t ht
    unfold tc3_cwlog
    by_cases h : t < 1 / 4
    · rw [Set.indicator_of_mem (show t ∈ Iio (1 / 4 : ℝ) from h)]
    · rw [Set.indicator_of_notMem (show t ∉ Iio (1 / 4 : ℝ) from h)]
      positivity
  have h2 : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (tc3_cwlog d t) *
      ENNReal.ofReal (Real.exp (-((4 * Real.pi ^ 2 * ‖w‖ ^ 2) * t))) ≤
        ENNReal.ofReal (M2 * ‖w‖ ^ (-(d : ℝ))) := by
    calc _ ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (c1 * t ^ (β - 1)) *
          ENNReal.ofReal (Real.exp (-((4 * Real.pi ^ 2 * ‖w‖ ^ 2) * t))) := by
          refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
          gcongr
          exact hcw_le t ht
      _ = ENNReal.ofReal (c1 * ((1 / (4 * Real.pi ^ 2 * ‖w‖ ^ 2)) ^ β * Real.Gamma β)) :=
          tc3_t_lintegral hβ hc10.le hr
      _ = ENNReal.ofReal (M2 * ‖w‖ ^ (-(d : ℝ))) := by
          congr 1
          have hp : 0 < 4 * Real.pi ^ 2 := by positivity
          have e1 : (1 / (4 * Real.pi ^ 2 * ‖w‖ ^ 2)) ^ β =
              (4 * Real.pi ^ 2) ^ (-β) * ‖w‖ ^ (-(d : ℝ)) := by
            rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity),
              Real.mul_rpow hp.le (by positivity)]
            congr 1
            rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
            congr 1
            rw [hβdef]; push_cast; ring
          rw [e1, hM2]
          ring
  -- combine
  have hpow : ∀ x : ℝ, 0 < x → ∀ y : ℝ, (x * 2) ^ y = x ^ y * 2 ^ y := fun x hx y =>
    Real.mul_rpow hx.le (by norm_num)
  by_cases hn1 : ‖w‖ ≤ 1
  · refine h1.trans (ENNReal.ofReal_le_ofReal ?_)
    have h3 : (2 : ℝ) ^ (-(d : ℝ)) ≤ (1 + ‖w‖) ^ (-(d : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)])
    have h4 : (2 : ℝ) ^ (d : ℝ) * (2 : ℝ) ^ (-(d : ℝ)) = 1 := by
      rw [← Real.rpow_add (by norm_num)]; simp
    have h5 : Mc ≤ C * (2 : ℝ) ^ (-(d : ℝ)) := by
      rw [hC, mul_assoc, mul_comm (Mc + M2 + 1), ← mul_assoc, h4, one_mul]
      linarith
    calc Mc ≤ C * (2 : ℝ) ^ (-(d : ℝ)) := h5
      _ ≤ C * (1 + ‖w‖) ^ (-(d : ℝ)) := by gcongr
  · push_neg at hn1
    refine h2.trans (ENNReal.ofReal_le_ofReal ?_)
    have h3 : (2 * ‖w‖) ^ (-(d : ℝ)) ≤ (1 + ‖w‖) ^ (-(d : ℝ)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)])
    have h4 : (2 : ℝ) ^ (d : ℝ) * (2 : ℝ) ^ (-(d : ℝ)) = 1 := by
      rw [← Real.rpow_add (by norm_num)]; simp
    have h5 : (2 * ‖w‖) ^ (-(d : ℝ)) = (2 : ℝ) ^ (-(d : ℝ)) * ‖w‖ ^ (-(d : ℝ)) :=
      Real.mul_rpow (by norm_num) hn.le
    have hwp : 0 < ‖w‖ ^ (-(d : ℝ)) := Real.rpow_pos_of_pos hn _
    calc M2 * ‖w‖ ^ (-(d : ℝ)) ≤ C * ((2 : ℝ) ^ (-(d : ℝ)) * ‖w‖ ^ (-(d : ℝ))) := by
          have hC2 : C * (2 : ℝ) ^ (-(d : ℝ)) = Mc + M2 + 1 := by
            rw [hC, mul_assoc, mul_comm (Mc + M2 + 1), ← mul_assoc, h4, one_mul]
          rw [← mul_assoc, hC2]
          nlinarith
      _ = C * (2 * ‖w‖) ^ (-(d : ℝ)) := by rw [h5]
      _ ≤ C * (1 + ‖w‖) ^ (-(d : ℝ)) := by gcongr

theorem tc3_logQ_decay {θ : Euc d → ℝ} (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    (hd : 0 < d) :
    ∃ A : ℝ, 0 < A ∧ ∀ ξ : Euc d,
      ‖tc3_Ghat (fun x => θ x * qTauLog d 1 x) ξ‖ ≤ A * wt ξ ^ (-(d : ℝ) / 2) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have : Nontrivial (Euc d) := by
    rw [← Module.finrank_pos_iff (R := ℝ)]; simpa using hd
  obtain ⟨C, hC, hw⟩ := tc3_log_weight_bound (d := d) hd
  set a : SchwartzMap (Euc d) ℂ := 𝓕 (sobmul_T θ hθ hc) with ha
  obtain ⟨⟨K1, hK1⟩, hint⟩ := tc3_schwartz_weight a (γ := (d : ℝ)) hdR.le
  set W : ℝ := ∫ η, ‖a η‖ * (1 + ‖η‖) ^ (d : ℝ) with hW
  have hW0 : 0 ≤ W := integral_nonneg fun η => by positivity
  have hx0 : ∀ᵐ x ∂(volume : Measure (Euc d)), x ≠ 0 := by
    rw [ae_iff]
    simpa using measure_singleton (μ := (volume : Measure (Euc d))) (0 : Euc d)
  obtain ⟨Bθ, hBθ⟩ := hθ.continuous.bounded_above_of_compact_support hc
  have hG : Integrable (fun x => θ x * qTauLog d 1 x) volume :=
    (qTauLog_integrable_integral (d := d) hd one_pos).1.bdd_mul
      hθ.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hBθ)
  refine ⟨(C * W + 1) * (2 * Real.pi) ^ (d : ℝ), by positivity, fun ξ => ?_⟩
  have h1 := tc3_Ghat_enorm_gen hθ hc (tc3_cwlog_meas d) (fun t ht => tc3_cwlog_nonneg d ht)
    (K := qTauLog d 1) (by filter_upwards [hx0] with x hx; exact tc3_logQ_rep hx)
    (by filter_upwards [hx0] with x hx; exact tc3_logQ_integrableOn hx) hG ξ
  have hne : ∀ᵐ η ∂(volume : Measure (Euc d)), η ≠ ξ := by
    rw [ae_iff]
    simpa using measure_singleton (μ := (volume : Measure (Euc d))) ξ
  have h2 : ∫⁻ η : Euc d, ‖a η‖ₑ * ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (tc3_cwlog d t) *
      ENNReal.ofReal (Real.exp (-((4 * Real.pi ^ 2 * ‖ξ - η‖ ^ 2) * t))) ≤
        ENNReal.ofReal (C * (1 + ‖ξ‖) ^ (-(d : ℝ)) * W) := by
    calc _ ≤ ∫⁻ η : Euc d, ENNReal.ofReal (C * (1 + ‖ξ‖) ^ (-(d : ℝ)) *
            (‖a η‖ * (1 + ‖η‖) ^ (d : ℝ))) := by
          refine lintegral_mono_ae ?_
          filter_upwards [hne] with η hη
          have hz : ξ - η ≠ 0 := sub_ne_zero.2 (Ne.symm hη)
          refine (mul_le_mul_right (hw (ξ - η) hz) _).trans ?_
          rw [← ofReal_norm, ← ENNReal.ofReal_mul (norm_nonneg _)]
          refine ENNReal.ofReal_le_ofReal ?_
          have hP : 1 + ‖ξ‖ ≤ (1 + ‖η‖) * (1 + ‖ξ - η‖) := by
            have h1 : ‖ξ‖ ≤ ‖η‖ + ‖ξ - η‖ := by
              have := norm_add_le η (ξ - η)
              simpa using this
            nlinarith [norm_nonneg η, norm_nonneg (ξ - η)]
          have hq : (1 + ‖ξ - η‖) ^ (-(d : ℝ)) ≤
              (1 + ‖η‖) ^ (d : ℝ) * (1 + ‖ξ‖) ^ (-(d : ℝ)) := by
            have hA : 0 < (1 + ‖ξ‖) ^ (d : ℝ) := by positivity
            have hD : 0 < (1 + ‖ξ - η‖) ^ (d : ℝ) := by positivity
            have h5 : (1 + ‖ξ‖) ^ (d : ℝ) ≤ (1 + ‖η‖) ^ (d : ℝ) * (1 + ‖ξ - η‖) ^ (d : ℝ) := by
              rw [← Real.mul_rpow (by positivity) (by positivity)]
              exact Real.rpow_le_rpow (by positivity) hP hdR.le
            rw [Real.rpow_neg (by positivity), Real.rpow_neg (by positivity), inv_eq_one_div,
              ← div_eq_mul_inv, div_le_div_iff₀ hD hA]
            linarith
          calc ‖a η‖ * (C * (1 + ‖ξ - η‖) ^ (-(d : ℝ)))
              ≤ ‖a η‖ * (C * ((1 + ‖η‖) ^ (d : ℝ) * (1 + ‖ξ‖) ^ (-(d : ℝ)))) := by gcongr
            _ = _ := by ring
      _ = ENNReal.ofReal (C * (1 + ‖ξ‖) ^ (-(d : ℝ)) * W) := by
          rw [← ofReal_integral_eq_lintegral_ofReal ((hint.const_mul _))
            (Filter.Eventually.of_forall fun η => by positivity), integral_const_mul]
  have h3 := h1.trans h2
  rw [← ofReal_norm] at h3
  have h4 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3
  refine h4.trans ?_
  have h5 := tc3_peetre_wt hdR ξ
  calc C * (1 + ‖ξ‖) ^ (-(d : ℝ)) * W = (C * W) * (1 + ‖ξ‖) ^ (-(d : ℝ)) := by ring
    _ ≤ (C * W + 1) * (1 + ‖ξ‖) ^ (-(d : ℝ)) := by gcongr; linarith
    _ ≤ (C * W + 1) * ((2 * Real.pi) ^ (d : ℝ) * wt ξ ^ (-(d : ℝ) / 2)) := by gcongr
    _ = _ := by ring

/-- **Fourier decay of the localised logarithmic kernel** (`d ≥ 1`, `θ ∈ C_c^∞`):
`‖\widehat{θ (-log |x|)}(ξ)‖ ≤ A ⟨ξ⟩^{-d}`. -/
theorem tc3_log_loc_decay {θ : Euc d → ℝ} (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    (hd : 0 < d) :
    ∃ A : ℝ, 0 < A ∧ ∀ ξ : Euc d,
      ‖tc3_Ghat (tc3_Gloc d 0 θ) ξ‖ ≤ A * wt ξ ^ (-((d : ℝ) - 0) / 2) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have : Nontrivial (Euc d) := by
    rw [← Module.finrank_pos_iff (R := ℝ)]; simpa using hd
  set c0 : ℝ := (1 / 2) * ∫ u in Ioi (1 : ℝ), Real.exp (-u) / u with hc0
  set S : Euc d → ℝ := fun x => θ x * (tc3_F (‖x‖ ^ 2) - c0) with hSdef
  have hS : ContDiff ℝ ∞ S :=
    hθ.mul (((tc3_F_contDiff_top.comp (contDiff_norm_sq ℝ))).sub contDiff_const)
  have hSc : HasCompactSupport S := hc.mul_right
  obtain ⟨AQ, hAQ, hQ⟩ := tc3_logQ_decay hθ hc hd
  obtain ⟨AS, hAS, hSd⟩ := tc3_smooth_decay hS hSc (γ := (d : ℝ)) hdR
  refine ⟨AQ + AS, by positivity, fun ξ => ?_⟩
  have hx0 : ∀ᵐ x ∂(volume : Measure (Euc d)), x ≠ 0 := by
    rw [ae_iff]
    simpa using measure_singleton (μ := (volume : Measure (Euc d))) (0 : Euc d)
  obtain ⟨Bθ, hBθ⟩ := hθ.continuous.bounded_above_of_compact_support hc
  have hQi : Integrable (fun x => θ x * qTauLog d 1 x) volume :=
    (qTauLog_integrable_integral (d := d) hd one_pos).1.bdd_mul
      hθ.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hBθ)
  have hSi : Integrable S volume := hS.continuous.integrable_of_hasCompactSupport hSc
  have hid : ∀ᵐ x ∂(volume : Measure (Euc d)),
      tc3_Gloc d 0 θ x = θ x * qTauLog d 1 x + S x := by
    filter_upwards [hx0] with x hx
    unfold tc3_Gloc
    rw [riesz_log_heat_split one_pos hx, hSdef]
    simp only [kTauLog, tc3_F, psd3_h, one_div_one, hc0]
    ring
  have hsplit : tc3_Ghat (tc3_Gloc d 0 θ) ξ =
      tc3_Ghat (fun x => θ x * qTauLog d 1 x) ξ + tc3_Ghat S ξ := by
    unfold tc3_Ghat
    rw [Real.fourier_eq, Real.fourier_eq, Real.fourier_eq]
    rw [← integral_add ((Real.fourierIntegral_convergent_iff ξ).2 hQi.ofReal)
      ((Real.fourierIntegral_convergent_iff ξ).2 hSi.ofReal)]
    refine integral_congr_ae ?_
    filter_upwards [hid] with x hx
    rw [hx]
    push_cast
    simp only [smul_add]
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  have h1 := hQ ξ
  have h2 := hSd ξ
  simp only [sub_zero]
  linarith

/-- **TC-3, Hilbert form** (`0 ≤ s < d`, `θ ∈ C_c^∞`): convolution with `θ g` gains `d - s` derivatives. -/
theorem tc3_riesz_loc_sobolev_gain {θ : Euc d → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hc : HasCompactSupport θ) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (f : Euc d → ℝ), HRS.PDE.ToolboxRd.MemSobolev t f →
      HRS.PDE.ToolboxRd.MemSobolev (t + ((d : ℝ) - s))
        (HRS.Whole.convFun (fun x => θ x * rieszKernel d s x) f) ∧
      HRS.PDE.ToolboxRd.sobolevNormSq (t + ((d : ℝ) - s))
        (HRS.Whole.convFun (fun x => θ x * rieszKernel d s x) f) ≤
          C ^ 2 * HRS.PDE.ToolboxRd.sobolevNormSq t f := by
  have hd : 0 < d := by
    have : (0 : ℝ) < d := lt_of_le_of_lt hs0 hsd
    exact_mod_cast this
  have hmeas := tc3_Gloc_measurable hθ.continuous s
  have hint := tc3_Gloc_integrable hθ.continuous hc hs0 hsd
  rcases hs0.eq_or_lt with h0 | hpos
  · subst h0
    obtain ⟨A, hA, hFG⟩ := tc3_log_loc_decay hθ hc hd
    exact ⟨A, hA, fun t f hf => tc3_sobolev_gain hmeas hint hFG hf⟩
  · obtain ⟨A, hA, hFG⟩ := tc3_riesz_loc_decay hθ hc hpos hsd
    exact ⟨A, hA, fun t f hf => tc3_sobolev_gain hmeas hint hFG hf⟩

/-- **TC-3, extended-norm form** (`0 ≤ s < d`). -/
theorem tc3_riesz_loc_sobolevNormE_gain {θ : Euc d → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hc : HasCompactSupport θ) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ) (f : Euc d → ℝ),
      HRS.Whole.sobolevNormE (t + ((d : ℝ) - s))
          (HRS.Whole.convFun (fun x => θ x * rieszKernel d s x) f) ≤
        ENNReal.ofReal C * HRS.Whole.sobolevNormE t f := by
  have hd : 0 < d := by
    have : (0 : ℝ) < d := lt_of_le_of_lt hs0 hsd
    exact_mod_cast this
  have hmeas := tc3_Gloc_measurable hθ.continuous s
  have hint := tc3_Gloc_integrable hθ.continuous hc hs0 hsd
  rcases hs0.eq_or_lt with h0 | hpos
  · subst h0
    obtain ⟨A, hA, hFG⟩ := tc3_log_loc_decay hθ hc hd
    exact ⟨A, hA, fun t f => tc3_sobolevNormE_gain hmeas hint hA hFG t f⟩
  · obtain ⟨A, hA, hFG⟩ := tc3_riesz_loc_decay hθ hc hpos hsd
    exact ⟨A, hA, fun t f => tc3_sobolevNormE_gain hmeas hint hA hFG t f⟩

end HRS.MS.Tc3
