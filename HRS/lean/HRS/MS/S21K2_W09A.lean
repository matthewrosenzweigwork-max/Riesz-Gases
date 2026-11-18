import HRS.MP.RdInit
import HRS.MS.S21G2_W01

/-!
# S21K2 W09A -- Fourier estimates for the local compactness packet (R26-T3.W09)

For `u` continuous with compact support in a ball `B_L`: `F u = 𝓕 u` is bounded by `∫|u|`, Lipschitz with constant
`2π L ∫|u|`, `∫ ‖F u‖² = ∫ u²`, the tail `∫_{|ξ|>R} ‖F u‖² <= K/(1+4π²R²)` when `∫ (1+4π²|ξ|²)|F u|² <= K`, and the distance
estimate `∫(u-v)² <= vol(B_R) δ² + 4K/(1+4π²R²)` when `sup_{B_R} |F u - F v| <= δ`.  Helper prefix `s21k2_w09_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators FourierTransform
noncomputable section
namespace HRS.MS.R26T3
open HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

/-- Fourier transform of a real function, complex valued -/
def s21k2_w09_F (u : HRS.Euc d → ℝ) : HRS.Euc d → ℂ := 𝓕 (fun x : HRS.Euc d => ((u x : ℝ) : ℂ))

theorem s21k2_w09_F_eq (u : HRS.Euc d → ℝ) (ξ : HRS.Euc d) :
    s21k2_w09_F u ξ = ∫ v, phase v ξ • ((u v : ℝ) : ℂ) := by
  unfold s21k2_w09_F
  rw [Real.fourier_eq']
  rfl

theorem s21k2_w09_F_bound {u : HRS.Euc d → ℝ} (hu : Continuous u) (hc : HasCompactSupport u) (ξ : HRS.Euc d) :
    ‖s21k2_w09_F u ξ‖ ≤ ∫ v, |u v| := by
  rw [s21k2_w09_F_eq]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq (integral_congr_ae (Eventually.of_forall fun v => ?_)))
  simp [norm_smul, norm_phase]

theorem s21k2_w09_F_lip {u : HRS.Euc d → ℝ} (hu : Continuous u) (hc : HasCompactSupport u) {L : ℝ}
    (hs : tsupport u ⊆ Metric.closedBall 0 L) (ξ ξ' : HRS.Euc d) :
    ‖s21k2_w09_F u ξ - s21k2_w09_F u ξ'‖ ≤ 2 * Real.pi * L * ‖ξ - ξ'‖ * ∫ v, |u v| := by
  have hia : Integrable (fun v : HRS.Euc d => |u v|) :=
    (hu.integrable_of_hasCompactSupport hc).abs
  have hint : ∀ ζ : HRS.Euc d, Integrable (fun v : HRS.Euc d => phase v ζ • ((u v : ℝ) : ℂ)) := fun ζ => by
    have hcont : Continuous fun v : HRS.Euc d => phase v ζ • ((u v : ℝ) : ℂ) := by
      unfold phase; fun_prop
    exact hia.mono' hcont.aestronglyMeasurable
      (Eventually.of_forall fun v => by simp [norm_phase])
  rw [s21k2_w09_F_eq, s21k2_w09_F_eq, ← integral_sub (hint ξ) (hint ξ')]
  have h := norm_integral_le_of_norm_le (hia.const_mul (2 * Real.pi * L * ‖ξ - ξ'‖)) (f := fun v : HRS.Euc d =>
    phase v ξ • ((u v : ℝ) : ℂ) - phase v ξ' • ((u v : ℝ) : ℂ)) (Eventually.of_forall fun v => ?_)
  · rw [integral_const_mul] at h
    exact h
  · by_cases hv : u v = 0
    · simp [hv]
    · have hvB : ‖v‖ ≤ L := by
        have := hs (subset_tsupport u (Function.mem_support.2 hv))
        simpa using this
      rw [← sub_smul, norm_smul]
      have h1 : ‖phase v ξ - phase v ξ'‖ ≤ 2 * Real.pi * L * ‖ξ - ξ'‖ := by
        have e : phase v ξ - phase v ξ' = phase v ξ * (1 - phase v (ξ' - ξ)) := by
          unfold phase
          rw [mul_sub, mul_one, ← Complex.exp_add]
          congr 2
          rw [inner_sub_right]; push_cast; ring
        rw [e, norm_mul, norm_phase, one_mul]
        refine (norm_one_sub_phase_le v (ξ' - ξ)).trans ?_
        rw [norm_sub_rev ξ' ξ]
        have := mul_le_mul_of_nonneg_right hvB (norm_nonneg (ξ - ξ'))
        nlinarith [Real.pi_pos]
      simp only [Complex.norm_real, Real.norm_eq_abs]
      calc ‖phase v ξ - phase v ξ'‖ * |u v| ≤ 2 * Real.pi * L * ‖ξ - ξ'‖ * |u v| :=
            mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ = _ := rfl


/-- `∫ |u| ≤ (vol B_L + ∫ u²)/2` for `u` supported in the ball -/
theorem s21k2_w09_L1 {u : HRS.Euc d → ℝ} (hu : Continuous u) (hc : HasCompactSupport u) {L : ℝ}
    (hs : tsupport u ⊆ Metric.closedBall 0 L) :
    ∫ v, |u v| ≤ ((volume (Metric.closedBall (0 : HRS.Euc d) L)).toReal + ∫ v, u v ^ 2) / 2 := by
  have hia : Integrable (fun v : HRS.Euc d => |u v|) :=
    (hu.integrable_of_hasCompactSupport hc).abs
  have hi2 : Integrable (fun v : HRS.Euc d => u v ^ 2) :=
    (hu.memLp_of_hasCompactSupport hc).integrable_sq
  have hB : Integrable ((Metric.closedBall (0 : HRS.Euc d) L).indicator (fun _ => (1 : ℝ))) :=
    (integrable_indicator_iff measurableSet_closedBall).2 (integrableOn_const measure_closedBall_lt_top.ne)
  have h := integral_mono hia ((hB.add hi2).div_const 2) (f := fun v : HRS.Euc d => |u v|)
    (g := fun v => ((Metric.closedBall (0 : HRS.Euc d) L).indicator (fun _ => (1 : ℝ)) v + u v ^ 2) / 2)
    (fun v => by
      by_cases hv : u v = 0
      · have h0 : 0 ≤ (Metric.closedBall (0 : HRS.Euc d) L).indicator (fun _ => (1 : ℝ)) v :=
          Set.indicator_nonneg (fun _ _ => zero_le_one) v
        simp only [hv, abs_zero]; nlinarith
      · have : v ∈ Metric.closedBall (0 : HRS.Euc d) L := hs (subset_tsupport u (Function.mem_support.2 hv))
        simp only [Set.indicator_of_mem this]
        nlinarith [sq_nonneg (|u v| - 1), sq_abs (u v)])
  refine h.trans (le_of_eq ?_)
  rw [integral_div, integral_add hB hi2, integral_indicator_const _ measurableSet_closedBall]
  simp [Measure.real]


theorem s21k2_w09_ae {u : HRS.Euc d → ℝ} (hu : Continuous u) (hc : HasCompactSupport u) :
    fourierL2 u =ᵐ[volume] s21k2_w09_F u :=
  HRS.Commutator.Whole.energyAux_fourierL2_eq u (hu.integrable_of_hasCompactSupport hc)
    (hu.memLp_of_hasCompactSupport hc)

theorem s21k2_w09_parseval {u : HRS.Euc d → ℝ} (hu : Continuous u) (hc : HasCompactSupport u) :
    ∫ ξ, ‖s21k2_w09_F u ξ‖ ^ 2 = ∫ x, u x ^ 2 := by
  rw [← integral_norm_sq_fourierL2 (hu.memLp_of_hasCompactSupport hc)]
  exact integral_congr_ae ((s21k2_w09_ae hu hc).mono fun ξ h => by show ‖s21k2_w09_F u ξ‖ ^ 2 = ‖fourierL2 u ξ‖ ^ 2; rw [h])

theorem s21k2_w09_diff {u v : HRS.Euc d → ℝ} (hu : Continuous u) (hcu : HasCompactSupport u)
    (hv : Continuous v) (hcv : HasCompactSupport v) :
    ∫ x, (u x - v x) ^ 2 = ∫ ξ, ‖s21k2_w09_F u ξ - s21k2_w09_F v ξ‖ ^ 2 := by
  have hm : MemLp (fun x => u x - v x) 2 volume :=
    (hu.memLp_of_hasCompactSupport hcu).sub (hv.memLp_of_hasCompactSupport hcv)
  rw [← integral_norm_sq_fourierL2 hm]
  refine integral_congr_ae ?_
  filter_upwards [fourierL2_sub (hu.memLp_of_hasCompactSupport hcu) (hv.memLp_of_hasCompactSupport hcv),
    s21k2_w09_ae hu hcu, s21k2_w09_ae hv hcv] with ξ h1 h2 h3
  rw [h1, h2, h3]

theorem s21k2_w09_tail {u : HRS.Euc d → ℝ} (hu : Continuous u) (hc : HasCompactSupport u) {K : ℝ}
    (hs : HRS.PDE.ToolboxRd.MemSobolev (1 : ℝ) u) (hK : ∫ ξ, (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (1 : ℝ) * ‖fourierL2 u ξ‖ ^ 2 ≤ K)
    {R : ℝ} (hR : 0 ≤ R) :
    ∫ ξ in (Metric.closedBall (0 : HRS.Euc d) R)ᶜ, ‖s21k2_w09_F u ξ‖ ^ 2 ≤ K / (1 + 4 * Real.pi ^ 2 * R ^ 2) := by
  have hpos : 0 < 1 + 4 * Real.pi ^ 2 * R ^ 2 := by positivity
  have hint : Integrable (fun ξ : HRS.Euc d => (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (1 : ℝ) * ‖fourierL2 u ξ‖ ^ 2) :=
    hs.2
  have hae := s21k2_w09_ae hu hc
  have h1 : ∫ ξ in (Metric.closedBall (0 : HRS.Euc d) R)ᶜ, ‖s21k2_w09_F u ξ‖ ^ 2 =
      ∫ ξ in (Metric.closedBall (0 : HRS.Euc d) R)ᶜ, ‖fourierL2 u ξ‖ ^ 2 :=
    integral_congr_ae (ae_restrict_of_ae (hae.mono fun ξ h => by
      show ‖s21k2_w09_F u ξ‖ ^ 2 = ‖fourierL2 u ξ‖ ^ 2; rw [h]))
  rw [h1, le_div_iff₀ hpos]
  have h2 : Integrable (fun ξ : HRS.Euc d => ‖fourierL2 u ξ‖ ^ 2) :=
    (memLp_fourierL2 (hu.memLp_of_hasCompactSupport hc)).norm.integrable_sq
  calc (∫ ξ in (Metric.closedBall (0 : HRS.Euc d) R)ᶜ, ‖fourierL2 u ξ‖ ^ 2) * (1 + 4 * Real.pi ^ 2 * R ^ 2)
      = ∫ ξ in (Metric.closedBall (0 : HRS.Euc d) R)ᶜ, ‖fourierL2 u ξ‖ ^ 2 * (1 + 4 * Real.pi ^ 2 * R ^ 2) := by
        rw [integral_mul_const]
    _ ≤ ∫ ξ in (Metric.closedBall (0 : HRS.Euc d) R)ᶜ, (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (1 : ℝ) * ‖fourierL2 u ξ‖ ^ 2 := by
        refine setIntegral_mono_on (h2.integrableOn.mul_const _) hint.integrableOn
          (measurableSet_closedBall.compl) fun ξ hξ => ?_
        have : R < ‖ξ‖ := by simpa using hξ
        rw [Real.rpow_one]
        have h3 : 1 + 4 * Real.pi ^ 2 * R ^ 2 ≤ 1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := by
          have : R ^ 2 ≤ ‖ξ‖ ^ 2 := by nlinarith
          nlinarith [Real.pi_pos]
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right h3 (sq_nonneg _)
    _ ≤ ∫ ξ, (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (1 : ℝ) * ‖fourierL2 u ξ‖ ^ 2 :=
        setIntegral_le_integral hint (Eventually.of_forall fun ξ => by positivity)
    _ ≤ K := hK


theorem s21k2_w09_F_cont {u : HRS.Euc d → ℝ} (hu : Continuous u) (hc : HasCompactSupport u) :
    Continuous (s21k2_w09_F u) := by
  have hi : Integrable (fun x : HRS.Euc d => ((u x : ℝ) : ℂ)) := (hu.integrable_of_hasCompactSupport hc).ofReal
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar continuous_inner hi

/-- the `L²` element of a continuous compactly supported function -/
def s21k2_w09_lp {u : HRS.Euc d → ℝ} (hu : Continuous u) (hc : HasCompactSupport u) : Lp ℝ 2 (volume : Measure (HRS.Euc d)) :=
  (hu.memLp_of_hasCompactSupport hc).toLp u

theorem s21k2_w09_lp_dist {u v : HRS.Euc d → ℝ} (hu : Continuous u) (hcu : HasCompactSupport u)
    (hv : Continuous v) (hcv : HasCompactSupport v) :
    dist (s21k2_w09_lp hu hcu) (s21k2_w09_lp hv hcv) ^ 2 = ∫ x, (u x - v x) ^ 2 := by
  have hmu : MemLp u 2 volume := hu.memLp_of_hasCompactSupport hcu
  have hmv : MemLp v 2 volume := hv.memLp_of_hasCompactSupport hcv
  have hmw : MemLp (fun x => u x - v x) 2 volume := hmu.sub hmv
  have e : s21k2_w09_lp hu hcu - s21k2_w09_lp hv hcv = hmw.toLp (fun x => u x - v x) := by
    unfold s21k2_w09_lp
    rw [← MemLp.toLp_sub]; rfl
  rw [dist_eq_norm, e]
  set f : Lp ℝ 2 (volume : Measure (HRS.Euc d)) := hmw.toLp (fun x => u x - v x) with hf
  have h : inner ℝ f f = ∫ a, inner ℝ (f a) (f a) := L2.inner_def f f
  rw [real_inner_self_eq_norm_sq] at h
  rw [h]
  refine integral_congr_ae ?_
  filter_upwards [MemLp.coeFn_toLp hmw] with x hx
  show inner ℝ (f x) (f x) = (u x - v x) ^ 2
  rw [hf, hx]; simp [sq]


theorem s21k2_w09_estimate {u v : HRS.Euc d → ℝ} (hu : Continuous u) (hcu : HasCompactSupport u)
    (hv : Continuous v) (hcv : HasCompactSupport v) {K : ℝ}
    (hsu : HRS.PDE.ToolboxRd.MemSobolev (1 : ℝ) u)
    (hKu : ∫ ξ, (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (1 : ℝ) * ‖fourierL2 u ξ‖ ^ 2 ≤ K)
    (hsv : HRS.PDE.ToolboxRd.MemSobolev (1 : ℝ) v)
    (hKv : ∫ ξ, (1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (1 : ℝ) * ‖fourierL2 v ξ‖ ^ 2 ≤ K) {R δ : ℝ}
    (hR : 0 ≤ R) (hnear : ∀ ξ ∈ Metric.closedBall (0 : HRS.Euc d) R,
      ‖s21k2_w09_F u ξ - s21k2_w09_F v ξ‖ ≤ δ) :
    ∫ x, (u x - v x) ^ 2 ≤ (volume (Metric.closedBall (0 : HRS.Euc d) R)).toReal * δ ^ 2 +
      4 * K / (1 + 4 * Real.pi ^ 2 * R ^ 2) := by
  have hmu : MemLp u 2 volume := hu.memLp_of_hasCompactSupport hcu
  have hmv : MemLp v 2 volume := hv.memLp_of_hasCompactSupport hcv
  rw [s21k2_w09_diff hu hcu hv hcv]
  have hiF : ∀ {w : HRS.Euc d → ℝ}, Continuous w → HasCompactSupport w →
      Integrable (fun ξ : HRS.Euc d => ‖s21k2_w09_F w ξ‖ ^ 2) := fun {w} hw hcw => by
    have := (memLp_fourierL2 (hw.memLp_of_hasCompactSupport hcw : MemLp w 2 volume)).norm.integrable_sq
    exact this.congr ((s21k2_w09_ae hw hcw).mono fun ξ h => by
      show ‖fourierL2 w ξ‖ ^ 2 = ‖s21k2_w09_F w ξ‖ ^ 2; rw [h])
  have hid : Integrable (fun ξ : HRS.Euc d => ‖s21k2_w09_F u ξ - s21k2_w09_F v ξ‖ ^ 2) := by
    have hmw : MemLp (fun x => u x - v x) 2 volume := hmu.sub hmv
    have := (memLp_fourierL2 hmw).norm.integrable_sq
    refine this.congr ?_
    filter_upwards [fourierL2_sub hmu hmv, s21k2_w09_ae hu hcu, s21k2_w09_ae hv hcv] with ξ h1 h2 h3
    show ‖fourierL2 (fun x => u x - v x) ξ‖ ^ 2 = ‖s21k2_w09_F u ξ - s21k2_w09_F v ξ‖ ^ 2
    rw [h1]
    show ‖fourierL2 u ξ - fourierL2 v ξ‖ ^ 2 = _
    rw [h2, h3]
  rw [← integral_add_compl measurableSet_closedBall hid]
  have h1 : ∫ ξ in Metric.closedBall (0 : HRS.Euc d) R, ‖s21k2_w09_F u ξ - s21k2_w09_F v ξ‖ ^ 2 ≤
      (volume (Metric.closedBall (0 : HRS.Euc d) R)).toReal * δ ^ 2 := by
    calc _ ≤ ∫ ξ in Metric.closedBall (0 : HRS.Euc d) R, δ ^ 2 :=
          setIntegral_mono_on hid.integrableOn (integrableOn_const measure_closedBall_lt_top.ne)
            measurableSet_closedBall fun ξ hξ =>
            pow_le_pow_left₀ (norm_nonneg _) (hnear ξ hξ) 2
      _ = _ := by rw [setIntegral_const]; simp [Measure.real]
  have h2 : ∫ ξ in (Metric.closedBall (0 : HRS.Euc d) R)ᶜ, ‖s21k2_w09_F u ξ - s21k2_w09_F v ξ‖ ^ 2 ≤
      4 * K / (1 + 4 * Real.pi ^ 2 * R ^ 2) := by
    have tu := s21k2_w09_tail hu hcu hsu hKu hR
    have tv := s21k2_w09_tail hv hcv hsv hKv hR
    calc _ ≤ ∫ ξ in (Metric.closedBall (0 : HRS.Euc d) R)ᶜ,
          (2 * ‖s21k2_w09_F u ξ‖ ^ 2 + 2 * ‖s21k2_w09_F v ξ‖ ^ 2) :=
          setIntegral_mono_on hid.integrableOn
            (((hiF hu hcu).const_mul 2).add ((hiF hv hcv).const_mul 2)).integrableOn
            measurableSet_closedBall.compl fun ξ _ => by
            have := norm_sub_le (s21k2_w09_F u ξ) (s21k2_w09_F v ξ)
            nlinarith [norm_nonneg (s21k2_w09_F u ξ), norm_nonneg (s21k2_w09_F v ξ),
              norm_nonneg (s21k2_w09_F u ξ - s21k2_w09_F v ξ), sq_nonneg (‖s21k2_w09_F u ξ‖ - ‖s21k2_w09_F v ξ‖)]
      _ = 2 * (∫ ξ in (Metric.closedBall (0 : HRS.Euc d) R)ᶜ, ‖s21k2_w09_F u ξ‖ ^ 2) +
          2 * ∫ ξ in (Metric.closedBall (0 : HRS.Euc d) R)ᶜ, ‖s21k2_w09_F v ξ‖ ^ 2 := by
          rw [integral_add ((hiF hu hcu).const_mul 2).integrableOn ((hiF hv hcv).const_mul 2).integrableOn,
            integral_const_mul, integral_const_mul]
      _ ≤ _ := by
          have : 4 * K / (1 + 4 * Real.pi ^ 2 * R ^ 2) = 2 * (K / (1 + 4 * Real.pi ^ 2 * R ^ 2)) +
              2 * (K / (1 + 4 * Real.pi ^ 2 * R ^ 2)) := by ring
          rw [this]; linarith
  linarith

end HRS.MS.R26T3
