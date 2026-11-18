import HRS.MS.WadAux66

/-!
# S8.3, packet S8D-2, part 13: local interpolation between a Lipschitz bound and the `L²(μ)` norm

`s8d_interp`: if `h` is `L`-Lipschitz about `x₀` on the unit ball and `‖x₀‖ ≤ R₀`, then for every `0 < r ≤ 1`
`|h(x₀)| ≤ L r + (∫ h² dμ)^{1/2} / (ρ₀ om r^d)^{1/2}`, with `ρ₀ = min_{‖z‖ ≤ R₀+1} ρ > 0` and `om = vol(B_1)`.
(On `B(x₀,r)` one has `|h| ≥ |h(x₀)| - Lr`, so `∫h²dμ ≥ (|h(x₀)|-Lr)² μ(B(x₀,r))`.)  This is the replacement of
the Ehrling lemma in the Lasota-Yorke inequality for `U_1 - Π` (no compact operator is needed).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8d_interp (hd1 : 1 ≤ d) {ρ : Euc d → ℝ} (hρc : Continuous ρ) (hρpos : ∀ x, 0 < ρ x)
    (hρm : Measurable ρ) (R₀ : ℝ) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ {h : Euc d → ℝ} {L r : ℝ} {x₀ : Euc d}, 0 ≤ L → 0 < r → r ≤ 1 → ‖x₀‖ ≤ R₀ →
      (∀ z : Euc d, ‖z - x₀‖ ≤ 1 → |h z - h x₀| ≤ L * ‖z - x₀‖) →
      Integrable (fun z => h z ^ 2) (HRS.Whole.withDensityReal ρ) →
      |h x₀| ≤ L * r + Real.sqrt (∫ z, h z ^ 2 ∂(HRS.Whole.withDensityReal ρ)) /
        Real.sqrt (ρ₀ * (volume (ball (0 : Euc d) 1)).toReal * r ^ d) := by
  have hK : IsCompact (closedBall (0 : Euc d) (|R₀| + 1)) := isCompact_closedBall _ _
  obtain ⟨xm, -, hxm⟩ := hK.exists_isMinOn ⟨0, mem_closedBall_self (by positivity)⟩ hρc.continuousOn
  refine ⟨ρ xm, hρpos xm, fun {h L r x₀} hL hr hr1 hx₀ hlip hint => ?_⟩
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set ρ₀ := ρ xm with hρ₀
  set om : ℝ := (volume (ball (0 : Euc d) 1)).toReal with hom
  have hom0 : 0 < om := by
    rw [hom]
    exact ENNReal.toReal_pos (measure_ball_pos _ _ one_pos).ne' (measure_ball_lt_top).ne
  set κ : ℝ := ρ₀ * om * r ^ d with hκ
  have hκ0 : 0 < κ := mul_pos (mul_pos (hρpos xm) hom0) (pow_pos hr d)
  set s : ℝ := |h x₀| with hs
  have hsq0 : 0 ≤ Real.sqrt (∫ z, h z ^ 2 ∂μ) / Real.sqrt κ := div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  by_cases hδ : s - L * r ≤ 0
  · linarith
  · push Not at hδ
    set B : Set (Euc d) := ball x₀ r with hB
    -- lower bound for the measure of the ball
    have hBsub : ∀ z ∈ B, z ∈ closedBall (0 : Euc d) (|R₀| + 1) := fun z hz => by
      rw [mem_closedBall_zero_iff]
      have h1 : ‖z - x₀‖ < r := by rwa [hB, mem_ball_iff_norm] at hz
      have h2 : ‖z‖ ≤ ‖z - x₀‖ + ‖x₀‖ := by
        have := norm_le_norm_sub_add z x₀
        linarith
      have := le_abs_self R₀
      linarith
    have hvol : (volume B) = ENNReal.ofReal (r ^ d) * volume (ball (0 : Euc d) 1) := by
      rw [hB, Measure.addHaar_ball_of_pos volume x₀ hr]
      simp
    have hμB : ENNReal.ofReal (ρ₀ * (r ^ d * om)) ≤ μ B := by
      rw [hμ, HRS.Whole.withDensityReal, withDensity_apply _ measurableSet_ball]
      have e1 : ENNReal.ofReal om = volume (ball (0 : Euc d) 1) := by
        rw [hom]; exact ENNReal.ofReal_toReal (measure_ball_lt_top).ne
      calc ENNReal.ofReal (ρ₀ * (r ^ d * om)) =
            ENNReal.ofReal ρ₀ * (ENNReal.ofReal (r ^ d) * ENNReal.ofReal om) := by
            rw [ENNReal.ofReal_mul (hρpos xm).le, ENNReal.ofReal_mul (pow_nonneg hr.le d)]
        _ = ENNReal.ofReal ρ₀ * volume B := by rw [hvol, e1]
        _ = ∫⁻ z in B, ENNReal.ofReal ρ₀ := by rw [setLIntegral_const]
        _ ≤ ∫⁻ z in B, ENNReal.ofReal (ρ z) := by
            refine setLIntegral_mono' measurableSet_ball fun z hz => ?_
            exact ENNReal.ofReal_le_ofReal (hxm (hBsub z hz))
    have hμBfin : μ B ≠ ⊤ := by
      rw [hμ, HRS.Whole.withDensityReal, withDensity_apply _ measurableSet_ball]
      refine ne_of_lt (lt_of_le_of_lt (setLIntegral_mono' measurableSet_ball
        (g := fun z => ENNReal.ofReal (sSup (ρ '' closedBall (0 : Euc d) (|R₀| + 1)))) fun z hz => ?_) ?_)
      · refine ENNReal.ofReal_le_ofReal (le_csSup (hK.image hρc).bddAbove ⟨z, hBsub z hz, rfl⟩)
      · rw [setLIntegral_const]
        exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_ball_lt_top
    have hBreal : κ ≤ μ.real B := by
      have := ENNReal.toReal_mono hμBfin hμB
      rw [ENNReal.toReal_ofReal (mul_nonneg (hρpos xm).le (mul_nonneg (pow_nonneg hr.le d) hom0.le))] at this
      show κ ≤ (μ B).toReal
      rw [hκ]
      nlinarith [this]
    -- pointwise lower bound for `h²` on the ball
    have hpt : ∀ z ∈ B, (s - L * r) ^ 2 ≤ h z ^ 2 := fun z hz => by
      have h1 : ‖z - x₀‖ < r := by rwa [hB, mem_ball_iff_norm] at hz
      have h2 := hlip z (by linarith)
      have h3 : s - L * r ≤ |h z| := by
        have := abs_sub_abs_le_abs_sub (h x₀) (h z)
        rw [abs_sub_comm] at this
        have h4 : L * ‖z - x₀‖ ≤ L * r := mul_le_mul_of_nonneg_left h1.le hL
        linarith
      calc (s - L * r) ^ 2 ≤ |h z| ^ 2 := pow_le_pow_left₀ hδ.le h3 2
        _ = h z ^ 2 := sq_abs _
    have hset : ∫ z in B, (s - L * r) ^ 2 ∂μ ≤ ∫ z in B, h z ^ 2 ∂μ :=
      setIntegral_mono_on (integrableOn_const (hs := hμBfin)) hint.integrableOn measurableSet_ball hpt
    have hle : ∫ z in B, h z ^ 2 ∂μ ≤ ∫ z, h z ^ 2 ∂μ :=
      setIntegral_le_integral hint (Eventually.of_forall fun z => sq_nonneg _)
    rw [setIntegral_const, smul_eq_mul] at hset
    have hkey : (s - L * r) ^ 2 * κ ≤ ∫ z, h z ^ 2 ∂μ := by
      calc (s - L * r) ^ 2 * κ ≤ (s - L * r) ^ 2 * μ.real B :=
            mul_le_mul_of_nonneg_left hBreal (sq_nonneg _)
        _ = μ.real B * (s - L * r) ^ 2 := by ring
        _ ≤ _ := hset.trans hle
    have hsq : (s - L * r) * Real.sqrt κ ≤ Real.sqrt (∫ z, h z ^ 2 ∂μ) := by
      rw [← Real.sqrt_sq hδ.le, ← Real.sqrt_mul (sq_nonneg _)]
      exact Real.sqrt_le_sqrt hkey
    have : s - L * r ≤ Real.sqrt (∫ z, h z ^ 2 ∂μ) / Real.sqrt κ := by
      rw [le_div_iff₀ (Real.sqrt_pos.2 hκ0)]
      exact hsq
    linarith

end HRS.MS.Wad
