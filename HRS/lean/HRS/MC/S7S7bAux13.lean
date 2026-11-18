import HRS.MC.S7S7bAux12
import HRS.MC.S7S7bAux4
import HRS.MC.SEdgeB7

/-!
# Packet `s7_S7b_weighted_moments`, helper 13: `E |sqrt N (mu_N(w) - E mu_N(w))|^{2q} <= C sup|w|^{2q}`
Uniformly in the bounded smooth observable `w` (B7 by homogeneity + the uniform mean bias).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ComplexConjugate

noncomputable section

namespace HRS.MC.Sec7.S7b

open HRS HRS.Sec7 HRS.MC.SEdge HRS.PDE

variable {d : ℕ} {s : ℝ}

theorem s7b_pair_emp_meas {N : ℕ} (hN : 1 ≤ N) {w : Torus d → ℝ} (hw : Measurable w) :
    Measurable (fun X : Config d N => pair (empirical X) w) := by
  have : (fun X : Config d N => pair (empirical X) w) = fun X => (∑ i, w (X i)) / N :=
    funext fun X => HRS.MC.SEdge.B4c.b4c_pair_empirical X hw
  rw [this]
  exact (Finset.measurable_sum _ fun i _ => hw.comp (measurable_pi_apply i)).div_const _

theorem s7b_Y_moment (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 ≤ γ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (w : Torus d → ℝ) (T : ℝ), Torus.IsSmooth w → (∀ x, |w x| ≤ T) →
      ∀ N : ℕ, 1 ≤ N →
        ∫ X, |sed_Y (sed_Q d s N γ ρ) w X| ^ (2 * q) ∂(sed_Q d s N γ ρ) ≤ C * T ^ (2 * q) := by
  haveI hμ : IsProbabilityMeasure (withDensityReal ρ) := HRS.MC.SEdge.B3.b3_prob hρ
  obtain ⟨Cu, hCu0, hCu⟩ := s7b_bias_uniform hd hs0 hs hγ hρ
  obtain ⟨CB, hCB⟩ := HRS.MC.SEdge.B7.sed_B7_lln_proof hd hs0 hs hγ hρ 1 q
  refine ⟨max 1 (2 ^ (2 * q) * (max CB 0 + Cu ^ (2 * q))), le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro w T hw hwT N hN
  haveI hQ : IsProbabilityMeasure (sed_Q d s N γ ρ) := B5a.b5a_Q_prob hd hs0 hs hγ hρ hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hT0 : 0 ≤ T := (abs_nonneg _).trans (hwT 0)
  have hwc : Continuous w := HRS.Q66.q66_cont_of_smooth hw
  have hwm : Measurable w := hwc.measurable
  rcases hT0.eq_or_lt with hT | hT
  · -- `T = 0`: `w = 0`
    subst hT
    have hw0 : ∀ x, w x = 0 := fun x => abs_nonpos_iff.1 (hwT x)
    have hY0 : ∀ X, sed_Y (sed_Q d s N γ ρ) w X = 0 := by
      intro X
      have : w = fun _ => 0 := funext hw0
      subst this
      simp [sed_Y, pair]
    simp_rw [hY0]
    rcases Nat.eq_zero_or_pos q with hq | hq
    · subst hq; simp
    · have : 0 < 2 * q := by omega
      simp [zero_pow this.ne']
  -- `T > 0`
  set u : Torus d → ℝ := fun x => w x / T with hu
  have hum : Measurable u := hwm.div_const T
  have hub : ∀ x, |u x| ≤ 1 := fun x => by
    rw [hu]; simp only
    rw [abs_div, abs_of_pos hT, div_le_one hT]
    exact hwT x
  have hB7 := hCB u hum hub N hN
  set Zu : Config d N → ℝ := fun X => pair (empirical X) u - pair (withDensityReal ρ) u with hZu
  set Z : Config d N → ℝ := fun X => pair (empirical X) w - pair (withDensityReal ρ) w with hZ
  have hZZu : ∀ X, Z X = T * Zu X := by
    intro X
    simp only [hZ, hZu]
    rw [HRS.MC.SEdge.B4c.b4c_pair_empirical X hum, HRS.MC.SEdge.B4c.b4c_pair_empirical X hwm]
    simp only [pair, hu]
    rw [integral_div]
    simp only [← Finset.sum_div]
    field_simp
  have hZuM : Measurable Zu := ((s7b_pair_emp_meas hN hum).sub_const _)
  have hZuB : ∀ X, |Zu X| ≤ 2 * 1 := fun X => HRS.MC.SEdge.B7.b7_bound hN (withDensityReal ρ) hum hub X
  have hZ2int : Integrable (fun X => Zu X ^ (2 * q)) (sed_Q d s N γ ρ) := by
    refine Integrable.of_bound (hZuM.pow_const _).aestronglyMeasurable ((2 * 1) ^ (2 * q))
      (Filter.Eventually.of_forall fun X => ?_)
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hZuB X) _
  -- the bias
  set E : ℝ := ∫ X, pair (empirical X) w ∂(sed_Q d s N γ ρ) with hE
  have hbias : |E - pair (withDensityReal ρ) w| ≤ Cu * T / N := hCu w T hw hwT N hN
  have hYZ : ∀ X, sed_Y (sed_Q d s N γ ρ) w X =
      Real.sqrt N * Z X - Real.sqrt N * (E - pair (withDensityReal ρ) w) := by
    intro X
    simp only [sed_Y, hZ, hE]
    ring
  have hsqrt : Real.sqrt N * (Cu * T / N) ≤ Cu * T := by
    have : Real.sqrt N / N ≤ 1 := by
      rw [div_le_one hNp]
      have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      calc Real.sqrt N ≤ Real.sqrt N * Real.sqrt N := by
            have := Real.one_le_sqrt.2 h1
            nlinarith [Real.sqrt_nonneg (N : ℝ)]
        _ = N := Real.mul_self_sqrt hNp.le
    calc Real.sqrt N * (Cu * T / N) = (Real.sqrt N / N) * (Cu * T) := by ring
      _ ≤ 1 * (Cu * T) := mul_le_mul_of_nonneg_right this (by positivity)
      _ = Cu * T := one_mul _
  have hYb : ∀ X, |sed_Y (sed_Q d s N γ ρ) w X| ≤ Real.sqrt N * |Z X| + Cu * T := by
    intro X
    rw [hYZ X]
    calc |Real.sqrt N * Z X - Real.sqrt N * (E - pair (withDensityReal ρ) w)|
        ≤ |Real.sqrt N * Z X| + |Real.sqrt N * (E - pair (withDensityReal ρ) w)| := abs_sub _ _
      _ ≤ Real.sqrt N * |Z X| + Real.sqrt N * (Cu * T / N) := by
          rw [abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
          gcongr
      _ ≤ _ := by linarith
  have hpt : ∀ X, |sed_Y (sed_Q d s N γ ρ) w X| ^ (2 * q) ≤
      2 ^ (2 * q) * ((N : ℝ) ^ q * (T ^ (2 * q) * Zu X ^ (2 * q)) + (Cu * T) ^ (2 * q)) := by
    intro X
    calc |sed_Y (sed_Q d s N γ ρ) w X| ^ (2 * q)
        ≤ (Real.sqrt N * |Z X| + Cu * T) ^ (2 * q) :=
          pow_le_pow_left₀ (abs_nonneg _) (hYb X) _
      _ ≤ 2 ^ (2 * q) * ((Real.sqrt N * |Z X|) ^ (2 * q) + (Cu * T) ^ (2 * q)) :=
          s7b_add_pow_le _ _ (by positivity) (by positivity) _
      _ = _ := by
          have e1 : (Real.sqrt N * |Z X|) ^ (2 * q) = (N : ℝ) ^ q * (T ^ (2 * q) * Zu X ^ (2 * q)) := by
            rw [mul_pow, pow_mul, Real.sq_sqrt hNp.le, Even.pow_abs (even_two_mul q), hZZu X,
              mul_pow]
          rw [e1]
  have hRint : Integrable (fun X : Config d N =>
      2 ^ (2 * q) * ((N : ℝ) ^ q * (T ^ (2 * q) * Zu X ^ (2 * q)) + (Cu * T) ^ (2 * q)))
      (sed_Q d s N γ ρ) :=
    (((hZ2int.const_mul (T ^ (2 * q))).const_mul ((N : ℝ) ^ q)).add (integrable_const _)).const_mul _
  have hYm : Measurable (fun X : Config d N => |sed_Y (sed_Q d s N γ ρ) w X| ^ (2 * q)) := by
    have : Measurable (sed_Y (sed_Q d s N γ ρ) w : Config d N → ℝ) := by
      unfold sed_Y
      exact measurable_const.mul ((s7b_pair_emp_meas hN hwm).sub_const _)
    exact this.abs.pow_const _
  have hint_le : ∫ X, |sed_Y (sed_Q d s N γ ρ) w X| ^ (2 * q) ∂(sed_Q d s N γ ρ) ≤
      ∫ X, 2 ^ (2 * q) * ((N : ℝ) ^ q * (T ^ (2 * q) * Zu X ^ (2 * q)) + (Cu * T) ^ (2 * q))
        ∂(sed_Q d s N γ ρ) :=
    integral_mono_of_nonneg (Filter.Eventually.of_forall fun X => by positivity) hRint
      (Filter.Eventually.of_forall hpt)
  refine hint_le.trans ?_
  rw [integral_const_mul, integral_add ((hZ2int.const_mul (T ^ (2 * q))).const_mul ((N : ℝ) ^ q))
    (integrable_const _), integral_const_mul, integral_const_mul]
  have hc1 : ∫ _X : Config d N, (Cu * T) ^ (2 * q) ∂(sed_Q d s N γ ρ) = (Cu * T) ^ (2 * q) := by
    simp
  rw [hc1]
  have hNq : 0 < (N : ℝ) ^ q := by positivity
  have h1 : (N : ℝ) ^ q * (T ^ (2 * q) * ∫ X, Zu X ^ (2 * q) ∂(sed_Q d s N γ ρ)) ≤
      max CB 0 * T ^ (2 * q) := by
    have hB7' : ∫ X, Zu X ^ (2 * q) ∂(sed_Q d s N γ ρ) ≤ max CB 0 / (N : ℝ) ^ q :=
      hB7.trans (by gcongr; exact le_max_left _ _)
    calc (N : ℝ) ^ q * (T ^ (2 * q) * ∫ X, Zu X ^ (2 * q) ∂(sed_Q d s N γ ρ))
        ≤ (N : ℝ) ^ q * (T ^ (2 * q) * (max CB 0 / (N : ℝ) ^ q)) := by gcongr
      _ = max CB 0 * T ^ (2 * q) := by field_simp
  have hCT : (Cu * T) ^ (2 * q) = Cu ^ (2 * q) * T ^ (2 * q) := mul_pow _ _ _
  calc 2 ^ (2 * q) * ((N : ℝ) ^ q * (T ^ (2 * q) * ∫ X, Zu X ^ (2 * q) ∂(sed_Q d s N γ ρ)) +
        (Cu * T) ^ (2 * q))
      ≤ 2 ^ (2 * q) * (max CB 0 * T ^ (2 * q) + Cu ^ (2 * q) * T ^ (2 * q)) := by
        rw [hCT]; gcongr
    _ = 2 ^ (2 * q) * (max CB 0 + Cu ^ (2 * q)) * T ^ (2 * q) := by ring
    _ ≤ max 1 (2 ^ (2 * q) * (max CB 0 + Cu ^ (2 * q))) * T ^ (2 * q) := by
        gcongr
        exact le_max_right _ _

end HRS.MC.Sec7.S7b

end
