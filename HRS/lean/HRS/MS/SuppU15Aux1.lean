import HRS.Whole.Adjoint
import HRS.Commutator.Whole.Bridge

/-!
# U15 auxiliary lemmas: the weighted bound on a density gives a pointwise bound and a log moment
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.SuppU15

open HRS HRS.Whole

variable {d : ℕ}

/-- The `j = 0` term of `weightedSupE`: `⟨x⟩^L |f x| ≤ max Λ 0`. -/
lemma u15_weighted_zero {k : ℕ} {L Λ : ℝ} {f : Euc d → ℝ}
    (h : weightedSupE k L f ≤ ENNReal.ofReal Λ) (x : Euc d) :
    jbracket x ^ L * |f x| ≤ max Λ 0 := by
  have h1 : ENNReal.ofReal (jbracket x ^ L * |f x|) ≤ weightedSupE k L f := by
    unfold weightedSupE derivSupE
    refine le_iSup_of_le (0 : Fin (k + 1)) (le_iSup_of_le (fun l => (Fin.elim0 (by simpa using l) : Fin d)) (le_iSup_of_le x ?_))
    have key : ∀ (j : ℕ) (hj : j = 0) (i : Fin j → Fin d), partialDeriv i f x = f x := by
      intro j hj i
      subst hj
      unfold partialDeriv
      rw [iteratedFDeriv_zero_apply]
    have : partialDeriv (fun l : Fin (((0 : Fin (k + 1)) : ℕ)) => (Fin.elim0 (by simpa using l) : Fin d)) f x = f x :=
      key _ (by simp) _
    rw [this]
  have h2 := h1.trans h
  have h3 : ENNReal.ofReal (jbracket x ^ L * |f x|) ≤ ENNReal.ofReal (max Λ 0) :=
    h2.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  exact (ENNReal.ofReal_le_ofReal_iff (le_max_right _ _)).1 h3

lemma u15_one_le_jbracket (x : Euc d) : 1 ≤ jbracket x := by
  unfold jbracket
  rw [Real.one_le_sqrt]
  nlinarith [sq_nonneg ‖x‖]

lemma u15_dens_le {L : ℝ} (hL : 0 ≤ L) {ρ : Euc d → ℝ} {B : ℝ} (hρ : ∀ x, 0 ≤ ρ x)
    (h : ∀ x, jbracket x ^ L * |ρ x| ≤ B) (x : Euc d) : ρ x ≤ B := by
  have h1 : 1 ≤ jbracket x ^ L := Real.one_le_rpow (u15_one_le_jbracket x) hL
  have := h x
  rw [abs_of_nonneg (hρ x)] at this
  nlinarith [hρ x]

/-- A bounded-by-`⟨x⟩^{-L}` probability density, `L > d + 1`, has a log moment bounded by a constant
depending only on `d, L, Λ`. -/
lemma u15_logmoment {L : ℝ} (hL : (d : ℝ) + 1 < L) (Λ : ℝ) :
    ∃ Lm : ℝ, ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, jbracket x ^ L * |ρ x| ≤ max Λ 0) →
      HRS.Whole.HasLogMoment (HRS.Whole.withDensityReal ρ) Lm := by
  have hr : ((Module.finrank ℝ (Euc d) : ℕ) : ℝ) < L - 1 := by
    rw [finrank_euclideanSpace_fin]; linarith
  have hGi : Integrable (fun x : Euc d => max Λ 0 * 2 ^ (L / 2) * (1 + ‖x‖) ^ (-(L - 1))) :=
    (integrable_one_add_norm hr).const_mul _
  refine ⟨∫ x : Euc d, max Λ 0 * 2 ^ (L / 2) * (1 + ‖x‖) ^ (-(L - 1)), ?_⟩
  intro ρ hρ hb
  have hL0 : 0 < L := by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  -- pointwise domination
  have hpt : ∀ x : Euc d, ρ x * Real.log (2 + ‖x‖) ≤ max Λ 0 * 2 ^ (L / 2) * (1 + ‖x‖) ^ (-(L - 1)) := by
    intro x
    have hx0 := norm_nonneg x
    have h1 : ρ x ≤ max Λ 0 * jbracket x ^ (-L) := by
      have hjpos : 0 < jbracket x := lt_of_lt_of_le one_pos (u15_one_le_jbracket x)
      have := hb x
      rw [abs_of_nonneg (hρ.nonneg x)] at this
      rw [Real.rpow_neg hjpos.le, ← div_eq_mul_inv, le_div_iff₀ (Real.rpow_pos_of_pos hjpos L)]
      linarith
    have h2 : jbracket x ^ (-L) ≤ 2 ^ (L / 2) * (1 + ‖x‖) ^ (-L) := by
      have := rpow_neg_one_add_norm_sq_le x hL0
      have e : jbracket x ^ (-L) = ((1 : ℝ) + ‖x‖ ^ 2) ^ (-L / 2) := by
        unfold jbracket
        rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by positivity)]
        congr 1; ring
      rw [e]; exact this
    have h3 : Real.log (2 + ‖x‖) ≤ 1 + ‖x‖ := by
      have := Real.log_le_sub_one_of_pos (show 0 < 2 + ‖x‖ by positivity)
      linarith
    have hlog0 : 0 ≤ Real.log (2 + ‖x‖) := Real.log_nonneg (by linarith)
    have hpow : (1 + ‖x‖) ^ (-(L - 1)) = (1 + ‖x‖) ^ (-L) * (1 + ‖x‖) := by
      have : -(L - 1) = -L + 1 := by ring
      rw [this, Real.rpow_add (by positivity), Real.rpow_one]
    have hM : 0 ≤ max Λ 0 := le_max_right _ _
    calc ρ x * Real.log (2 + ‖x‖) ≤ (max Λ 0 * (2 ^ (L / 2) * (1 + ‖x‖) ^ (-L))) * (1 + ‖x‖) := by
          apply mul_le_mul _ h3 hlog0 (by positivity)
          exact h1.trans (mul_le_mul_of_nonneg_left h2 hM)
      _ = _ := by rw [hpow]; ring
  have hcont : Continuous fun x : Euc d => Real.log (2 + ‖x‖) :=
    (continuous_const.add continuous_norm).log (fun x => by show (2 + ‖x‖) ≠ 0; positivity)
  have hmeas : Measurable fun x : Euc d => ρ x * Real.log (2 + ‖x‖) :=
    hρ.measurable.mul hcont.measurable
  have hint : Integrable (fun x : Euc d => ρ x * Real.log (2 + ‖x‖)) := by
    refine hGi.mono' hmeas.aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    have hlog0 : 0 ≤ Real.log (2 + ‖x‖) := Real.log_nonneg (by linarith [norm_nonneg x])
    rw [Real.norm_of_nonneg (mul_nonneg (hρ.nonneg x) hlog0)]
    exact hpt x
  unfold HRS.Whole.HasLogMoment HRS.Whole.withDensityReal
  refine ⟨?_, ?_⟩
  · rw [integrable_withDensity_iff_integrable_smul' hρ.measurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    refine hint.congr (Eventually.of_forall fun x => ?_)
    simp [ENNReal.toReal_ofReal (hρ.nonneg x)]
  · rw [integral_withDensity_eq_integral_toReal_smul₀ hρ.measurable.ennreal_ofReal.aemeasurable
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    have e : ∫ x : Euc d, (ENNReal.ofReal (ρ x)).toReal • Real.log (2 + ‖x‖) =
        ∫ x : Euc d, ρ x * Real.log (2 + ‖x‖) :=
      integral_congr_ae (Eventually.of_forall fun x => by
        simp [ENNReal.toReal_ofReal (hρ.nonneg x)])
    rw [e]
    exact integral_mono hint hGi hpt

end HRS.MS.SuppU15
