import HRS.Whole.HeadlineStatement
import HRS.MH.CoercLowerFinal
import HRS.MS.QsfCorr3
import HRS.MS.MovThermAux1

/-!
# S21 packet A: the completion clause of S2.1 (i) and (ii)

Clause 1 of `HRS.Whole.whole_space_stationary` (and of `whole_space_prepared`): there is a constant `C0` with
`0 <= F_N(X, rho) + oN d s C0 N` for all `N >= 2` and all collision-free `X`, for every thermal equilibrium `rho_beta`
(resp. every `rho t` of an `IsResultingSolution`).

* `s21_oN_mono`: `oN d s C0 N` is monotone in `C0` (so the clause holds for every `C0 >=` a threshold).
* `s21_completion_of_bounded`: for a probability density `rho <= Lam` (with the first logarithmic moment at `s = 0`)
  `0 <= rieszModulatedEnergy d s X (HRS.Whole.withDensityReal rho) + oN d s C0 N` for all `C0 >= C0min(d, s, Lam)`;
  from `MH.CoercLower.completionNonnegRd_exists` and `oNΛ_le_oN` (`oNΛ = oN` with an enlarged constant).
* `s21_thermal_bounded`: the thermal equilibrium is a probability density bounded by a constant `Lam(d,s,a,beta)`
  with the first logarithmic moment (`S45.s45_thermal_data`, `S45.s45_thermal_logmoment2`, `Mov0.mv0_rho_eq`).
* `s21_clause1_stationary`: clause 1 of (i), for all `C0 >=` a threshold.
* `s21_clause1_resulting`: clause 1 of (ii) for `rho` with `IsResultingSolution` (only the clauses `global` and `ratio` are used).

Junk-value audit.  `oN` has the term `if s = 0 then log N / (2dN)`, no junk for `N >= 2`.  The log moment hypothesis is
genuine (Bochner integrals in the interaction energy are junk without it), supplied by Gaussian decay.  Everything is
proved without any open row (S6.3 is not used: `IsResultingSolution` is a hypothesis).
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.MS.S21

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s21_oN_mono {s : ℝ} {C₀ C₀' : ℝ} (h : C₀ ≤ C₀') (N : ℕ) :
    HRS.oN d s C₀ N ≤ HRS.oN d s C₀' N := by
  unfold HRS.oN
  have hx : 0 ≤ (N : ℝ) ^ (s / d - 1) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  nlinarith [mul_le_mul_of_nonneg_right h hx]

theorem s21_completion_of_bounded (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (Λ : ℝ) :
    ∃ C₀min : ℝ, 0 ≤ C₀min ∧ ∀ C₀ : ℝ, C₀min ≤ C₀ → ∀ N : ℕ, 2 ≤ N → ∀ ρ : Euc d → ℝ,
      HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
      (s = 0 → Integrable (fun x : Euc d => Real.log (2 + ‖x‖)) (HRS.Whole.withDensityReal ρ)) →
      ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
        0 ≤ rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ρ) + HRS.oN d s C₀ N := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨C₁, hC₁, hcomp⟩ := HRS.MH.CoercLower.completionNonnegRd_exists hd1 hs0 hsd
  have hC := hcomp C₁ le_rfl
  have hΛ1 : 1 ≤ max Λ 1 := le_max_right _ _
  obtain ⟨-, C₂, hC₂, hC₂le⟩ := HRS.oNΛ_le_oN hd1 hs0 hsd C₁ hC₁ (max Λ 1) hΛ1
  refine ⟨C₂, hC₂, fun C₀ hC₀ N hN ρ hρ hρΛ hlog X hX => ?_⟩
  have h1 := hC.2 (max Λ 1) hΛ1 N hN ρ hρ (fun x => (hρΛ x).trans (le_max_left _ _)) hlog X hX
  have h2 := hC₂le N hN
  have h3 := s21_oN_mono (d := d) (s := s) hC₀ N
  linarith

theorem s21_thermal_bounded (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) :
    ∃ Λ : ℝ, ∀ ρ : Euc d → ℝ, IsThermalEquilibrium d s a β ρ → HRS.Whole.IsProbDensity ρ ∧ (∀ x, ρ x ≤ Λ) ∧
      Integrable (fun x : Euc d => Real.log (2 + ‖x‖)) (HRS.Whole.withDensityReal ρ) := by
  obtain ⟨C, c, BU, hT⟩ := S45.s45_thermal_data hd hs0 hsd ha hβ
  obtain ⟨L, hL⟩ := S45.s45_thermal_logmoment2 hT
  refine ⟨C, fun ρ hρ => ?_⟩
  have hρeq : ρ = thermalDensity d s a β := HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ
  subst hρeq
  have hprob := hT.prob
  refine ⟨hprob, fun x => ?_, ?_⟩
  · exact (le_abs_self _).trans ((hT.h0 x).trans
      (mul_le_of_le_one_right hT.C0 (by
        rw [Real.exp_le_one_iff]
        have := sq_nonneg ‖x‖
        nlinarith [hT.hc])))
  · have hμ : HRS.Whole.withDensityReal (thermalDensity d s a β) = thermalMeasure d s a β := rfl
    rw [hμ]
    have hfin : IsFiniteMeasure (thermalMeasure d s a β) := by
      have : IsProbabilityMeasure (thermalMeasure d s a β) := by
        refine ⟨?_⟩
        show HRS.Whole.withDensityReal (thermalDensity d s a β) Set.univ = 1
        unfold HRS.Whole.withDensityReal
        rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
          ← ofReal_integral_eq_lintegral_ofReal]
        · rw [hprob.integral_one]; simp
        · have : Integrable (thermalDensity d s a β) := by
            by_contra hni
            have := hprob.integral_one
            rw [integral_undef hni] at this
            exact zero_ne_one this
          exact this
        · exact Filter.Eventually.of_forall hprob.nonneg
      infer_instance
    have hm : Measurable fun x : Euc d => Real.log (2 + ‖x‖) :=
      Real.measurable_log.comp (measurable_const.add measurable_norm)
    refine Integrable.mono' (hL.1.add (integrable_const (1 : ℝ))) hm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => ?_)
    have hn := norm_nonneg x
    have hl0 : 0 ≤ Real.log (2 + ‖x‖) := Real.log_nonneg (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg hl0]
    simp only [Pi.add_apply]
    nlinarith [sq_nonneg (Real.log (2 + ‖x‖) - 1)]

theorem s21_clause1_stationary (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) :
    ∃ C₀min : ℝ, 0 ≤ C₀min ∧ ∀ C₀ : ℝ, C₀min ≤ C₀ → ∀ ρβ : Euc d → ℝ,
      IsThermalEquilibrium d s a β ρβ → ∀ N : ℕ, 2 ≤ N → ∀ X : EucConfig d N,
        X ∉ eucCollisionSet d N →
          0 ≤ rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ρβ) + HRS.oN d s C₀ N := by
  obtain ⟨Λ, hΛ⟩ := s21_thermal_bounded hd hs0 hsd ha hβ
  obtain ⟨C₀min, h0, h⟩ := s21_completion_of_bounded hd hs0 hsd Λ
  refine ⟨C₀min, h0, fun C₀ hC₀ ρβ hρβ N hN X hX => ?_⟩
  obtain ⟨hp, hb, hl⟩ := hΛ ρβ hρβ
  exact h C₀ hC₀ N hN ρβ hp hb (fun _ => hl) X hX

theorem s21_clause1_resulting (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) (C₁ : ℝ) :
    ∃ C₀min : ℝ, 0 ≤ C₀min ∧ ∀ C₀ : ℝ, C₀min ≤ C₀ → ∀ ρβ : Euc d → ℝ,
      IsThermalEquilibrium d s a β ρβ → ∀ (εstar ε : ℝ) (ψ : Euc d → ℝ) (c₁ : ℝ)
        (ρ : ℝ → Euc d → ℝ), IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ →
        ∀ N : ℕ, 2 ≤ N → ∀ t : ℝ, 0 ≤ t → ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
          0 ≤ rieszModulatedEnergy d s X (HRS.Whole.withDensityReal (ρ t)) + HRS.oN d s C₀ N := by
  obtain ⟨Λ, hΛ⟩ := s21_thermal_bounded hd hs0 hsd ha hβ
  obtain ⟨C₀min, h0, h⟩ := s21_completion_of_bounded hd hs0 hsd (max C₁ 0 * |Λ|)
  refine ⟨C₀min, h0, fun C₀ hC₀ ρβ hρβ εstar ε ψ c₁ ρ hR N hN t ht X hX => ?_⟩
  obtain ⟨hp, hb, hl⟩ := hΛ ρβ hρβ
  have hprob : HRS.Whole.IsProbDensity (ρ t) := (hR.global t).density t ⟨ht, le_rfl⟩
  have hle : ∀ x, ρ t x ≤ C₁ * ρβ x := fun x => (hR.ratio t ht x).2
  have hbd : ∀ x, ρ t x ≤ max C₁ 0 * |Λ| := fun x => by
    have h1 : ρ t x ≤ max C₁ 0 * ρβ x := by
      refine (hle x).trans ?_
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (hp.nonneg x)
    refine h1.trans (mul_le_mul_of_nonneg_left ((hb x).trans (le_abs_self _)) (le_max_right _ _))
  refine h C₀ hC₀ N hN (ρ t) hprob hbd (fun _ => ?_) X hX
  -- the logarithmic moment: `rho t <= max C1 0 * rho_beta`
  have hdom : HRS.Whole.withDensityReal (ρ t) ≤ ENNReal.ofReal (max C₁ 0) • HRS.Whole.withDensityReal ρβ := by
    refine Measure.le_iff.2 fun A hA => ?_
    unfold HRS.Whole.withDensityReal
    rw [Measure.smul_apply, withDensity_apply _ hA, withDensity_apply _ hA,
      smul_eq_mul, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun x => ?_
    rw [← ENNReal.ofReal_mul (le_max_right _ _)]
    refine ENNReal.ofReal_le_ofReal ?_
    refine (hle x).trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (hp.nonneg x)
  exact (hl.smul_measure ENNReal.ofReal_ne_top).mono_measure hdom

end HRS.MS.S21
