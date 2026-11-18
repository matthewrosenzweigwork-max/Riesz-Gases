import HRS.MS.S104eC0
import HRS.MS.WadAux19

/-!
# S104E route C, packet C1 (part D): the base case (`j = 0`) of the sup-norm gain for the Mehler semigroup

`s104c1_base`: for `g` continuous with `‖g‖ ≤ C`, `0 < τ ≤ T`: `P_τ g ∈ C¹`, `‖D P_τ g‖ ≤ K C τ^{-1/2}` and
`D P_τ g` is Lipschitz with constant `K C τ^{-1}` at scale `s₀ τ^{1/2}`.  (From `WadAux17-19`: Stein formula and
Lipschitz smoothing by Cameron-Martin, with the weight exponent `M = 0`.)
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ContDiff

namespace HRS.MS.S104e.C
open HRS HRS.Whole HRS.MS.Wad
variable {d : ℕ}

theorem s104c1_base (a ν T : ℝ) (ha : 0 < a) (hν : 0 < ν) :
    ∃ K s0 : ℝ, 0 ≤ K ∧ 0 < s0 ∧ ∀ {g : Euc d → ℝ} {C : ℝ}, Continuous g → (∀ y, ‖g y‖ ≤ C) →
      ∀ {τ : ℝ}, 0 < τ → τ ≤ T →
        ContDiff ℝ 1 (s83_P a ν τ g) ∧
        (∀ x, ‖fderiv ℝ (s83_P a ν τ g) x‖ ≤ K * C * (Real.sqrt τ)⁻¹) ∧
        ∀ x x' : Euc d, ‖x' - x‖ ≤ s0 * Real.sqrt τ →
          ‖fderiv ℝ (s83_P a ν τ g) x' - fderiv ℝ (s83_P a ν τ g) x‖ ≤ K * C * τ⁻¹ * ‖x' - x‖ := by
  set σ₀ : ℝ := Real.sqrt (ν / a) with hσ₀
  set K₁ : ℝ := s84_K1 d 0 a ν T with hK₁
  have hK₁0 : 0 ≤ K₁ := s84_K1_nonneg 0 ha hν
  set Pm : ℝ := Real.sqrt (mom d (2 * 0) σ₀) with hPm
  have hPm0 : 0 ≤ Pm := Real.sqrt_nonneg _
  set sT : ℝ := s84_sT a ν T with hsT
  have hsT0 : 0 < sT := s84_sT_pos hν
  set s' : ℝ := sT / Real.sqrt 2 with hs'
  have hs'0 : 0 < s' := by positivity
  set R : ℝ := K₁ * Real.sqrt 2 * Pm * 2 / s' with hR
  have hR0 : 0 ≤ R := by positivity
  refine ⟨max K₁ R, s', le_max_of_le_left hK₁0, hs'0, ?_⟩
  intro g C hg hgC τ hτ0 hτT
  have hw : Wt 0 C g := fun x => by simpa using hgC x
  have hC : 0 ≤ C := (norm_nonneg _).trans (hgC 0)
  obtain ⟨hC1, hD⟩ := s84_P_fderiv (T := T) ha hν (le_refl (0 : ℝ)) hg hw hτ0 hτT
  have hsq : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ0
  refine ⟨hC1, fun x => ?_, fun x x' hxx => ?_⟩
  · refine (hD x).trans ?_
    simp only [Real.rpow_zero, mul_one]
    have : 0 ≤ C * (Real.sqrt τ)⁻¹ := by positivity
    nlinarith [le_max_left K₁ R]
  · set δ : ℝ := ‖x' - x‖ with hδ
    have hδ0 : 0 ≤ δ := norm_nonneg _
    have hh0 : 0 < τ / 2 := by positivity
    have hhT : τ / 2 ≤ T := by linarith
    have hsqh : Real.sqrt (τ / 2) = Real.sqrt τ / Real.sqrt 2 := Real.sqrt_div hτ0.le 2
    have hsq2 : 0 < Real.sqrt 2 := by positivity
    obtain ⟨hfC1, hfD⟩ := s84_P_fderiv (T := T) ha hν (le_refl (0 : ℝ)) hg hw hh0 hhT
    have hfw : Wt 0 (C * 2 ^ (0 : ℝ) * mom d 0 σ₀) (s83_P a ν (τ / 2) g) :=
      s83_P_wt hg le_rfl hw ha hν.le hh0.le
    have hfDw : Wt 0 (K₁ * C * (Real.sqrt (τ / 2))⁻¹) (fderiv ℝ (s83_P a ν (τ / 2) g)) := hfD
    have hsplit : s83_P a ν τ g =
        s83_G (s83_mc a (τ / 2)) (s83_ms a ν (τ / 2)) (s83_P a ν (τ / 2) g) := by
      have := s83_P_add hg (le_refl (0 : ℝ)) hw ha hν.le hh0.le hh0.le (a := a) (ν := ν)
      rw [show τ / 2 + τ / 2 = τ by ring] at this
      exact this
    have hc1 : |s83_mc a (τ / 2)| ≤ 1 := s83_abs_mc_le_one ha.le hh0.le
    have hσ1 : |s83_ms a ν (τ / 2)| ≤ σ₀ := s83_abs_ms_le ha hν.le hh0.le
    have hσ0 : s83_ms a ν (τ / 2) ≠ 0 := (s83_ms_pos ha hν hh0).ne'
    have hσlow : sT * Real.sqrt (τ / 2) ≤ s83_ms a ν (τ / 2) := s84_ms_lower ha hν hh0.le hhT
    have hς0 : 0 < s' * Real.sqrt τ := by positivity
    have hςeq : sT * Real.sqrt (τ / 2) = s' * Real.sqrt τ := by
      rw [hsqh, hs']; field_simp
    have hςσ : s' * Real.sqrt τ ≤ s83_ms a ν (τ / 2) := by rw [← hςeq]; exact hσlow
    have hσpos : 0 < s83_ms a ν (τ / 2) := lt_of_lt_of_le hς0 hςσ
    have hκ : (|s83_mc a (τ / 2)| / |s83_ms a ν (τ / 2)|) * ‖x' - x‖ ≤ δ / (s' * Real.sqrt τ) := by
      rw [abs_of_pos hσpos]
      calc |s83_mc a (τ / 2)| / s83_ms a ν (τ / 2) * ‖x' - x‖
          ≤ 1 / (s' * Real.sqrt τ) * ‖x' - x‖ := by
            refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
            calc |s83_mc a (τ / 2)| / s83_ms a ν (τ / 2) ≤ 1 / s83_ms a ν (τ / 2) :=
                  div_le_div_of_nonneg_right hc1 hσpos.le
              _ ≤ 1 / (s' * Real.sqrt τ) := one_div_le_one_div_of_le hς0 hςσ
        _ = δ / (s' * Real.sqrt τ) := by rw [hδ]; ring
    have hu1 : δ / (s' * Real.sqrt τ) ≤ 1 := by rw [div_le_one hς0]; exact hxx
    have hlip := s84_clm_lip hfC1 (le_refl (0 : ℝ)) hfw hfDw hc1 hσ1 hσ0 x x' (hκ.trans hu1)
    rw [hsplit]
    refine hlip.trans ?_
    simp only [Real.rpow_zero, mul_one]
    rw [← hPm, hsqh]
    have hq : Real.sqrt τ * Real.sqrt τ = τ := Real.mul_self_sqrt hτ0.le
    have hb : K₁ * C * (Real.sqrt τ / Real.sqrt 2)⁻¹ * Pm * (2 * ((|s83_mc a (τ / 2)| / |s83_ms a ν (τ / 2)|) * ‖x' - x‖))
        ≤ K₁ * C * (Real.sqrt τ / Real.sqrt 2)⁻¹ * Pm * (2 * (δ / (s' * Real.sqrt τ))) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      linarith
    refine hb.trans ?_
    have e : K₁ * C * (Real.sqrt τ / Real.sqrt 2)⁻¹ * Pm * (2 * (δ / (s' * Real.sqrt τ))) =
        R * C * τ⁻¹ * δ := by
      rw [hR, show τ⁻¹ = (Real.sqrt τ * Real.sqrt τ)⁻¹ by rw [hq]]
      field_simp
    rw [e]
    have : 0 ≤ C * τ⁻¹ * δ := by positivity
    nlinarith [le_max_right K₁ R]

end HRS.MS.S104e.C
