import HRS.MS.R2WinOrbAux9

/-!
# S10.3 (stationary half), part 10: one cosine coefficient of a jet along a family with two terminal-time derivatives

Prefix `s103_`, namespace `HRS.MS.R2WinOrb`.  For a family `F a t` (`a ≤ 2`) of `C^k` functions with `C^j`-sup difference quotients
`h⁻¹(F a (t+h) - F a t) → F (a+1) t` and uniform bounds `A` on `D^jF a t` (`j ≤ k`), the `j`-th jet of `x ↦ ∫_0^T e_n(u) F 0 (b+u)(x) du` at `x`
is bounded by `s103_cosBound T A n`:
* `n = 0`: `T A / √T`;
* `n ≥ 1`: `√(2/T) (2A + TA)/λ²`, `λ = nπ/T` (two integrations by parts, `s103_ibp`).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R2WinOrb

open HRS HRS.Whole

variable {d : ℕ}

/-- The bound for the `n`-th cosine coefficient. -/
def s103_cosBound (T A : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then T * (1 / Real.sqrt T) * A else Real.sqrt (2 / T) * ((2 * A + T * A) / ((n : ℝ) * Real.pi / T) ^ 2)

theorem s103_cos_abs_le {T : ℝ} (hT : 0 < T) (n : ℕ) (u : ℝ) :
    |r2CosBasis T n u| ≤ if n = 0 then 1 / Real.sqrt T else Real.sqrt (2 / T) := by
  unfold r2CosBasis
  by_cases hn : n = 0
  · simp only [hn, if_true]
    rw [abs_of_pos (one_div_pos.2 (Real.sqrt_pos.2 hT))]
  · simp only [hn, if_false]
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    calc Real.sqrt (2 / T) * |Real.cos (n * Real.pi * u / T)| ≤ Real.sqrt (2 / T) * 1 :=
          mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (Real.sqrt_nonneg _)
      _ = _ := mul_one _

theorem s103_cosBasis_continuous (T : ℝ) (n : ℕ) : Continuous (r2CosBasis T n) := by
  unfold r2CosBasis
  by_cases hn : n = 0
  · simp only [hn, if_true]; exact continuous_const
  · simp only [hn, if_false]; fun_prop

theorem s103_hasDeriv_val {Fa Fb : ℝ → Euc d → ℝ} {T0 : ℝ}
    (hcdA : ∀ τ ∈ Set.Icc (0 : ℝ) T0, ContDiff ℝ ((0 : ℕ) : WithTop ℕ∞) (Fa τ))
    (hcdB : ∀ τ ∈ Set.Icc (0 : ℝ) T0, ContDiff ℝ ((0 : ℕ) : WithTop ℕ∞) (Fb τ))
    (hdiff : ∀ t ∈ Set.Icc (0 : ℝ) T0, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ, h ≠ 0 → |h| < δ →
      t + h ∈ Set.Icc (0 : ℝ) T0 → ∀ x : Euc d,
        ‖iteratedFDeriv ℝ 0 (fun y => h⁻¹ * (Fa (t + h) y - Fa t y) - Fb t y) x‖ ≤ ε) (x : Euc d) :
    ∀ t ∈ Set.Icc (0 : ℝ) T0, HasDerivWithinAt (fun τ => Fa τ x) (Fb t x) (Set.Icc 0 T0) t := by
  intro t ht
  rw [hasDerivWithinAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro c hc
  obtain ⟨δ, hδ, hδ'⟩ := hdiff t ht c hc
  have hev : ∀ᶠ t' in 𝓝[Set.Icc 0 T0] t, t' ∈ Set.Icc (0 : ℝ) T0 ∧ |t' - t| < δ := by
    refine eventually_nhdsWithin_iff.2 ?_
    filter_upwards [Metric.ball_mem_nhds t hδ] with t' ht' hmem
    exact ⟨hmem, by simpa [Real.dist_eq] using ht'⟩
  filter_upwards [hev] with t' ⟨ht'm, ht'd⟩
  by_cases h0 : t' - t = 0
  · have : t' = t := by linarith
    subst this; simp
  · have ht'm' : t + (t' - t) ∈ Set.Icc (0 : ℝ) T0 := by simpa using ht'm
    have hq := hδ' (t' - t) h0 ht'd ht'm' x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at hq
    simp only [add_sub_cancel] at hq
    have e : Fa t' x - Fa t x - (t' - t) • Fb t x =
        (t' - t) * ((t' - t)⁻¹ * (Fa t' x - Fa t x) - Fb t x) := by
      field_simp
      simp [smul_eq_mul]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, e, abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right hq (abs_nonneg _)

end HRS.MS.R2WinOrb

end
