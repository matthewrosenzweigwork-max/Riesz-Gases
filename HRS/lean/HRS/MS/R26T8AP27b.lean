import HRS.MS.R26T8AP27a

/-!
# S8.2 local Newton layer, packet T8A.P27 (part b): Fubini for the time integral of centered kernels
`r26t8a_p27_fub`: if `g t` is continuous for `t > 0`, `g . v` is continuous on `(0,oo)`, `|g t v| <= b t B v` with `b` integrable on
`(0,oo)` and `B` `mu`-integrable, and each `g t` has `mu`-mean zero, then so has `v |-> int_0^oo g t v dt`.
Joint measurability comes from the truncations `g (max t (1/(n+1))) v` (continuous in `t`, measurable in `v`).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

theorem r26t8a_p27_fub {d : ℕ} {μ : Measure (Euc d)} [SFinite μ] (g : ℝ → Euc d → ℝ) {b : ℝ → ℝ} {B : Euc d → ℝ}
    (hb : IntegrableOn b (Set.Ioi 0)) (hb0 : ∀ t, 0 ≤ b t) (hB : Integrable B μ) (hB0 : ∀ v, 0 ≤ B v)
    (hcd : ∀ t, 0 < t → Continuous (g t)) (hct : ∀ v, ContinuousOn (fun t => g t v) (Set.Ioi 0))
    (hbd : ∀ t, 0 < t → ∀ v, |g t v| ≤ b t * B v)
    (hcen : ∀ t, 0 < t → ∫ v, g t v ∂μ = 0) :
    ∫ v, (∫ t in Set.Ioi (0 : ℝ), g t v) ∂μ = 0 := by
  classical
  set G : ℝ × Euc d → ℝ := fun p => if 0 < p.1 then g p.1 p.2 else 0 with hG
  have hGn : ∀ n : ℕ, Measurable (fun p : ℝ × Euc d =>
      if 0 < p.1 then g (max p.1 (1 / ((n : ℝ) + 1))) p.2 else 0) := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    have hm : Measurable (Function.uncurry fun (t : ℝ) (v : Euc d) => g (max t (1 / ((n : ℝ) + 1))) v) := by
      refine measurable_uncurry_of_continuous_of_measurable (fun v => ?_) (fun t => ?_)
      · exact (hct v).comp_continuous (continuous_id.max continuous_const)
          (fun t => lt_max_of_lt_right hpos)
      · exact (hcd _ (lt_max_of_lt_right hpos)).measurable
    exact Measurable.ite (measurableSet_lt measurable_const measurable_fst) hm measurable_const
  have hGm : Measurable G := by
    refine measurable_of_tendsto_metrizable hGn (tendsto_pi_nhds.2 fun p => ?_)
    by_cases hp : 0 < p.1
    · simp only [hp, if_true, hG]
      refine tendsto_const_nhds.congr' ?_
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / p.1)
      filter_upwards [eventually_ge_atTop N] with n hn
      have h1 : 1 / ((n : ℝ) + 1) ≤ p.1 := by
        rw [div_le_iff₀ (by positivity)]
        have : 1 / p.1 < n + 1 := by
          have : (N : ℝ) ≤ n := by exact_mod_cast hn
          linarith
        rw [div_lt_iff₀ hp] at this
        linarith
      rw [max_eq_left h1]
    · simp only [hp, if_false, hG]
      exact tendsto_const_nhds
  set ν : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ)) with hν
  have hf : Integrable (Function.uncurry fun (v : Euc d) (t : ℝ) => G (t, v)) (μ.prod ν) := by
    refine Integrable.mono' (hB.mul_prod hb) ?_ ?_
    · exact (hGm.comp measurable_swap).aestronglyMeasurable
    · refine Eventually.of_forall fun p => ?_
      simp only [Function.uncurry, hG, Real.norm_eq_abs]
      split_ifs with h
      · rw [mul_comm]; exact hbd _ h _
      · simp only [abs_zero]; exact mul_nonneg (hB0 _) (hb0 _)
  have hswap := integral_integral_swap hf
  have hL : ∀ v, ∫ t, G (t, v) ∂ν = ∫ t in Set.Ioi (0 : ℝ), g t v := fun v =>
    setIntegral_congr_fun measurableSet_Ioi (fun t ht => by simp only [hG, if_pos (Set.mem_Ioi.1 ht)])
  have hR : ∀ᵐ t ∂ν, ∫ v, G (t, v) ∂μ = 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : 0 < t := ht
    simp only [hG, if_pos ht']
    exact hcen t ht'
  have h2 : ∫ t, ∫ v, G (t, v) ∂μ ∂ν = 0 := by
    rw [integral_congr_ae hR]; simp
  simp only [hL] at hswap
  rw [hswap]
  exact h2

end HRS.MS.R26T8A
