import HRS.PDE.TorusFPExistAux7

/-!
# D1 existence, helper 8: narrow continuity of `t ↦ μ_t`
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS

variable {n : ℕ}

section Narrow

variable (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
  (μ₀ : Measure (Torus n)) [IsProbabilityMeasure μ₀]

theorem d1_narrow_smooth {ψ : Torus n → ℝ} (hψ : Torus.IsSmooth ψ) (T : ℝ) :
    ContinuousOn (fun t => ∫ x, ψ x ∂(d1_mu hn hκ hU μ₀ t)) (Set.Icc 0 T) := by
  rcases lt_or_ge 0 T with hT | hT
  · have hs := d1_sol_spec hn hκ hU hT hψ
    set f := d1_sol hn hκ hU T ψ with hf
    let ι : Set.Icc (0 : ℝ) T × Torus n → Set.Icc (0 : ℝ) T × Torus n := fun p =>
      (⟨T - p.1, by linarith [p.1.2.2], by linarith [p.1.2.1]⟩, p.2)
    have hι : Continuous ι :=
      Continuous.prodMk (Continuous.subtype_mk (continuous_const.sub (continuous_subtype_val.comp
        continuous_fst)) _) continuous_snd
    have hcont : Continuous (Function.uncurry fun (t : Set.Icc (0 : ℝ) T) (x : Torus n) =>
        f (T - t) x) := by
      have := hs.continuous_joint.comp hι
      exact this
    have h1 := continuous_parametric_integral_of_continuous (μ := μ₀) hcont
      (isCompact_univ (X := Torus n))
    rw [continuousOn_iff_continuous_restrict]
    refine (h1.congr fun t => ?_)
    simp only [Measure.restrict_univ, Set.restrict_apply]
    rw [d1_mu_integral hn hκ hU μ₀ t.2.1 hψ]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    exact (d1_P_eq hn hκ hU hT hψ hs t.2 x).symm
  · have : Set.Icc (0 : ℝ) T ⊆ {0} := fun t ht => by
      have : t = 0 := le_antisymm (ht.2.trans hT) ht.1
      simp [this]
    exact (continuousOn_singleton _ _).mono this

theorem d1_exists_smooth_seq {g : Torus n → ℝ} (hg : Continuous g) (k : ℕ) :
    ∃ ψ : Torus n → ℝ, Torus.IsSmooth ψ ∧ ∀ x, |g x - ψ x| ≤ 1 / ((k : ℝ) + 1) :=
  d1_exists_smooth_approx hg (by positivity)

theorem d1_narrow {g : Torus n → ℝ} (hg : Continuous g) (T : ℝ) :
    ContinuousOn (fun t => ∫ x, g x ∂(d1_mu hn hκ hU μ₀ t)) (Set.Icc 0 T) := by
  choose ψ hψ hψg using d1_exists_smooth_seq hg
  have hunif : TendstoUniformlyOn (fun (k : ℕ) t => ∫ x, ψ k x ∂(d1_mu hn hκ hU μ₀ t))
      (fun t => ∫ x, g x ∂(d1_mu hn hκ hU μ₀ t)) atTop (Set.Icc 0 T) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    filter_upwards [eventually_ge_atTop N] with k hk t _
    have := d1_mu_prob hn hκ hU μ₀ t
    have hk' : 1 / ((k : ℝ) + 1) < ε := by
      refine lt_of_le_of_lt ?_ hN
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hk 1)
    rw [Real.dist_eq]
    have hψc : Continuous (ψ k) := StaticLimitAux.continuous_of_smooth (hψ k)
    have hi1 : Integrable g (d1_mu hn hκ hU μ₀ t) :=
      hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hi2 : Integrable (ψ k) (d1_mu hn hκ hU μ₀ t) :=
      hψc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [← integral_sub hi1 hi2]
    calc |∫ x, (g x - ψ k x) ∂(d1_mu hn hκ hU μ₀ t)|
        ≤ ∫ x, |g x - ψ k x| ∂(d1_mu hn hκ hU μ₀ t) := abs_integral_le_integral_abs
      _ ≤ ∫ _x, 1 / ((k : ℝ) + 1) ∂(d1_mu hn hκ hU μ₀ t) :=
          integral_mono_of_nonneg (ae_of_all _ fun x => abs_nonneg _) (integrable_const _)
            (ae_of_all _ (hψg k))
      _ = 1 / ((k : ℝ) + 1) := by simp
      _ < ε := hk'
  exact hunif.continuousOn (Eventually.of_forall fun k => d1_narrow_smooth hn hκ hU μ₀ (hψ k) T).frequently

end Narrow

end HRS
