import HRS.MS.SA16RDuh2
import HRS.MS.SA16RHeat18

/-!
# S.A.16 (SA16S) Hw1: analytic lemmas for the weak heat identity

* `sa16sw_cc_lap`: the Laplacian `sa16r_lap ψ` of `ψ ∈ C_c^∞` is in `C_c^∞`.
* `sa16sw_cv_abs_le`: `|g_a ⋆ u| ≤ sup |u|`.
* `sa16sw_cv_hasDerivAt`: for `φ ∈ C_c^∞`, `a ↦ (g_a ⋆ φ)(x)` has derivative `(g_a ⋆ Δφ)(x)`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Hw1
variable {d : ℕ}

lemma sa16sw_cc_lap {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) : IsCcInfty (sa16r_lap ψ) := by
  have h : sa16r_lap ψ = ∑ i : Fin d, fun x => fderiv ℝ (fun y => fderiv ℝ ψ y
      (EuclideanSpace.single i 1)) x (EuclideanSpace.single i 1) := by
    funext x; simp [sa16r_lap, Finset.sum_apply]
  rw [h]
  exact (ccSub d).sum_mem (fun i _ => sa16s_cc_fderiv (sa16s_cc_fderiv hψ _) _)

lemma sa16sw_cv_abs_le {a : ℝ} (ha : 0 < a) {u : Euc d → ℝ} {B : ℝ}
    (hB : ∀ y, |u y| ≤ B) (x : Euc d) : |sa16r_cv (sa16r_g d a) u x| ≤ B := by
  unfold sa16r_cv
  calc |∫ z, sa16r_g d a z * u (x - z)| = ‖∫ z, sa16r_g d a z * u (x - z)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ z, B * sa16r_g d a z := by
        refine norm_integral_le_of_norm_le ((sa16r_g_int ha).const_mul B) (Eventually.of_forall fun z => ?_)
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (sa16r_g_pos ha z)]
        have := hB (x - z)
        have := sa16r_g_pos ha z
        nlinarith
    _ = B := by rw [integral_const_mul, sa16r_g_mass ha, mul_one]

/-- uniform bound of `∂_a g_a` on a ball -/
lemma sa16sw_coef_bound {a0 a R : ℝ} (ha0 : 0 < a0) (ha1 : a0 / 2 ≤ a) (ha2 : a ≤ 2 * a0) {z : Euc d}
    (hz : ‖z‖ ≤ R) :
    |(‖z‖ ^ 2 / (4 * a ^ 2) - (d : ℝ) / (2 * a)) * sa16r_g d a z| ≤
      (R ^ 2 / a0 ^ 2 + (d : ℝ) / a0) * (2 * Real.pi * a0) ^ (-((d : ℝ) / 2)) := by
  have ha : 0 < a := lt_of_lt_of_le (by positivity) ha1
  have hg0 := sa16r_g_pos ha z
  have hgb : sa16r_g d a z ≤ (2 * Real.pi * a0) ^ (-((d : ℝ) / 2)) := by
    refine (sa16r_g_dom ha0 ha1 ha2 z).trans ?_
    have : Real.exp (-(1 / (8 * a0)) * ‖z‖ ^ 2) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ (1 / (8 * a0)) * ‖z‖ ^ 2 := by positivity
      linarith
    have hp : 0 ≤ (2 * Real.pi * a0) ^ (-((d : ℝ) / 2)) := by positivity
    nlinarith
  have hR : ‖z‖ ^ 2 ≤ R ^ 2 := by
    have := norm_nonneg z
    nlinarith
  have h1 : ‖z‖ ^ 2 / (4 * a ^ 2) ≤ R ^ 2 / a0 ^ 2 := by
    have hR0 : 0 ≤ R ^ 2 := le_trans (sq_nonneg _) hR
    calc ‖z‖ ^ 2 / (4 * a ^ 2) ≤ R ^ 2 / (4 * a ^ 2) := by gcongr
      _ ≤ R ^ 2 / a0 ^ 2 := by
        apply div_le_div_of_nonneg_left hR0 (by positivity)
        nlinarith
  have h2 : (d : ℝ) / (2 * a) ≤ (d : ℝ) / a0 := by
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg d) ha0
    linarith
  have h3 : 0 ≤ ‖z‖ ^ 2 / (4 * a ^ 2) := by positivity
  have h4 : 0 ≤ (d : ℝ) / (2 * a) := by positivity
  rw [abs_mul, abs_of_pos hg0]
  have hb : |‖z‖ ^ 2 / (4 * a ^ 2) - (d : ℝ) / (2 * a)| ≤ R ^ 2 / a0 ^ 2 + (d : ℝ) / a0 := by
    rw [abs_le]; constructor <;> linarith
  exact mul_le_mul hb hgb hg0.le (le_trans (abs_nonneg _) hb)

/-- inner derivative: `d/da (g_a ⋆ φ)(x) = (g_a ⋆ Δφ)(x)` -/
lemma sa16sw_cv_hasDerivAt {a0 : ℝ} (ha0 : 0 < a0) {φ : Euc d → ℝ} (hφ : IsCcInfty φ) (x : Euc d) :
    HasDerivAt (fun a => sa16r_cv (sa16r_g d a) φ x)
      (sa16r_cv (sa16r_g d a0) (sa16r_lap φ) x) a0 := by
  obtain ⟨Rφ, hRφ0, hRφ⟩ := sa16r_cc_support hφ.2
  obtain ⟨Bφ, hBφ⟩ := sa16r_cc_bdd hφ
  set R : ℝ := ‖x‖ + Rφ with hR
  set C1 : ℝ := (R ^ 2 / a0 ^ 2 + (d : ℝ) / a0) * (2 * Real.pi * a0) ^ (-((d : ℝ) / 2)) with hC1
  set F : ℝ → Euc d → ℝ := fun a z => sa16r_g d a z * φ (x - z) with hF
  set F' : ℝ → Euc d → ℝ := fun a z =>
    ((‖z‖ ^ 2 / (4 * a ^ 2) - (d : ℝ) / (2 * a)) * sa16r_g d a z) * φ (x - z) with hF'
  have hs : Ioo (a0 / 2) (2 * a0) ∈ 𝓝 a0 := Ioo_mem_nhds (by linarith) (by linarith)
  have hφc : Continuous fun z : Euc d => φ (x - z) := hφ.1.continuous.comp (continuous_const.sub continuous_id)
  have hbound_int : Integrable ((closedBall (0 : Euc d) R).indicator (fun _ => C1 * Bφ)) := by
    refine (integrable_indicator_iff measurableSet_closedBall).2 ?_
    exact integrableOn_const (measure_closedBall_lt_top).ne
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure (Euc d)))
    (F := F) (F' := F') (bound := (closedBall (0 : Euc d) R).indicator (fun _ => C1 * Bφ)) hs
    (Eventually.of_forall fun a => ((sa16r_g_contDiff (a := a)).continuous.mul hφc).aestronglyMeasurable)
    (sa16r_cv_integrand (sa16r_g_int ha0) hφ x)
    (by
      refine Continuous.aestronglyMeasurable ?_
      have : Continuous fun z : Euc d => (‖z‖ ^ 2 / (4 * a0 ^ 2) - (d : ℝ) / (2 * a0)) * sa16r_g d a0 z :=
        (((continuous_norm.pow 2).div_const _).sub continuous_const).mul
          (sa16r_g_contDiff (a := a0)).continuous
      exact this.mul hφc)
    (Eventually.of_forall fun z a ha => by
      by_cases hz : ‖z‖ ≤ R
      · have hzm : z ∈ closedBall (0 : Euc d) R := by simpa using hz
        rw [Set.indicator_of_mem hzm]
        show ‖(_ : ℝ) * φ (x - z)‖ ≤ _
        rw [Real.norm_eq_abs, abs_mul]
        have := sa16sw_coef_bound ha0 ha.1.le ha.2.le hz
        have h2 := hBφ (x - z)
        exact mul_le_mul this h2 (abs_nonneg _) (le_trans (abs_nonneg _) this)
      · have hz' : R < ‖z‖ := not_le.1 hz
        have : φ (x - z) = 0 := by
          apply hRφ
          have h1 : ‖z‖ ≤ ‖x - z‖ + ‖x‖ := by
            have := norm_sub_le x (x - z)
            simp only [sub_sub_cancel] at this
            linarith
          linarith
        have hzn : z ∉ closedBall (0 : Euc d) R := by simpa using hz
        rw [Set.indicator_of_notMem hzn]
        simp [hF', this])
    hbound_int
    (Eventually.of_forall fun z a ha => by
      have ha' : 0 < a := lt_trans (by linarith [ha.1]) ha.1 |>.trans_le le_rfl
      exact (sa16r_g_hasDerivAt_a ha' z).mul_const (φ (x - z)))
  have e1 : (fun a => sa16r_cv (sa16r_g d a) φ x) = fun a => ∫ z, F a z := rfl
  rw [e1]
  have e2 : ∫ z, F' a0 z = sa16r_cv (sa16r_g d a0) (sa16r_lap φ) x := by
    have := sa16r_lap_ibp ha0 hφ x
    unfold sa16r_cv
    rw [← this]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [hF', sa16r_g_heat ha0 z]
  rw [← e2]
  exact key.2

end Hw1

end HRS.Whole.AppendixA.Phase2SA16R
