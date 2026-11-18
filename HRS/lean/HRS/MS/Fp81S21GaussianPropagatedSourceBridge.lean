import HRS.MS.Fp81S21GaussianPhysicalPackage
import HRS.MS.Fp81S21Uniform2

/-! Packet 36B bridge, partial construction. The propagated test is represented
by the retained thermal operator, and compact smooth approximants converge in
its domain. Each approximant has the literal retained-source evaluation.
The convergence of their literal combined features to the propagated test's
literal feature is a separate, unproved step; this file does not assert the
propagated source bridge. No source or physical selector is replaced. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

private theorem fp81s21_bridge_thermal_approximation
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (f : Euc p.d → ℝ)
    (hfW : IsR2WeightedTest (2 * p.d + 8) ((p.d : ℝ) + 2) f)
    (hf : MemLp f 2 (HRS.Whole.withDensityReal R.ρβ)) :
    ∃ ψ : ℕ → compactSmoothSubmodule p.d,
    ∃ hψ : ∀ n, MemLp (ψ n : Euc p.d → ℝ) 2 (HRS.Whole.withDensityReal R.ρβ),
      Tendsto (fun n => (hψ n).toLp (ψ n : Euc p.d → ℝ))
        atTop (𝓝 (hf.toLp f)) := by
  let μ := HRS.Whole.withDensityReal R.ρβ
  letI : IsProbabilityMeasure μ := HRS.Whole.Q34.isProbabilityMeasure_nu R.thermal.1.1
  have hr : (2 : ℝ) + (p.d : ℝ) / 2 < ((2 * p.d + 8 : ℕ) : ℝ) := by
    have hd : (0 : ℝ) ≤ p.d := Nat.cast_nonneg _
    push_cast
    linarith
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) p.d]
  obtain ⟨B, _, hOp⟩ := physical_weighted_L2_operators p.hd p.s p.a p.β
    ((p.d : ℝ) + 2) (2 * p.d + 8) p.hs0 p.hs p.ha p.hβ hr hP R.ρβ R.thermal
  let ψ : ℕ → compactSmoothSubmodule p.d := chartSection E (E.encode f)
  have hψW : ∀ n, IsR2WeightedTest (2 * p.d + 8) ((p.d : ℝ) + 2)
      (ψ n : Euc p.d → ℝ) := fun n =>
    weightedTestSubmodule_iff.1 (weighted_test_of_compact_smooth hP (ψ n).property)
  let hψ : ∀ n, MemLp (ψ n : Euc p.d → ℝ) 2 μ :=
    fun n => (hOp (ψ n) (hψW n)).1
  refine ⟨ψ, hψ, ?_⟩
  let fn : ℕ → Lp ℝ 2 μ := fun n => (hψ n).toLp (ψ n : Euc p.d → ℝ)
  let fL : Lp ℝ 2 μ := hf.toLp f
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hb : ∀ n, ‖fn n - fL‖ ^ 2 ≤ B *
      (weightedSobolevE (2 * p.d + 8) ((p.d : ℝ) + 2)
        ((ψ n : Euc p.d → ℝ) - f)).toReal ^ 2 := by
    intro n
    have heq : ‖fn n - fL‖ ^ 2 = ∫ x : Euc p.d,
        ((ψ n : Euc p.d → ℝ) x - f x) ^ 2 ∂μ := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub (fn n) fL, (hψ n).coeFn_toLp,
        hf.coeFn_toLp] with x h1 h2 h3
      change (fn n - fL) x * (fn n - fL) x = _
      rw [h1]
      simp only [Pi.sub_apply]
      change fn n x = _ at h2
      change fL x = _ at h3
      rw [h2, h3]
      ring
    rw [heq]
    simpa only [Pi.sub_apply] using
      (hOp _ (chartSection_error_weighted E hP f hfW n)).2.1
  have he := chartSection_error_tendsto E hP f hfW
  have hlim : Tendsto (fun n : ℕ => B *
      (weightedSobolevE (2 * p.d + 8) ((p.d : ℝ) + 2)
        ((ψ n : Euc p.d → ℝ) - f)).toReal ^ 2) atTop (𝓝 0) := by
    simpa [ψ] using (he.pow 2).const_mul B
  have hsq : Tendsto (fun n => ‖fn n - fL‖ ^ 2) atTop (𝓝 0) :=
    squeeze_zero (fun _ => sq_nonneg _) hb hlim
  have hsqrt := (Real.continuous_sqrt.tendsto 0).comp hsq
  simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_sq (norm_nonneg _)] using hsqrt

/-- The thermal side of the propagated source bridge, together with compact
approximants whose source evaluations use the original literal features.
This does not assert convergence of those features to the feature at `f`. -/
theorem fp81s21_gaussian_propagated_thermal_approximation (p : Parameters) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
      letI := fp81s21_initialMeasure_isProbability p R
      ∀ Q : fp81s21_Physical35 p R, ∀ a : ℝ, 0 ≤ a →
      ∀ r ∈ Icc (0 : ℝ) (a + p.T), ∀ t ∈ Icc r (a + p.T),
      ∀ α : MultiIndex p.d,
      let f := propagatorW (r26t3_coeff R) r t
        (oscTestFun (wholeSpaceIndex p.d : ℝ) α)
      IsR2WeightedTest (2 * p.d + 8) ((p.d : ℝ) + 2) f ∧
      ∃ hf : MemLp f 2 (HRS.Whole.withDensityReal R.ρβ),
        ((fun ω => fp81s21_chartAction Q.E
          (fp81s21_gaussian35_qG Q.tofp81s21_Gaussian35Selection r ω) f)
          =ᵐ[Q.src.G0.P] (Q.S.T Q.src.G0 r (hf.toLp f) : Q.src.G0.Ω → ℝ)) ∧
        ∃ ψ : ℕ → compactSmoothSubmodule p.d,
        ∃ hψ : ∀ n, MemLp (ψ n : Euc p.d → ℝ) 2 (HRS.Whole.withDensityReal R.ρβ),
          Tendsto (fun n => (hψ n).toLp (ψ n : Euc p.d → ℝ))
            atTop (𝓝 (hf.toLp f)) ∧
          ∀ n, (Q.S.T Q.src.G0 r ((hψ n).toLp (ψ n : Euc p.d → ℝ)) :
            Q.src.G0.Ω → ℝ) =ᵐ[Q.src.G0.P]
              fun ω => Q.src.W
                (Q.src.J (fp81s21_combinedFeature p R Q.src.hK r (ψ n))) ω := by
  obtain ⟨δ₀, hδ₀, hhalf, hD⟩ := fp81s21_uniform_orbit_amplitudes p
  refine ⟨δ₀, hδ₀, hhalf, ?_⟩
  intro δ hδ hδle R
  letI := fp81s21_initialMeasure_isProbability p R
  intro Q a ha r hr t ht α
  dsimp only
  have hH : 0 < a + p.T := add_pos_of_nonneg_of_pos ha p.hT
  obtain ⟨Co, co, _, _, hDR⟩ := hD δ hδ hδle R
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) p.d]
  have hfW := (HRS.MS.R2Interp.s102_orbit_test hP (hDR (a + p.T) hH) hr ht α).1
  obtain ⟨hf, _, hag, _⟩ := Q.weighted r hr.1 _ hfW
  obtain ⟨ψ, hψ, hconv⟩ := fp81s21_bridge_thermal_approximation p R Q.E _ hfW hf
  refine ⟨hfW, hf, hag, ψ, hψ, hconv, ?_⟩
  intro n
  have hosc := r2Test_isOscTest (wholeSpaceIndex p.d : ℝ) (ψ n).property
  exact (Q.T_oscillator r hr.1 (ψ n) hosc (hψ n)).trans
    (Q.src.sourceEvaluation r hr.1 (ψ n) hosc)

#print axioms fp81s21_bridge_thermal_approximation
#print axioms fp81s21_gaussian_propagated_thermal_approximation
end HRS.Fp81.S21
end
