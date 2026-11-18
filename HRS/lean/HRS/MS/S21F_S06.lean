import HRS.MS.S21F_S06a
import HRS.MS.S21F_S19a
import HRS.MS.S21F_S00

/-!
# S21F, packet R26-T3.S06: actual static marginal bias and covariance bounds

For `s > 0` the calibrated `euc_static_proof` (native; bounded density `ρ₀ ≤ |M₀|`, `β = γ`), for `s = 0` the logarithmic
`r2_log_static_proof` (spherical bound `s46_spherical` from the Gaussian bound of the actual reference), both at the actual `μ₀`; `N δ_N = 1`.
`s21f_scalar_of_static` then gives the variance and bias bounds.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole

namespace HRS.MS.R26T3

theorem r26t3_static_scalar {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (hγ : 0 < p.γ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      (∀ f : Euc p.d → ℝ, MemLp f 2 (r26t3_mu R 0) →
        (N : ℝ) * variance (fun X => HRS.Whole.pair (HRS.Whole.empirical X) f) (r26t3_Q R N) ≤
          C * ∫ x, f x ^ 2 ∂(r26t3_mu R 0)) ∧
      (∀ f : Euc p.d → ℝ, Measurable f → ∀ B : ℝ, (∀ x, |f x| ≤ B) →
        |HRS.Whole.pair (r26t3_marg R N) f - HRS.Whole.pair (r26t3_mu R 0) f| ≤ C * B / N) := by
  obtain ⟨-, -, -, href⟩ := r26t3_reference_data p δ hδ hδh R
  obtain ⟨M₀, c0, S, hc0, hTc⟩ := href 0
  have hd := p.hd
  have hdr : (2 : ℝ) ≤ p.d := by exact_mod_cast hd
  have hsd : p.s < p.d := by have := p.hs; linarith
  have hP : IsProbabilityMeasure (HRS.Whole.withDensityReal (R.ρ 0)) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hTc.prob
  have hP' : IsProbabilityMeasure (r26t3_mu R 0) := hP
  have hρg : ∀ x, R.ρ 0 x ≤ |M₀| * Real.exp (-c0 * ‖x‖ ^ 2) := fun x =>
    (hTc.gauss x).trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)
  have hρM : ∀ x, R.ρ 0 x ≤ |M₀| := fun x =>
    (hρg x).trans (by
      calc |M₀| * Real.exp (-c0 * ‖x‖ ^ 2) ≤ |M₀| * 1 := mul_le_mul_of_nonneg_left
            (Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖x‖])) (abs_nonneg _)
        _ = |M₀| := mul_one _)
  have hδN : ∀ N : ℕ, 2 ≤ N → HRS.deltaN p.d p.s N = (N : ℝ)⁻¹ := fun N hN => by
    rw [HRS.Whole.deltaN_eq]; simp [p.hs]
  rcases p.hs0.eq_or_lt with h0 | hpos
  · -- s = 0
    obtain ⟨A, hA⟩ := S46.s46_spherical (d := p.d) (by omega) hc0 (abs_nonneg M₀)
    obtain ⟨C, hC⟩ := HRS.MS.Wl.r2_log_static_proof hd p.γ p.γ A hγ le_rfl
    refine ⟨max C 0, le_max_right _ _, fun N hN => ?_⟩
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have h := hC (R.ρ 0) hTc.prob (hA _ hρg) p.γ ⟨le_rfl, le_rfl⟩ N hN
    obtain ⟨-, hlin, hmarg, -⟩ := h
    have hC' : C ≤ max C 0 := le_max_left _ _
    have hQ : r26t3_Q R N = HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel p.d 0) N p.γ (r26t3_mu R 0) := by
      unfold r26t3_Q; rw [← h0]
    have key := s21f_scalar_of_static (μ := r26t3_mu R 0) (C := max C 0)
      (Q := HRS.Whole.modulatedGibbs (HRS.Whole.rieszKernel p.d 0) N p.γ (r26t3_mu R 0)) hN (le_max_right _ _) ?_ ?_
    · rw [hQ]; unfold r26t3_marg; rw [hQ]; exact key
    · intro f hf
      have hI : 0 ≤ ∫ x, f x ^ 2 ∂(r26t3_mu R 0) := integral_nonneg fun x => sq_nonneg _
      refine (hlin f hf).trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hC' hN0.le) hI
    · obtain ⟨φ, hφm, hφeq, hφb, hφ2, hφn⟩ := hmarg
      have hle : ∀ x, φ x ≤ max C 0 := fun x => by
        refine (hφb x).2.trans ?_
        have hp1 : (1 + ‖x‖ ^ 2) ^ (-(p.γ / (2 * N))) ≤ 1 :=
          Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [sq_nonneg ‖x‖])
            (by have : 0 < p.γ / (2 * N) := by positivity
                linarith)
        have h1 : 0 ≤ (1 + ‖x‖ ^ 2) ^ (-(p.γ / (2 * N))) := Real.rpow_nonneg (by positivity) _
        calc C * (1 + ‖x‖ ^ 2) ^ (-(p.γ / (2 * N))) ≤ max C 0 * (1 + ‖x‖ ^ 2) ^ (-(p.γ / (2 * N))) :=
              mul_le_mul_of_nonneg_right hC' h1
          _ ≤ max C 0 * 1 := mul_le_mul_of_nonneg_left hp1 (le_max_right _ _)
          _ = max C 0 := mul_one _
      exact ⟨φ, hφm, hφeq, fun x => ⟨(hφb x).1, hle x⟩, hφ2,
        hφn.trans (div_le_div_of_nonneg_right hC' hN0.le)⟩
  · -- s > 0
    obtain ⟨C, hC⟩ := HRS.MS.Wr.euc_static_proof hd hpos hsd p.γ p.γ |M₀| hγ le_rfl
    refine ⟨max C 0, le_max_right _ _, fun N hN => ?_⟩
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have h := hC (R.ρ 0) hTc.prob hρM p.γ ⟨le_rfl, le_rfl⟩ N hN
    obtain ⟨-, hlin, hmarg, -⟩ := h
    have hC' : C ≤ max C 0 := le_max_left _ _
    refine s21f_scalar_of_static (μ := r26t3_mu R 0) (Q := r26t3_Q R N) hN (le_max_right _ _) ?_ ?_
    · intro f hf
      have hI : 0 ≤ ∫ x, f x ^ 2 ∂(r26t3_mu R 0) := integral_nonneg fun x => sq_nonneg _
      refine (hlin f hf).trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hC' hN0.le) hI
    · obtain ⟨φ, hφm, hφeq, hφb, hφ2, hφn⟩ := hmarg
      refine ⟨φ, hφm, hφeq, fun x => ⟨(hφb x).1, (hφb x).2.trans hC'⟩, hφ2, ?_⟩
      refine hφn.trans ?_
      rw [hδN N hN, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right hC' hN0.le

end HRS.MS.R26T3
