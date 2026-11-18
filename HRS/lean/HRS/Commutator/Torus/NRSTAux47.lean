import HRS.Commutator.Torus.NRSTAux46

/-!
# NRS-T, part 47: the limit `N → ∞` of the rescaled terms, and the expansion of `Jf`
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators FourierTransform ContDiff SchwartzMap RealInnerProductSpace
  ComplexConjugate

namespace HRS.Commutator.TorusNote

open HRS HRS.Commutator.TorusNote.NRST

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma nrstr_integral_theta0_sq :
    ∫ η : 𝔼, (nrstr_theta0 (d := d) η) ^ 2 = ((nrstr_m0 d : ℝ) : ℂ) := by
  unfold nrstr_m0
  rw [← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
  simp only
  rw [nrstr_theta0_apply, Complex.norm_real, Real.norm_of_nonneg (nrstr_bumpE_nonneg η)]
  push_cast
  ring

lemma nrstr_Hs_continuous {σ : ℝ} (hσ : 0 < σ) (N : ℝ) (k l : Lattice d) (c : Fin d) :
    Continuous (nrstr_Hs σ N k l c) := by
  unfold nrstr_Hs
  have hn : Continuous fun η : 𝔼 => ‖Lattice.toEuc k + N⁻¹ • η‖ := by fun_prop
  have h1 : Continuous fun η : 𝔼 => (2 * Real.pi * ‖Lattice.toEuc k + N⁻¹ • η‖) ^ (2 * σ) :=
    (Real.continuous_rpow_const (by linarith)).comp (continuous_const.mul hn)
  have h2 : Continuous fun η : 𝔼 => (((l c : ℤ) : ℝ) - N⁻¹ * η c) := by fun_prop
  exact (Complex.continuous_ofReal.comp (h1.mul h2)).mul ((nrstr_theta0 (d := d)).continuous.pow 2)

lemma nrstr_S_tendsto {σ : ℝ} (hσ : 0 < σ) (k l : Lattice d) (c : Fin d) :
    Tendsto (fun n : ℕ => nrstr_S σ ((n : ℝ) + 1) k l c) atTop
      (𝓝 ((((2 * Real.pi * ‖Lattice.toEuc k‖) ^ (2 * σ) * (((l c : ℤ) : ℝ)) : ℝ) : ℂ) *
        ((nrstr_m0 d : ℝ) : ℂ))) := by
  rw [← nrstr_integral_theta0_sq, ← integral_const_mul]
  unfold nrstr_S
  set M : ℝ := (2 * Real.pi * (‖Lattice.toEuc k‖ + 1 / 8)) ^ (2 * σ) * (|((l c : ℤ) : ℝ)| + 1 / 8) with hM
  have hM0 : 0 ≤ M := by positivity
  refine tendsto_integral_of_dominated_convergence (fun η => M * ‖nrstr_theta0 (d := d) η‖ ^ 2) ?_ ?_ ?_ ?_
  · intro n
    exact (nrstr_Hs_continuous hσ _ k l c).aestronglyMeasurable
  · exact (nrstr_theta0_sq_integrable (d := d)).const_mul M
  · intro n
    refine Filter.Eventually.of_forall fun η => ?_
    unfold nrstr_Hs
    by_cases hη : ‖η‖ < 1 / 8
    · have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hn1 : ((n : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      have hn0 : 0 ≤ ((n : ℝ) + 1)⁻¹ := by positivity
      rw [norm_mul, Complex.norm_real, norm_pow, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_right ?_ (by positivity)
      rw [abs_mul]
      have h1 : ‖Lattice.toEuc k + ((n : ℝ) + 1)⁻¹ • η‖ ≤ ‖Lattice.toEuc k‖ + 1 / 8 := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, Real.norm_of_nonneg hn0]
        nlinarith [norm_nonneg η]
      have h2 : |(((l c : ℤ) : ℝ) - ((n : ℝ) + 1)⁻¹ * η c)| ≤ |((l c : ℤ) : ℝ)| + 1 / 8 := by
        refine (abs_sub _ _).trans ?_
        rw [abs_mul, abs_of_nonneg hn0]
        have : |η c| ≤ ‖η‖ := by simpa [Real.norm_eq_abs] using PiLp.norm_apply_le η c
        nlinarith [abs_nonneg (η c)]
      rw [hM]
      refine mul_le_mul ?_ h2 (abs_nonneg _) (by positivity)
      rw [abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
      exact Real.rpow_le_rpow (by positivity) (by gcongr) (by positivity)
    · push Not at hη
      rw [nrstr_theta0_zero_of_far hη]
      simp
  · refine Filter.Eventually.of_forall fun η => ?_
    unfold nrstr_Hs
    have hlim : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    have h1 : Tendsto (fun n : ℕ => (2 * Real.pi * ‖Lattice.toEuc k + ((n : ℝ) + 1)⁻¹ • η‖) ^ (2 * σ) *
        (((l c : ℤ) : ℝ) - ((n : ℝ) + 1)⁻¹ * η c)) atTop
        (𝓝 ((2 * Real.pi * ‖Lattice.toEuc k‖) ^ (2 * σ) * ((l c : ℤ) : ℝ))) := by
      have e1 : Tendsto (fun n : ℕ => (2 * Real.pi * ‖Lattice.toEuc k + ((n : ℝ) + 1)⁻¹ • η‖)) atTop
          (𝓝 (2 * Real.pi * ‖Lattice.toEuc k‖)) := by
        have := (hlim.smul_const η).const_add (Lattice.toEuc k)
        simp only [zero_smul, add_zero] at this
        exact (this.norm).const_mul _
      have e2 := (Real.continuousAt_rpow_const (2 * Real.pi * ‖Lattice.toEuc k‖) (2 * σ)
        (Or.inr (by linarith))).tendsto.comp e1
      have e3 : Tendsto (fun n : ℕ => (((l c : ℤ) : ℝ) - ((n : ℝ) + 1)⁻¹ * η c)) atTop
          (𝓝 (((l c : ℤ) : ℝ))) := by
        have := (hlim.mul_const (η c)).const_sub (((l c : ℤ) : ℝ))
        simpa using this
      simpa using e2.mul e3
    exact ((Complex.continuous_ofReal.tendsto _).comp h1).mul_const _

end HRS.Commutator.TorusNote
