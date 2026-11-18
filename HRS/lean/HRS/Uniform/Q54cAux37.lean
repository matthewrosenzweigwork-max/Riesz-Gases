import HRS.Uniform.Q54cAux36

/-!
# Q54c, part 37: the Bures cost between two covariance forms with different `q` and densities
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.Uniform.Q54c

open HRS HRS.PDE HRS.Torus HRS.Uniform

variable {d : ℕ}

theorem sq_sqrt_sub_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 ≤ |a - b| := by
  have hx := Real.sqrt_nonneg a
  have hy := Real.sqrt_nonneg b
  have e : a - b = (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) := by
    have h1 := Real.sq_sqrt ha
    have h2 := Real.sq_sqrt hb
    nlinarith
  rw [e, abs_mul, abs_of_nonneg (by linarith : 0 ≤ Real.sqrt a + Real.sqrt b)]
  have : |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt a + Real.sqrt b := by
    rw [abs_le]; constructor <;> linarith
  calc (Real.sqrt a - Real.sqrt b) ^ 2 = |Real.sqrt a - Real.sqrt b| * |Real.sqrt a - Real.sqrt b| := by
        rw [← sq, sq_abs]
    _ ≤ _ := mul_le_mul_of_nonneg_left this (abs_nonneg _)

/-- the family representation of `covForm` -/
theorem covForm_rep {n : ℝ} (hn : (d : ℝ) / 2 + 2 < n) {q : ℝ} (hq : 0 ≤ q) {ρ : Torus d → ℝ}
    (hρ : IsProbDensity ρ) (hρc : Continuous ρ) (x y : NegSobolev d n) :
    covForm n q (withDensityReal ρ) x y = ∑ j : Fin d, ∫ s,
      inner ℝ (Real.sqrt (2 * q * ρ s) • bVec n j s) x *
        inner ℝ (Real.sqrt (2 * q * ρ s) • bVec n j s) y ∂(volume : Measure (Torus d)) := by
  haveI := HRS.Uniform.Q48c.isFiniteMeasure_withDensityReal_of_cont hρc
  rw [HRS.Uniform.Q14.q14_covForm_apply hn hq]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [HRS.integral_withDensityReal_eq ρ hρ.measurable hρ.nonneg]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s => ?_)
  simp only [inner_smul_left, conj_trivial]
  have h1 : Real.sqrt (2 * q * ρ s) * Real.sqrt (2 * q * ρ s) = 2 * q * ρ s :=
    Real.mul_self_sqrt (mul_nonneg (by positivity) (hρ.nonneg s))
  have h2 : Real.sqrt (2 * q) * Real.sqrt (2 * q) = 2 * q := Real.mul_self_sqrt (by positivity)
  calc ρ s * (Real.sqrt (2 * q) * inner ℝ (bVec n j s) x * (Real.sqrt (2 * q) * inner ℝ (bVec n j s) y))
      = ρ s * ((Real.sqrt (2 * q) * Real.sqrt (2 * q)) *
        (inner ℝ (bVec n j s) x * inner ℝ (bVec n j s) y)) := by ring
    _ = (Real.sqrt (2 * q * ρ s) * Real.sqrt (2 * q * ρ s)) *
        (inner ℝ (bVec n j s) x * inner ℝ (bVec n j s) y) := by rw [h1, h2]; ring
    _ = _ := by ring

theorem bures2_covForm_le {n : ℝ} (hn : (d : ℝ) / 2 + 2 < n) {qa qb : ℝ} (hqa : 0 ≤ qa) (hqb : 0 ≤ qb)
    {ρa ρb : Torus d → ℝ} (hρa : IsProbDensity ρa) (hρb : IsProbDensity ρb)
    (hca : Continuous ρa) (hcb : Continuous ρb) {δ : ℝ} (hδ : ∀ x, |ρa x - ρb x| ≤ δ) :
    HRS.Uniform.bures2 (covForm n qa (withDensityReal ρa)) (covForm n qb (withDensityReal ρb)) ≤
      4 * d * HRS.Uniform.Q14.q14S d (n - 1) * (qa * δ + |qa - qb|) := by
  set S := HRS.Uniform.Q14.q14S d (n - 1) with hS
  have hS0 : 0 ≤ S := HRS.Uniform.Q14.q14S_nonneg d (n - 1)
  set u : Fin d → Torus d → NegSobolev d n := fun j s => Real.sqrt (2 * qa * ρa s) • bVec n j s with hu
  set v : Fin d → Torus d → NegSobolev d n := fun j s => Real.sqrt (2 * qb * ρb s) • bVec n j s with hv
  have hbc := fun j => HRS.Uniform.Q14.q14_continuous_bVec hn j
  have huc : ∀ j, Continuous (u j) := fun j =>
    (Real.continuous_sqrt.comp (continuous_const.mul hca)).smul (hbc j)
  have hvc : ∀ j, Continuous (v j) := fun j =>
    (Real.continuous_sqrt.comp (continuous_const.mul hcb)).smul (hbc j)
  obtain ⟨Ba, hBa⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hca.continuousOn
  obtain ⟨Bb, hBb⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hcb.continuousOn
  have hMb : ∀ (j : Fin d) (s : Torus d), ‖bVec n j s‖ ≤ Real.sqrt (2 * S) := fun j s => by
    calc ‖bVec n j s‖ = Real.sqrt (‖bVec n j s‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
      _ ≤ _ := Real.sqrt_le_sqrt (HRS.Uniform.Q14.q14_norm_bVec_sq_le hn j s)
  set M : ℝ := Real.sqrt (2 * |qa| * |Ba|) * Real.sqrt (2 * S) + Real.sqrt (2 * |qb| * |Bb|) * Real.sqrt (2 * S)
    with hM
  have hM0 : 0 ≤ M := by positivity
  have hMu : ∀ j s, ‖u j s‖ ≤ M := by
    intro j s
    have h1 : ‖u j s‖ ≤ Real.sqrt (2 * qa * ρa s) * Real.sqrt (2 * S) := by
      rw [hu]; simp only [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hMb j s) (Real.sqrt_nonneg _)
    have h2 : Real.sqrt (2 * qa * ρa s) ≤ Real.sqrt (2 * |qa| * |Ba|) := by
      refine Real.sqrt_le_sqrt ?_
      have := hBa s (Set.mem_univ _)
      rw [Real.norm_eq_abs] at this
      have h3 : ρa s ≤ |Ba| := (le_abs_self _).trans (this.trans (le_abs_self _))
      have : 2 * qa * ρa s ≤ 2 * |qa| * |Ba| := by
        have := hρa.nonneg s
        nlinarith [le_abs_self qa, abs_nonneg qa, abs_nonneg Ba]
      exact this
    refine h1.trans ?_
    have : Real.sqrt (2 * qa * ρa s) * Real.sqrt (2 * S) ≤ Real.sqrt (2 * |qa| * |Ba|) * Real.sqrt (2 * S) :=
      mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)
    have : 0 ≤ Real.sqrt (2 * |qb| * |Bb|) * Real.sqrt (2 * S) := by positivity
    linarith
  have hMv : ∀ j s, ‖v j s‖ ≤ M := by
    intro j s
    have h1 : ‖v j s‖ ≤ Real.sqrt (2 * qb * ρb s) * Real.sqrt (2 * S) := by
      rw [hv]; simp only [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hMb j s) (Real.sqrt_nonneg _)
    have h2 : Real.sqrt (2 * qb * ρb s) ≤ Real.sqrt (2 * |qb| * |Bb|) := by
      refine Real.sqrt_le_sqrt ?_
      have := hBb s (Set.mem_univ _)
      rw [Real.norm_eq_abs] at this
      have h3 : ρb s ≤ |Bb| := (le_abs_self _).trans (this.trans (le_abs_self _))
      have := hρb.nonneg s
      nlinarith [le_abs_self qb, abs_nonneg qb, abs_nonneg Bb]
    refine h1.trans ?_
    have : Real.sqrt (2 * qb * ρb s) * Real.sqrt (2 * S) ≤ Real.sqrt (2 * |qb| * |Bb|) * Real.sqrt (2 * S) :=
      mul_le_mul_of_nonneg_right h2 (Real.sqrt_nonneg _)
    have : 0 ≤ Real.sqrt (2 * |qa| * |Ba|) * Real.sqrt (2 * S) := by positivity
    linarith
  obtain ⟨ι, hι, e, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := NegSobolev d n)
  have key := HRS.Uniform.Q14.q14_bures2_le_family (ξ := (volume : Measure (Torus d)))
    (fun j => (huc j).measurable) (fun j => (hvc j).measurable) hM0 hMu hMv
    (C := covForm n qa (withDensityReal ρa)) (D := covForm n qb (withDensityReal ρb))
    (fun x y => covForm_rep hn hqa hρa hca x y) (fun x y => covForm_rep hn hqb hρb hcb x y)
  refine key.trans ?_
  -- pointwise bound
  have hpt : ∀ (j : Fin d) (s : Torus d), ‖u j s - v j s‖ ^ 2 ≤
      2 * S * |2 * qa * ρa s - 2 * qb * ρb s| := by
    intro j s
    have : u j s - v j s = (Real.sqrt (2 * qa * ρa s) - Real.sqrt (2 * qb * ρb s)) • bVec n j s := by
      rw [hu, hv]; simp only [sub_smul]
    rw [this, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    have h1 := sq_sqrt_sub_le (2 * qa * ρa s) (2 * qb * ρb s)
      (mul_nonneg (by positivity) (hρa.nonneg s)) (mul_nonneg (by positivity) (hρb.nonneg s))
    have h2 := HRS.Uniform.Q14.q14_norm_bVec_sq_le hn j s
    calc _ ≤ |2 * qa * ρa s - 2 * qb * ρb s| * (2 * S) :=
          mul_le_mul h1 h2 (sq_nonneg _) (abs_nonneg _)
      _ = _ := by ring
  have hint : Integrable (fun s : Torus d => 2 * S * |2 * qa * ρa s - 2 * qb * ρb s|) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _)
    fun_prop
  have hbound : ∀ j : Fin d, ∫ s, ‖u j s - v j s‖ ^ 2 ∂(volume : Measure (Torus d)) ≤
      4 * S * (qa * δ + |qa - qb|) := by
    intro j
    refine (integral_mono_of_nonneg (Filter.Eventually.of_forall fun s => sq_nonneg _) hint
      (Filter.Eventually.of_forall (hpt j))).trans ?_
    have hA : ∀ s : Torus d, 2 * S * |2 * qa * ρa s - 2 * qb * ρb s| ≤
        4 * S * (qa * δ + |qa - qb| * ρb s) := by
      intro s
      have : |2 * qa * ρa s - 2 * qb * ρb s| ≤ 2 * (qa * δ + |qa - qb| * ρb s) := by
        have e1 : 2 * qa * ρa s - 2 * qb * ρb s = 2 * (qa * (ρa s - ρb s) + (qa - qb) * ρb s) := by ring
        rw [e1, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_mul, abs_of_nonneg hqa, abs_of_nonneg (hρb.nonneg s)]
        exact add_le_add (mul_le_mul_of_nonneg_left (hδ s) hqa) le_rfl
      nlinarith [mul_le_mul_of_nonneg_left this hS0]
    have hint2 : Integrable (fun s : Torus d => 4 * S * (qa * δ + |qa - qb| * ρb s)) := by
      refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _)
      fun_prop
    refine (integral_mono hint hint2 hA).trans (le_of_eq ?_)
    have hρbi : Integrable ρb := hcb.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [integral_const_mul, integral_add (integrable_const _) (hρbi.const_mul _), integral_const,
      integral_const_mul, hρb.integral_one]
    simp
  calc ∑ j : Fin d, ∫ s, ‖u j s - v j s‖ ^ 2 ∂(volume : Measure (Torus d)) ≤
        ∑ j : Fin d, 4 * S * (qa * δ + |qa - qb|) := Finset.sum_le_sum fun j _ => hbound j
    _ = _ := by simp; ring

end HRS.Uniform.Q54c
