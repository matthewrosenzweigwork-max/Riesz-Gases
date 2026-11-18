import HRS.Energy.Modulated

/-!
# Q32a helper: pointwise upper bound on a thermal density of the periodic Riesz kernel

For a thermal density `ρ` of `V` (`IsThermalDensity g V β ρ`, `H:eq:thermal-equation`) with
`g = periodicRiesz d s` (`d ≥ 2`, `0 ≤ s < d`), `V` continuous and bounded by `M`, and `β ≥ 0`,
the density is bounded above by a constant `Λ` (TeX M L3357-3363).  Route:
* `g ≥ -B` pointwise (`periodicRiesz_ge`), so `u := g ⋆ ρ ≥ -B₁` with `B₁ = max B 0`
  (`ρ ≥ 0`, `∫ρ = 1`);
* `Z := ∫ exp(-β(V + u))`; Jensen (`ConvexOn.map_integral_le`) with `∫ u = ∫ g` (Mathlib
  `integral_convolution`, since `u = ρ ⋆ g`) gives `Z ≥ exp(-β(M + |∫g|))`;
* `ρ = exp(-β(V + u))/Z ≤ exp(β(M + B₁)) / Z`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d : ℕ} {s : ℝ}

theorem q32a_integrable_of_isProb {ρ : Torus d → ℝ} (hρ : IsProbDensity ρ) : Integrable ρ := by
  by_contra h
  have h0 := integral_undef h
  rw [hρ.integral_one] at h0
  norm_num at h0

theorem q32a_integrable_of_continuous {f : Torus d → ℝ} (hf : Continuous f) : Integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- For a probability density `ρ` and integrable `g`, the convolution `g ⋆ ρ` (as written in
`convFun`) is integrable with integral `∫ g`. -/
theorem q32a_convFun_integrable_integral {g ρ : Torus d → ℝ} (hg : Integrable g)
    (hρ : IsProbDensity ρ) :
    Integrable (convFun g ρ) ∧ ∫ x, convFun g ρ x = ∫ x, g x := by
  have hρi := q32a_integrable_of_isProb hρ
  have hu : convFun g ρ = convolution ρ g (ContinuousLinearMap.mul ℝ ℝ) volume := by
    funext x
    rw [convolution_def]
    unfold convFun
    congr 1
    funext y
    simp only [ContinuousLinearMap.mul_apply']
    ring
  rw [hu]
  refine ⟨hρi.integrable_convolution (L := ContinuousLinearMap.mul ℝ ℝ) hg, ?_⟩
  rw [integral_convolution (L := ContinuousLinearMap.mul ℝ ℝ) hρi hg, hρ.integral_one]
  simp

/-- **Q32a thermal upper bound**: a thermal density of a bounded continuous potential, for the
periodic Riesz kernel with `β ≥ 0`, is bounded above (a constant depending on `ρ`). -/
theorem q32a_thermal_bounded_above (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    {V : Torus d → ℝ} (hVc : Continuous V) {M : ℝ} (hVM : ∀ x, |V x| ≤ M) {β : ℝ} (hβ : 0 ≤ β)
    {ρ : Torus d → ℝ} (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) :
    ∃ Λ : ℝ, ∀ x, ρ x ≤ Λ := by
  obtain ⟨hprob, hth⟩ := hρ
  obtain ⟨B, hB⟩ := periodicRiesz_ge (d := d) hd hs0 hsd
  have hgi : Integrable (periodicRiesz d s) := KernelAux.integrable_periodicRiesz hd hs0 hsd
  have hB1nn : 0 ≤ max B 0 := le_max_right _ _
  have hB1le : ∀ x, -max B 0 ≤ periodicRiesz d s x :=
    fun x => (neg_le_neg (le_max_left _ _)).trans (hB x)
  have hρi := q32a_integrable_of_isProb hprob
  obtain ⟨hui, huI⟩ := q32a_convFun_integrable_integral hgi hprob
  -- lower bound `u ≥ -B₁` pointwise
  have hu_lb : ∀ x, -max B 0 ≤ convFun (periodicRiesz d s) ρ x := by
    intro x
    by_cases hint : Integrable (fun y => periodicRiesz d s (x - y) * ρ y)
    · have h1 : ∫ y, -max B 0 * ρ y = -max B 0 := by
        rw [integral_const_mul, hprob.integral_one, mul_one]
      calc -max B 0 = ∫ y, -max B 0 * ρ y := h1.symm
        _ ≤ ∫ y, periodicRiesz d s (x - y) * ρ y :=
          integral_mono (hρi.const_mul _) hint
            (fun y => mul_le_mul_of_nonneg_right (hB1le (x - y)) (hprob.nonneg y))
        _ = convFun (periodicRiesz d s) ρ x := rfl
    · have h0 : convFun (periodicRiesz d s) ρ x = 0 := by
        unfold convFun
        exact integral_undef hint
      rw [h0]
      linarith
  -- the partition function
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = ∫ y, Real.exp (-β * (V y + convFun (periodicRiesz d s) ρ y)) :=
    ⟨_, rfl⟩
  have hth' : ∀ x, ρ x = Real.exp (-β * (V x + convFun (periodicRiesz d s) ρ x)) / Z := by
    intro x
    rw [hZ]
    exact hth x
  have hZnn : 0 ≤ Z := by
    rw [hZ]
    exact integral_nonneg fun y => (Real.exp_pos _).le
  have hZne : Z ≠ 0 := by
    intro h0
    have h1 : ∀ x, ρ x = 0 := fun x => by rw [hth' x, h0, div_zero]
    have h2 := hprob.integral_one
    simp only [h1, integral_zero] at h2
    norm_num at h2
  have hZpos : 0 < Z := lt_of_le_of_ne hZnn (Ne.symm hZne)
  -- integrability of the exponent and of its exponential
  have hΦi : Integrable (fun x => -β * (V x + convFun (periodicRiesz d s) ρ x)) :=
    ((q32a_integrable_of_continuous hVc).add hui).const_mul _
  have hEi : Integrable (fun x => Real.exp (-β * (V x + convFun (periodicRiesz d s) ρ x))) := by
    have e : (fun x => Real.exp (-β * (V x + convFun (periodicRiesz d s) ρ x)))
        = fun x => ρ x * Z := by
      funext x
      rw [hth' x, div_mul_cancel₀ _ hZne]
    rw [e]
    exact hρi.mul_const Z
  -- Jensen: `exp (∫ Φ) ≤ ∫ exp Φ = Z`
  have hJ : Real.exp (∫ x, -β * (V x + convFun (periodicRiesz d s) ρ x))
      ≤ ∫ x, Real.exp (-β * (V x + convFun (periodicRiesz d s) ρ x)) :=
    ConvexOn.map_integral_le (convexOn_exp) Real.continuous_exp.continuousOn isClosed_univ
      (Filter.Eventually.of_forall fun x => Set.mem_univ _) hΦi hEi
  -- the integral of the exponent
  have hIV : ∫ x, V x ≤ M := by
    have := integral_mono (q32a_integrable_of_continuous hVc) (integrable_const M)
      (fun x => (abs_le.mp (hVM x)).2)
    simpa using this
  have hΦint : ∫ x, -β * (V x + convFun (periodicRiesz d s) ρ x)
      = -β * ((∫ x, V x) + ∫ x, periodicRiesz d s x) := by
    rw [integral_const_mul, integral_add (q32a_integrable_of_continuous hVc) hui, huI]
  have hlow : -(β * (M + |∫ x, periodicRiesz d s x|))
      ≤ ∫ x, -β * (V x + convFun (periodicRiesz d s) ρ x) := by
    rw [hΦint]
    have hsum : (∫ x, V x) + (∫ x, periodicRiesz d s x)
        ≤ M + |∫ x, periodicRiesz d s x| := by
      linarith [le_abs_self (∫ x, periodicRiesz d s x)]
    have := mul_le_mul_of_nonneg_left hsum hβ
    linarith
  set K : ℝ := β * (M + |∫ x, periodicRiesz d s x|) with hK
  have hZlow : Real.exp (-K) ≤ Z := by
    have h1 : Real.exp (-K) ≤ Real.exp (∫ x, -β * (V x + convFun (periodicRiesz d s) ρ x)) :=
      Real.exp_le_exp.mpr hlow
    rw [hZ]
    exact h1.trans hJ
  -- pointwise upper bound of the exponent
  refine ⟨Real.exp (β * (M + max B 0) + K), fun x => ?_⟩
  have hup : -β * (V x + convFun (periodicRiesz d s) ρ x) ≤ β * (M + max B 0) := by
    have hv := (abs_le.mp (hVM x)).1
    have hu := hu_lb x
    have h2 : -(M + max B 0) ≤ V x + convFun (periodicRiesz d s) ρ x := by linarith
    have := mul_le_mul_of_nonneg_left h2 hβ
    linarith
  rw [hth' x, div_le_iff₀ hZpos]
  calc Real.exp (-β * (V x + convFun (periodicRiesz d s) ρ x))
      ≤ Real.exp (β * (M + max B 0)) := Real.exp_le_exp.mpr hup
    _ = Real.exp (β * (M + max B 0) + K) * Real.exp (-K) := by
        rw [← Real.exp_add]
        congr 1
        ring
    _ ≤ Real.exp (β * (M + max B 0) + K) * Z :=
        mul_le_mul_of_nonneg_left hZlow (Real.exp_pos _).le

end HRS

end
