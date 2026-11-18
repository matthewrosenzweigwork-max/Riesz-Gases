import HRS.Whole.MovtrAux8

/-!
# MOVTR auxiliary 9: translation covariance of the particle system, the modulated energy and the
Gibbs reference law (S6.8 (1), (3), (4))
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole

variable {d : ℕ}

lemma movtr_gradient_confinement (q : ℝ) (x : Euc d) : gradient (confinement q) x = q • x := by
  have h1 : HasGradientAt (confinement (d := d) q) (q • x) x := by
    rw [hasGradientAt_iff_hasFDerivAt]
    have h := (hasStrictFDerivAt_norm_sq x).hasFDerivAt
    have h2 := h.const_mul (q / 2)
    have hf : confinement (d := d) q = fun y => q / 2 * ‖y‖ ^ 2 := by
      funext y; unfold confinement; ring
    rw [hf]
    convert h2 using 1
    ext v
    simp [InnerProductSpace.toDual_apply_apply]
    ring
  exact h1.gradient

/-- The drift is affinely covariant under joint translation. -/
lemma movtr_drift_translate (s q β : ℝ) {N : ℕ} (X : EucConfig d N) (b : Euc d) (i : Fin N) :
    particleDriftW (quadraticGradientDyn d s q β) (fun j => X j + b) i =
      particleDriftW (quadraticGradientDyn d s q β) X i - q • b := by
  unfold particleDriftW quadraticGradientDyn
  simp only [add_sub_add_right_eq_sub, movtr_gradient_confinement]
  rw [smul_add]
  abel


lemma movtr_integral_shift (q : ℝ) (a₀ : Euc d) (t : ℝ) (ht : 0 ≤ t) :
    ∫ s in Set.Icc (0 : ℝ) t, q • (Real.exp (-q * s) • a₀) = a₀ - Real.exp (-q * t) • a₀ := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ht]
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (fun s : ℝ => -(Real.exp (-q * s)) • a₀) (q • (Real.exp (-q * x) • a₀)) x := by
    intro x _
    have h1 : HasDerivAt (fun s : ℝ => Real.exp (-q * s)) (Real.exp (-q * x) * (-q)) x := by
      have := ((hasDerivAt_id x).const_mul (-q)).exp
      refine this.congr_deriv ?_
      simp only [id, mul_one]
    have h2 := (h1.neg).smul_const a₀
    refine h2.congr_deriv ?_
    rw [smul_smul]
    congr 1
    ring
  have hcont : Continuous (fun s : ℝ => q • (Real.exp (-q * s) • a₀)) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  simp
  abel

/-- The translated particle process is again a canonical particle solution. -/
theorem movtr_strong_translate {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (s q β : ℝ) {N : ℕ}
    (T : ℝ) (Y₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (Y : ℝ≥0 → Ω → EucConfig d N)
    (h : IsWholeStrongSolution P (quadraticGradientDyn d s q β) T Y₀ W Y) (a₀ : Euc d) :
    IsWholeStrongSolution P (quadraticGradientDyn d s q β) T (fun ζ i => Y₀ ζ i + a₀) W
      (fun t ζ i => Y t ζ i + Real.exp (-q * (t : ℝ)) • a₀) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · filter_upwards [h.init] with ζ hζ
    funext i
    simp [hζ]
  · filter_upwards [h.eqn] with ζ hζ t ht
    obtain ⟨hint, hsol⟩ := hζ t ht
    have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.coe_nonneg
    have hdr : ∀ (u : ℝ≥0) (i : Fin N),
        particleDriftW (quadraticGradientDyn d s q β)
          (fun j => Y u ζ j + Real.exp (-q * (u : ℝ)) • a₀) i =
        particleDriftW (quadraticGradientDyn d s q β) (Y u ζ) i - q • (Real.exp (-q * (u : ℝ)) • a₀) :=
      fun u i => movtr_drift_translate s q β (Y u ζ) _ i
    have hcontc : Continuous (fun x : ℝ => q • (Real.exp (-q * ((Real.toNNReal x : ℝ≥0) : ℝ)) • a₀)) := by
      have : Continuous (fun x : ℝ => ((Real.toNNReal x : ℝ≥0) : ℝ)) := by fun_prop
      fun_prop
    have hI : ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
        q • (Real.exp (-q * ((Real.toNNReal u : ℝ≥0) : ℝ)) • a₀) =
        a₀ - Real.exp (-q * (t : ℝ)) • a₀ := by
      rw [← movtr_integral_shift q a₀ (t : ℝ) ht0]
      refine setIntegral_congr_fun measurableSet_Icc (fun u hu => ?_)
      simp [Real.coe_toNNReal _ hu.1]
    refine ⟨fun i => ?_, fun i => ?_⟩
    · beta_reduce
      simp only [hdr]
      exact (hint i).sub hcontc.integrableOn_Icc
    · beta_reduce
      simp only [hdr]
      have hsub : ∫ u in Set.Icc (0 : ℝ) (t : ℝ),
          (particleDriftW (quadraticGradientDyn d s q β) (Y (Real.toNNReal u) ζ) i -
            q • (Real.exp (-q * ((Real.toNNReal u : ℝ≥0) : ℝ)) • a₀)) =
          (∫ u in Set.Icc (0 : ℝ) (t : ℝ),
            particleDriftW (quadraticGradientDyn d s q β) (Y (Real.toNNReal u) ζ) i) -
          ∫ u in Set.Icc (0 : ℝ) (t : ℝ), q • (Real.exp (-q * ((Real.toNNReal u : ℝ≥0) : ℝ)) • a₀) :=
        integral_sub (hint i) hcontc.integrableOn_Icc
      rw [hsub, hI, hsol i]
      simp only [NNReal.coe_zero, mul_zero, Real.exp_zero, one_smul]
      abel
  · filter_upwards [h.cont] with ζ hζ i
    have hc : Continuous (fun t : ℝ≥0 => Real.exp (-q * (t : ℝ)) • a₀) := by fun_prop
    exact (hζ i).add hc
  · intro t
    refine measurable_pi_iff.mpr fun i => ?_
    exact ((measurable_pi_iff.mp (h.adapted t) i)).add_const _
  · filter_upwards [h.no_collision] with ζ hζ t ht ⟨i, j, hij, heq⟩
    exact hζ t ht ⟨i, j, hij, add_right_cancel heq⟩

end HRS.Whole
