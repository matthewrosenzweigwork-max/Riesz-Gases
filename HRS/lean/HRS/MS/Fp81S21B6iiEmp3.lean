import HRS.MS.Fp81S21B6iiEmp2
import HRS.MS.Fp81S21WeightedMomentsS3

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

private theorem fp81s21_b6ii_moving_density_clip_continuous
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) :
    Continuous (fun q : ℝ × Euc p.d =>
      R.ρ ((max q.1 0).toNNReal) q.2) := by
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have hρeq : R.ρβ = HRS.Whole.thermalDensity p.d p.s p.a p.β :=
    HRS.MS.Mov0.mv0_rho_eq p.hd p.hs0 hsd p.ha p.hβ R.thermal
  have hρβc : Continuous R.ρβ := by
    obtain ⟨-, ψ', hψ'⟩ := HRS.MS.S21.s21_schwartz_thermal
      p.hd p.hs0 hsd p.ha p.hβ
    rw [hρeq, ← hψ']
    exact ψ'.continuous
  have hρβpos : ∀ x, 0 < R.ρβ x :=
    fun x => HRS.Whole.u4_thermal_pos R.thermal x
  have hm : (p.d : ℝ) / 2 < ((102 * p.d + 1020 : ℕ) : ℝ) := by
    rw [HRS.MS.R2WinOrbNL.s103n_cast_m]
    nlinarith
  have hclass := HRS.MS.R2WinOrbNL.s103n_small_class R.resulting
    (r := p.C₁ * δ) le_rfl
  have hjoint := HRS.MS.R2S11.s11_class_continuous hρβc hρβpos hm hclass
  have hmap : Continuous (fun q : ℝ × Euc p.d =>
      ((max q.1 0).toNNReal, q.2)) := by
    fun_prop
  exact hjoint.comp hmap


private theorem fp81s21_b6ii_weighted_reference_integrable
    {d : ℕ} {ρ : Euc d → ℝ} {C₀ c₀ Pw : ℝ}
    (hρ : HRS.Whole.IsProbDensity ρ) (hc₀ : 0 < c₀) (hPw : 0 ≤ Pw)
    (hG : HRS.Whole.HasR2GaussianUpper C₀ c₀ ρ) :
    Integrable (fun x : Euc d => jbracket x ^ Pw)
      (HRS.Whole.withDensityReal ρ) := by
  obtain ⟨C, hC₀, hC⟩ := HRS.MS.R2Poly.s95_moment d C₀ c₀ hc₀
    (Pw := Pw / 2) (by linarith)
  have hpow : ∀ x : Euc d, (jbracket x ^ (Pw / 2)) ^ 2 = jbracket x ^ Pw := by
    intro x
    have hj : 0 < jbracket x := lt_of_lt_of_le zero_lt_one
      (HRS.MS.R2Poly.s95_one_le_jb x)
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hj)]
    congr 1
    ring
  have hbound :
      (∫⁻ x, ENNReal.ofReal (jbracket x ^ Pw)
        ∂(HRS.Whole.withDensityReal ρ)) ≤ ENNReal.ofReal C := by
    calc
      _ = ∫⁻ x, ENNReal.ofReal ((jbracket x ^ (Pw / 2)) ^ 2)
          ∂(HRS.Whole.withDensityReal ρ) := by
            refine lintegral_congr fun x => ?_
            rw [hpow]
      _ ≤ ENNReal.ofReal C := hC ρ hρ hG.2
  have hjb : Continuous (fun x : Euc d => jbracket x) := by
    unfold jbracket
    fun_prop
  have hmeas : Measurable (fun x : Euc d => jbracket x ^ Pw) :=
    (hjb.rpow_const fun x => Or.inl
      (zero_lt_one.trans_le (HRS.MS.R2Poly.s95_one_le_jb x)).ne').measurable
  have hnonneg : ∀ x : Euc d, 0 ≤ jbracket x ^ Pw := fun x =>
    Real.rpow_nonneg (Real.sqrt_nonneg _) _
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  calc
    ∫⁻ x, ‖jbracket x ^ Pw‖ₑ ∂(HRS.Whole.withDensityReal ρ) =
        ∫⁻ x, ENNReal.ofReal (jbracket x ^ Pw)
          ∂(HRS.Whole.withDensityReal ρ) := by
            refine lintegral_congr fun x => ?_
            rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hnonneg x)]
    _ ≤ ENNReal.ofReal C := hbound
    _ < ⊤ := ENNReal.ofReal_lt_top

/-- A clipped reference family has the integrability and time measurability
needed to build the common-time empirical representative. -/
theorem fp81s21_emp_reference_data (p : Parameters)
    (E : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4)) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ μ : ℝ → Measure (Euc p.d),
          (∀ u, 0 ≤ u → μ u = r26t3_mu R u) ∧
          (∀ u, Integrable (fun x : Euc p.d => jbracket x ^ ((p.d : ℝ) + 4)) (μ u)) ∧
          (∀ j, Measurable (fun u => HRS.Whole.pair (μ u) (E.test j))) := by
  obtain ⟨δ0, hδ0, hδhalf, hUniform⟩ := fp81s21_uniform_density_moments p
  refine ⟨δ0, hδ0, hδhalf, ?_⟩
  intro δ hδ hδle R
  obtain ⟨pinf, K, C₀, c₀, M, L, Mρ, Cm, hpinf, hc₀,
    hGaussian, hRound2, hReferenceMoment, hParticle⟩ := hUniform δ hδ hδle R
  let μ : ℝ → Measure (Euc p.d) := fun u => HRS.Whole.withDensityReal (R.ρ (max u 0))
  refine ⟨μ, ?_, ?_, ?_⟩
  · intro u hu
    simp [μ, r26t3_mu, max_eq_left hu]
  · intro u
    exact fp81s21_b6ii_weighted_reference_integrable
      (hRound2 (max u 0) (le_max_right _ _)).prob hc₀ (by positivity)
      (hGaussian (max u 0) (le_max_right _ _))
  · intro j
    have hρjoint : Measurable (fun q : ℝ × Euc p.d => R.ρ (max q.1 0) q.2) := by
      simpa using (fp81s21_b6ii_moving_density_clip_continuous p R hδ
        (hδle.trans hδhalf)).measurable
    have hρnonneg : ∀ u x, 0 ≤ R.ρ (max u 0) x := by
      intro u x
      exact (hRound2 (max u 0) (le_max_right _ _)).prob.nonneg x
    have htest : Measurable (fun q : ℝ × Euc p.d => E.test j q.2) :=
      ((E.test_smooth j).1.continuous.measurable).comp measurable_snd
    have hint : Measurable (fun u => ∫ x, E.test j x ∂μ u) := by
      simpa [μ] using fp81s21_moving_spatial_integral_meas hρjoint hρnonneg htest
    simpa [HRS.Whole.pair] using hint

#print axioms fp81s21_emp_reference_data
end HRS.Fp81.S21
end
