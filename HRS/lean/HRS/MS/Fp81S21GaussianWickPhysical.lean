import HRS.MS.Fp81S21GaussianPhysicalPackage
import HRS.MS.Fp81S21MovingOscOrbitApprox
import HRS.MS.S111K4ATE
import HRS.MS.S111K4ATK

/-! Arbitrary oscillator evaluations of the actual selected D and J.
The coefficient histories are the retained ones; their time-a.e. chart
agreement transfers both the integrals and their integrability. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.S111K2
open HRS.MS.S111K4J01 HRS.MS.S111K4AT HRS.MS.ProClosureS111

private theorem fp81s21_wick_physical_interval_coordinates
    {d r : ℕ} {Pw T a c K : ℝ} {E : r26t6_WeightedChart d r Pw}
    {C : WholeCoeff d} (ha : 0 ≤ a) (hH : 0 ≤ a + T)
    (hP : (d : ℝ) < 2 * Pw)
    (horb : K4OscOrbitApprox C (wholeSpaceIndex d : ℝ) (a + T) r)
    (hco : r26t6_ChartedOrbits E C (wholeSpaceIndex d) (a + T))
    (O : r26t6_IntervalOperators E C T a c K) (q : r26t6_TimeCoeff (a + T)) :
    ((∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) (a + T)),
        inner ℝ (q s) (E.encode (fun _ => 1)) = 0) →
      AllDriftCoordinates C (wholeSpaceIndex d : ℝ) T a
        (r26t6_coefficientField E q) (a + T) (O.drift 0 (a + T) q)) ∧
    AllShiftedJValue C (wholeSpaceIndex d : ℝ) T a
      (r26t6_coefficientField E q) (a + T) (O.covariance 0 (a + T) q) := by
  have hsm := Lp.stronglyMeasurable q
  have hint := (Lp.memLp q).integrable le_rfl
  have hz := zQ_L1F (nativeChartOfFrozen E) hsm hint.hasFiniteIntegral
  have hJm := zQ_JMeas (nativeChartOfFrozen E) hco hsm
  have hdm : S111k2DriftIntegrandMeas C (wholeSpaceIndex d : ℝ) T a
      (r26t6_coefficientField E q) := by
    intro t ht φ hφ
    exact (hsm.aestronglyMeasurable.inner
      (hco.2 t ⟨ha.trans ht.1, ht.2⟩ φ hφ)).aemeasurable
  have hNm : Measurable (fun s : ℝ => ENNReal.ofReal ‖q s‖) :=
    hsm.measurable.norm.ennreal_ofReal
  have hN : ∫⁻ s in Icc (0 : ℝ) (a + T), ENNReal.ofReal ‖q s‖ < ⊤ := by
    simpa [HasFiniteIntegral] using hint.hasFiniteIntegral
  have hzN : ∀ s ∈ Icc (0 : ℝ) (a + T),
      dualNormE r Pw (r26t6_coefficientField E q s) ≤ ENNReal.ofReal ‖q s‖ :=
    fun s _ => dualNormE_coefficientField_le (nativeChartOfFrozen E) q s
  constructor
  · intro hq0
    exact k4_all_tests_drift ha hP horb hz hNm hN hzN hdm _
      (O.drift_coordinate q hq0 0 (a + T) le_rfl hH le_rfl)
  · exact k4_all_tests_cov ha hP horb hz hNm hN hzN hJm _
      (O.covariance_coordinate q 0 (a + T) le_rfl hH le_rfl)

variable {p : Parameters} {δ : ℝ} {R : Trajectory p δ}

/-- All-test time-density formulas for the literal full-horizon physical D/J.
The radius precedes the selected physical package and the window start. -/
theorem fp81s21_gaussian_wick_physical_coordinates (p : Parameters) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
      ∀ Q : fp81s21_Physical35 p R, ∀ (a : ℝ) (ha : 0 ≤ a),
      (∀ᵐ ω ∂Q.src.G0.P,
        AllDriftCoordinates (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) p.T a
          (fun s f => fp81s21_chartAction Q.E (Q.S.qe Q.src.G0 s ω) f)
          (a + p.T) (fp81s21_physical35_D Q.tofp81s21_Gaussian35Selection Q.OD a ω)) ∧
      (∀ᵐ ω ∂Q.src.G0.P,
        AllShiftedJValue (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) p.T a
          (fun s f => fp81s21_chartAction Q.E
            (fp81s21_gaussian_embedFamily p Q.Es Q.E (Q.canon.q Q.src.G0) s ω) f)
          (a + p.T) (fp81s21_physical35_J Q.tofp81s21_Gaussian35Selection Q.OJ a ω)) := by
  obtain ⟨δo, ho, hhalf, horb⟩ := fp81s21_moving_osc_orbit_approx p
  obtain ⟨δs, hs, _, hstd⟩ := fp81s21_moving_std p
  refine ⟨min δo δs, lt_min ho hs, (min_le_left _ _).trans hhalf, ?_⟩
  intro δ hδ hδle R Q a ha
  have hH : 0 < a + p.T := add_pos_of_nonneg_of_pos ha p.hT
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by
    linarith [Nat.cast_nonneg p.d (α := ℝ)]
  have ho := horb δ hδ (hδle.trans (min_le_left _ _)) R a ha
  obtain ⟨coef, hdata⟩ := hstd δ hδ (hδle.trans (min_le_right _ _)) R a ha
  have hco := fp81s21_moving_charted_orbits p R hH hdata hP Q.E
  have hB := (fp81s21_TimeL2Rep_toL1_chart Q.E Q.src.G0.P _ _ 0
    (a + p.T) hH.le (Q.UB a ha) (Q.hUB a ha)).2
  have hG := (fp81s21_TimeL2Rep_toL1_chart Q.E Q.src.G0.P _ _ 0
    (a + p.T) hH.le (Q.UG a ha) (Q.hUG a ha)).2
  have hmass := fp81s21_quadraticPhysical31_zero_mass p R Q.Es Q.E Q.S
    Q.src.G0 (a + p.T) hH.le
  simp only [zero_add] at hB hG
  constructor
  · filter_upwards [hB, hmass] with ω hrep hm
    let q := fp81s21_timeL2L1 (a + p.T) hH.le (Q.UB a ha ω)
    have hq0 : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) (a + p.T)),
        inner ℝ (q s) (Q.E.encode (fun _ => 1)) = 0 := by
      filter_upwards [hrep, hm] with s hs hs0
      exact (hs (fun _ => 1)).trans hs0
    have hc := (fp81s21_wick_physical_interval_coordinates ha hH.le hP ho hco
      (Q.OD a ha) q).1 hq0
    intro τ φ hφ
    have hsub : Icc (0 : ℝ) (min (a + p.T) (a + τ)) ⊆ Icc 0 (a + p.T) :=
      Icc_subset_Icc_right (min_le_left _ _)
    have he : (fun s => r26t6_coefficientField Q.E q s
        (propagatorW (r26t3_coeff R) s (a + τ) φ)) =ᵐ[
          volume.restrict (Icc (0 : ℝ) (min (a + p.T) (a + τ)))]
        (fun s => fp81s21_chartAction Q.E (Q.S.qe Q.src.G0 s ω)
          (propagatorW (r26t3_coeff R) s (a + τ) φ)) := by
      filter_upwards [ae_mono (Measure.restrict_mono hsub le_rfl) hrep] with s hs
      exact hs _
    refine ⟨(hc τ φ hφ).1.congr he, ?_⟩
    simpa only [fp81s21_physical35_D, dif_pos ha, fp81s21_gaussian_Dcum] using
      (hc τ φ hφ).2.trans (integral_congr_ae he)
  · filter_upwards [hG] with ω hrep
    let q := fp81s21_timeL2L1 (a + p.T) hH.le (Q.UG a ha ω)
    have hc := (fp81s21_wick_physical_interval_coordinates ha hH.le hP ho hco
      (Q.OJ a ha) q).2
    intro ta tb φ ψ hφ hψ
    have hsub : Icc (0 : ℝ) (min (a + p.T) (min (a + ta) (a + tb))) ⊆
        Icc 0 (a + p.T) := Icc_subset_Icc_right (min_le_left _ _)
    have he : (fun s => r26t6_coefficientField Q.E q s (fun x =>
        inner ℝ (gradient (propagatorW (r26t3_coeff R) s (a + ta) φ) x)
          (gradient (propagatorW (r26t3_coeff R) s (a + tb) ψ) x))) =ᵐ[
          volume.restrict (Icc (0 : ℝ) (min (a + p.T) (min (a + ta) (a + tb))))]
        (fun s => fp81s21_chartAction Q.E
          (fp81s21_gaussian_embedFamily p Q.Es Q.E (Q.canon.q Q.src.G0) s ω)
          (fun x => inner ℝ (gradient (propagatorW (r26t3_coeff R) s (a + ta) φ) x)
            (gradient (propagatorW (r26t3_coeff R) s (a + tb) ψ) x))) := by
      filter_upwards [ae_mono (Measure.restrict_mono hsub le_rfl) hrep] with s hs
      exact hs _
    refine ⟨(hc ta tb φ ψ hφ hψ).1.congr he, ?_⟩
    intro l₁ l₂ hl₁ hl₂
    have hv := (hc ta tb φ ψ hφ hψ).2 l₁ l₂ hl₁ hl₂
    have hi := congrArg (fun x : ℝ => 2 * (r26t3_coeff R).ν * x)
      (integral_congr_ae he)
    simpa only [fp81s21_physical35_J, dif_pos ha, fp81s21_gaussian_Jcum] using hv.trans hi

end HRS.Fp81.S21
#print axioms HRS.Fp81.S21.fp81s21_gaussian_wick_physical_coordinates
end
