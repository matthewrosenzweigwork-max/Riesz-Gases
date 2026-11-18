import HRS.MS.S111K4J02G
import HRS.MS.S111K4ATE
import HRS.MS.S111K4ATK

/-!
# S11.1 / J02, piece H (S111K4): the coordinate clause of `random_interval_L2`, a.e. `ω`, all `v`
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4J01

open HRS HRS.Whole HRS.MS.S111K2

theorem k4_random_coordinates {d r : ℕ} {Pw : ℝ} (T u c0 B : ℝ) (hu : 0 ≤ u)
    {E : WeightedChart d r Pw} {C : WholeCoeff d}
    (hco : ChartedOrbits E C (wholeSpaceIndex d : ℝ) (u + T))
    (hP : (d : ℝ) < 2 * Pw)
    (horb : HRS.MS.S111K4AT.K4OscOrbitApprox C (wholeSpaceIndex d : ℝ) (u + T) r)
    (O : IntervalOperators E C T u c0 B)
    {Omega : Type*} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (q : ℝ × Omega → Coeff) (hqm : Measurable q)
    (hq : MemLp q 2 ((volume.restrict (Set.Icc 0 (u + T))).prod P))
    (hq0 : ∀ p, inner ℝ (q p) (E.encode (fun _ => 1)) = 0)
    :
    ∀ᵐ w ∂P, ∀ v ∈ Set.Icc 0 (u + T),
      AllDriftCoordinates C (wholeSpaceIndex d : ℝ) T u
        (coefficientField E (fun z => q (z, w))) v (randomDrift O q v w) ∧
      AllShiftedJValue C (wholeSpaceIndex d : ℝ) T u
        (coefficientField E (fun z => q (z, w))) v (randomCovariance O q v w) := by
  filter_upwards [k4j_slice_memLp1 hq] with w hmem
  intro v hv
  have hsm : StronglyMeasurable (fun z => q (z, w)) := (hqm.comp measurable_prodMk_right).stronglyMeasurable
  have hint : ∫⁻ z in Set.Icc (0 : ℝ) (u + T), ‖q (z, w)‖ₑ < ⊤ := (memLp_one_iff_integrable.1 hmem).2
  have htc : timeCoeffOf (u + T) q w = hmem.toLp (fun z => q (z, w)) := by
    unfold timeCoeffOf; rw [dif_pos hmem]
  have hae : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) (u + T))),
      ((timeCoeffOf (u + T) q w : TimeCoeff (u + T)) : ℝ → Coeff) x = q (x, w) := by
    rw [htc]; exact hmem.coeFn_toLp
  have hq0Q : ∀ᵐ x ∂(volume.restrict (Set.Icc (0 : ℝ) (u + T))),
      inner ℝ (((timeCoeffOf (u + T) q w : TimeCoeff (u + T)) : ℝ → Coeff) x) (E.encode (fun _ => 1)) = 0 :=
    hae.mono fun x hx => by rw [hx]; exact hq0 (x, w)
  obtain ⟨hz, hJm⟩ := admQ E hco hsm hint
  have hdm : S111k2DriftIntegrandMeas C (wholeSpaceIndex d : ℝ) T u
      (coefficientField E (fun z => q (z, w))) := by
    intro t ht phi hphi
    have ht0 : t ∈ Set.Icc (0 : ℝ) (u + T) := ⟨hu.trans ht.1, ht.2⟩
    exact (hsm.aestronglyMeasurable.inner (hco.2 t ht0 phi hphi)).aemeasurable
  have hNm : Measurable fun s : ℝ => ENNReal.ofReal ‖q (s, w)‖ :=
    ENNReal.measurable_ofReal.comp (hsm.measurable.norm)
  have hN : ∫⁻ s in Set.Icc (0 : ℝ) (u + T), ENNReal.ofReal ‖q (s, w)‖ < ⊤ := by
    simpa [ofReal_norm_eq_enorm] using hint
  have hzN : ∀ s ∈ Set.Icc (0 : ℝ) (u + T),
      dualNormE r Pw (coefficientField E (fun z => q (z, w)) s) ≤ ENNReal.ofReal ‖q (s, w)‖ :=
    fun s _ => dualNormE_coefficientField_le E (fun z => q (z, w)) s
  constructor
  · refine HRS.MS.S111K4AT.k4_all_tests_drift hu hP horb hz hNm hN hzN hdm _ (fun tau phi hphi => ?_)
    show OscDual.eval (OscPath.at' (O.drift 0 v (timeCoeffOf (u + T) q w)) tau) phi = _
    rw [O.drift_coordinate _ hq0Q 0 v le_rfl hv.1 hv.2 tau phi hphi]
    exact k4j_drift_coord_congr E hae hv.2 tau phi
  · refine HRS.MS.S111K4AT.k4_all_tests_cov hu hP horb hz hNm hN hzN hJm _ ?_
    refine k4j_ShiftedJValue_congr le_rfl hv.2 (hae.mono fun x hx => ?_)
      (O.covariance_coordinate (timeCoeffOf (u + T) q w) 0 v le_rfl hv.1 hv.2)
    funext f
    simp only [coefficientField, hx]

end HRS.MS.S111K4J01
