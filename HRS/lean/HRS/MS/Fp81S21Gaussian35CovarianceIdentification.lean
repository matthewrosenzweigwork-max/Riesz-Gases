import HRS.MS.Fp81S21GaussianCovPhysical
import HRS.MS.S111K4J01I
import HRS.MS.Fp81S21DualMeas3

/-! Packet 35, unit 4: the selected coefficient covariance is the packet-16
window covariance measure.  No Gaussian35 selection record is needed.

The plan's joint measurability input is explicit as `hqG`; `TimeL2Rep`
provides the samplewise L² bound and representative equality, not this
pointwise measurability.  Charts precede radii, and localization constants
precede the window start.  All conclusions of `gaussian_Jcum_physical`
are retained, with the sample event preceding every endpoint in JMeasure.
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.S111K2
open HRS.MS.ProClosureS111 HRS.MS.S111K4J01

local instance fp81s21_Gaussian35CovarianceIdentification_inst1 (H : ℝ) :
    MeasurableSpace (Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) H))) := borel _
local instance fp81s21_Gaussian35CovarianceIdentification_inst2 (H : ℝ) :
    BorelSpace (Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) H))) := ⟨rfl⟩

/-- Generic physical covariance identification for any selected measurable
coefficient field, compatible L² history, and physical interval operators. -/
theorem fp81s21_gaussian35_J_physical
    (p : Parameters)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
      ∃ Cmix cdec : ℝ, 0 ≤ Cmix ∧ 0 < cdec ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω],
      ∀ (P : Measure Ω) (qG : ℝ → Ω → r26t6_Coeff) (MG : ℝ),
      Measurable (fun z : ℝ × Ω => qG z.1 z.2) →
      ∀ (a : ℝ) (ha : 0 ≤ a) (c K : ℝ), 0 ≤ c → 0 ≤ K →
      ∀ (O : r26t6_IntervalOperators E (r26t3_coeff R) p.T a c K)
        (UG : Ω → Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) (a + p.T)))),
      fp81s21_TimeL2Rep P qG MG 0 (a + p.T) UG →
      let VG := fun ω => fp81s21_timeL2L1 (a + p.T) (add_nonneg ha p.hT.le) (UG ω)
      let Jcum := fp81s21_gaussian_Jcum O (add_nonneg ha p.hT.le) UG
      let QG := fun s ω f => fp81s21_chartAction E (qG s ω) f
      (∀ v r, 0 ≤ v → v ≤ r → r ≤ a + p.T → ∀ᵐ ω ∂P,
        fp81s21_IsWindowJValue (r26t3_coeff R) (wholeSpaceIndex p.d) p.T a
          (fun s f => QG s ω f) (Ioc v r)
          ((Jcum r ω - Jcum v ω : projTensor (R2X p.d p.T) 2) :
            TensorDual (R2X p.d p.T) 2)) ∧
      (∀ᵐ ω ∂P, ∃ I : fp81s21_WindowLocalInput (r26t3_coeff R)
          (wholeSpaceIndex p.d) p.T a (2 * p.d + 8) ((p.d : ℝ) + 2)
          (fun s f => QG s ω f) Cmix cdec,
        ∀ v r, 0 ≤ v → v ≤ r → r ≤ a + p.T →
          Jcum r ω - Jcum v ω = fp81s21_window_covariance_measure I v r) ∧
      ((∀ r, AEStronglyMeasurable (Jcum r) P) ∧
        (∀ ω, ContinuousOn (fun r => Jcum r ω) (Icc 0 (a + p.T)) ∧
          BoundedVariationOn (fun r => Jcum r ω) (Icc 0 (a + p.T))) ∧
        (∀ v r, 0 ≤ v → v ≤ r → r ≤ a + p.T → ∀ ω,
          Jcum r ω - Jcum v ω = O.covariance v r (VG ω)) ∧
        (∀ v r, 0 ≤ v → v ≤ r → r ≤ a + p.T → ∀ ω,
          eVariationOn (fun s => Jcum s ω) (Icc v r) ≤ ENNReal.ofReal
            (K * |2 * (r26t3_coeff R).ν| * ∫ s in Ioc v r,
              s111k2_age c a s ^ 2 * ‖VG ω s‖))) ∧
      (∀ r, 0 ≤ r → r ≤ a + p.T → ∀ ω,
        ∀ M : R2X p.d p.T [×2]→L[ℝ] ℝ,
          ((Jcum r ω : projTensor (R2X p.d p.T) 2) : TensorDual (R2X p.d p.T) 2) M =
          ((Jcum r ω : projTensor (R2X p.d p.T) 2) : TensorDual (R2X p.d p.T) 2)
            (M.domDomCongr (Equiv.swap 0 1))) := by
  obtain ⟨δm, hδm, hδmh, hmeasure⟩ := fp81s21_window_covariance_measure_physical' p
  obtain ⟨δs, hδs, hδsh, hstd⟩ := fp81s21_moving_std p
  refine ⟨min δm δs, lt_min hδm hδs, (min_le_left _ _).trans hδmh, ?_⟩
  intro δ hδ hδle R
  obtain ⟨Cs0, cdec, Cmix, Km, hCs0, hcdec, hsumb, hCmix, hCs0mix, hKm, hbody⟩ :=
    hmeasure δ hδ (hδle.trans (min_le_left _ _)) R
  refine ⟨Cmix, cdec, hCmix, hcdec, ?_⟩
  intro Ω instΩ P qG MG hqG a ha c K hc hK O UG hUG
  dsimp only
  let H := a + p.T
  have hH : 0 ≤ H := add_nonneg ha p.hT.le
  let VG := fun ω => fp81s21_timeL2L1 H hH (UG ω)
  let Jcum := fp81s21_gaussian_Jcum O hH UG
  obtain ⟨hmeas, hreg, hadd, hphys, hsymm, hvar⟩ :=
    fp81s21_gaussian_Jcum_physical E (r26t3_coeff R) P qG MG a p.T c K
      ha p.hT hc hK O UG hUG
  refine ⟨hphys, ?_, ⟨hmeas, hreg, hadd, hvar⟩, hsymm⟩
  have hPw : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by
    linarith [Nat.cast_nonneg p.d (α := ℝ)]
  obtain ⟨b, hb⟩ := hstd δ hδ (hδle.trans (min_le_right _ _)) R a ha
  have hchart := fp81s21_moving_charted_orbits p R
    (show 0 < a + p.T from add_pos_of_nonneg_of_pos ha p.hT) hb hPw E
  have hbridge := (fp81s21_TimeL2Rep_toL1_chart E P qG MG 0 H hH UG hUG).2
  filter_upwards [hUG.2.2.2, hbridge] with ω hsection hrep
  have hQ : StronglyMeasurable (fun s => qG s ω) :=
    (hqG.comp (measurable_id.prodMk measurable_const)).stronglyMeasurable
  have hint : Integrable (fun s => qG s ω) (volume.restrict (Icc (0 : ℝ) H)) := by
    simpa only [zero_add] using hsection.1.integrable one_le_two
  have hz : IsR2L1F (2 * p.d + 8) ((p.d : ℝ) + 2) H
      (fun s f => fp81s21_chartAction E (qG s ω) f) :=
    zQ_L1F (nativeChartOfFrozen E) hQ hint.hasFiniteIntegral
  have hm : R2JIntegrandMeas (r26t3_coeff R) (wholeSpaceIndex p.d) H
      (fun s f => fp81s21_chartAction E (qG s ω) f) :=
    zQ_JMeas (nativeChartOfFrozen E) hchart hQ
  obtain ⟨I, I', Isum, Ismul, hI⟩ := hbody a ha ((p.d : ℝ) + 2) hPw
    (fun s f => fp81s21_chartAction E (qG s ω) f)
    (fun s f => fp81s21_chartAction E (qG s ω) f) 1 hz hz hm hm
  refine ⟨I, ?_⟩
  intro v r hv hvr hr
  rw [hadd v r hv hvr hr ω]
  apply fp81s21_interval_covariance_eq_physical O (VG ω) I hv hvr hr
  · exact (hI v r hv hvr hr).2.2.2.2.2.2.2.1
  · intro ta tb φ ψ hφ hψ hta htb
    have hbase : ∀ᵐ s ∂volume.restrict (Icc (0 : ℝ) H), ∀ f,
        r26t6_coefficientField E (VG ω) s f = fp81s21_chartAction E (qG s ω) f := by
      simpa only [zero_add] using hrep
    have hsub : Ioc v r ∩ Icc 0 (min (a + ta) (a + tb)) ⊆ Icc (0 : ℝ) H := by
      intro s hs
      exact ⟨hv.trans hs.1.1.le, hs.1.2.trans hr⟩
    have hrestricted := ae_mono (Measure.restrict_mono hsub le_rfl) hbase
    filter_upwards [hrestricted] with s hs
    exact hs _

#print axioms fp81s21_gaussian35_J_physical

end HRS.Fp81.S21
