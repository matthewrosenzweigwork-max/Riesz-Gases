import HRS.MS.Fp81S21GaussianPredictionAdapted2
import HRS.MS.Fp81S21GaussianPhysicalPackage

/-! Packet 36A: the continuous prediction with exactly past-measurable section
representatives. A measurable inverse on countably many window coordinates
avoids any assertion that raw coefficients agree simultaneously at all times.
This constructs the producer directly from the retained source. It does not
identify its sections with a separately selected FutureIndep39 past path. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.R2Interp HRS.MS.GenPath

/-- One cutoff-continuous physical prediction family; every cutoff section has
an ambient measurable representative measurable in the exact retained past.
The radius precedes every realization, chart, selection and time shift. -/
theorem fp81s21_gaussian_prediction_continuous_ae_adapted (p : Parameters) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
      ∀ Q : fp81s21_Physical35 p R, ∀ a : ℝ, 0 ≤ a →
      ∃ Y : Q.src.G0.Ω → C(Icc (0 : ℝ) (a + p.T), Window p),
        Measurable Y ∧
        (∀ r : Icc (0 : ℝ) (a + p.T), ∃ Yr : Q.src.G0.Ω → Window p,
          Measurable Yr ∧
          Measurable[MeasurableSpace.comap
            (fp81s21_predictionPast Q.tofp81s21_Gaussian35Selection (r : ℝ)) inferInstance] Yr ∧
          (fun ω => Y ω r) =ᵐ[Q.src.G0.P] Yr) ∧
        (∀ r : Icc (0 : ℝ) (a + p.T), ∀ τ : Icc (0 : ℝ) p.T,
          ∀ᵐ ω ∂Q.src.G0.P,
            OscPath.at' (Y ω r) τ =
              r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
                (a + τ) (min (r : ℝ) (a + τ))
                (fp81s21_chartAction Q.E (fp81s21_gaussian35_qG
                  Q.tofp81s21_Gaussian35Selection (min (r : ℝ) (a + τ)) ω))) := by
  obtain ⟨δv, hδv, hhalf, hv⟩ := fp81s21_gaussian_prediction_continuous_physical p
  obtain ⟨δd, hδd, _, hd⟩ := fp81s21_uniform_orbit_amplitudes p
  refine ⟨min δv δd, lt_min hδv hδd, (min_le_left _ _).trans hhalf, ?_⟩
  intro δ hδ hδle R Q a ha
  obtain ⟨Y, hYm, _, hphys⟩ := hv δ hδ (hδle.trans (min_le_left _ _)) R
    Q.tofp81s21_Gaussian35Selection a ha
  obtain ⟨Co, co, _, _, hD⟩ := hd δ hδ (hδle.trans (min_le_right _ _)) R
  refine ⟨Y, hYm, ?_, hphys⟩
  intro r
  have hH : 0 < a + p.T := add_pos_of_nonneg_of_pos ha p.hT
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) p.d]
  let u : Icc (0 : ℝ) p.T → ℝ := fun τ => min (r : ℝ) (a + τ)
  have hu (τ : Icc (0 : ℝ) p.T) : u τ ∈ Icc (0 : ℝ) (a + p.T) :=
    ⟨le_min r.property.1 (add_nonneg ha τ.property.1),
      (min_le_left _ _).trans r.property.2⟩
  have ht (τ : Icc (0 : ℝ) p.T) : a + τ ∈ Icc (u τ) (a + p.T) :=
    ⟨min_le_right _ _, by linarith [τ.property.2]⟩
  let V (τ : Icc (0 : ℝ) p.T) : r26t6_Coeff →L[ℝ]
      OscDual p.d (wholeSpaceIndex p.d : ℝ) :=
    fp81s21_chartVprop hP (hD (a + p.T) hH)
      (fp81s21_S102Lin p R (a + p.T)) Q.E (hu τ) (ht τ)
  have hcoeff := fun τ : Icc (0 : ℝ) p.T =>
    fp81s21_gaussian_prediction_coefficient_adapted Q.tofp81s21_Gaussian35Selection
      (u τ) r (hu τ).1 (min_le_left _ _)
  choose q hqm hqp hqeq using hcoeff
  letI : Nonempty (Icc (0 : ℝ) p.T) := ⟨⟨0, le_rfl, p.hT.le⟩⟩
  let s : ℕ → Icc (0 : ℝ) p.T := TopologicalSpace.denseSeq _
  have hs : DenseRange s := TopologicalSpace.denseRange_denseSeq _
  let B : Q.src.G0.Ω → (ℕ × MultiIndex p.d → ℝ) := fun ω i =>
    OscDual.coord (V (s i.1) (q (s i.1) ω)) i.2
  have hBm : Measurable B := measurable_pi_iff.2 fun i =>
    (s56_continuous_coord (wholeSpaceIndex p.d : ℝ) i.2).measurable.comp
      ((V (s i.1)).continuous.measurable.comp (hqm (s i.1)))
  have hBp : Measurable[MeasurableSpace.comap
      (fp81s21_predictionPast Q.tofp81s21_Gaussian35Selection (r : ℝ)) inferInstance] B := by
    letI : MeasurableSpace Q.src.G0.Ω := MeasurableSpace.comap
      (fp81s21_predictionPast Q.tofp81s21_Gaussian35Selection (r : ℝ)) inferInstance
    exact measurable_pi_iff.2 fun i =>
      (s56_continuous_coord (wholeSpaceIndex p.d : ℝ) i.2).measurable.comp
        ((V (s i.1)).continuous.measurable.comp (hqp (s i.1)))
  have hemb := s56_measurableEmbedding_pathCoords (d := p.d)
    (wholeSpaceIndex p.d : ℝ) p.T s hs
  obtain ⟨g, hgm, hg⟩ := hemb.exists_measurable_extend
    (g := id) measurable_id (fun _ => ⟨0⟩)
  refine ⟨fun ω => g (B ω), hgm.comp hBm, hgm.comp hBp, ?_⟩
  have hcoords : ∀ i : ℕ × MultiIndex p.d, ∀ᵐ ω ∂Q.src.G0.P,
      OscDual.coord (OscPath.at' (Y ω r) (s i.1)) i.2 = B ω i := by
    intro i
    filter_upwards [hphys r (s i.1), hqeq (s i.1)] with ω he hq
    change OscPath.at' (Y ω r) (s i.1) =
      V (s i.1) (fp81s21_gaussian35_qG Q.tofp81s21_Gaussian35Selection
        (u (s i.1)) ω) at he
    rw [hq] at he
    exact congrArg (fun z => OscDual.coord z i.2) he
  filter_upwards [ae_all_iff.2 hcoords] with ω hω
  have he : s56PathCoords (wholeSpaceIndex p.d : ℝ) p.T s (Y ω r) = B ω := funext hω
  rw [← he]
  exact (congrFun hg (Y ω r)).symm

#print axioms fp81s21_gaussian_prediction_continuous_ae_adapted
end HRS.Fp81.S21
end
