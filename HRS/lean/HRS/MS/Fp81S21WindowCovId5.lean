import HRS.MS.Fp81S21WindowCovId4
import HRS.MS.Fp81S21WindowCovId3
import HRS.MS.Fp81S21CovCumulative3
import HRS.MS.Fp81S21CovClose4

/-! Physical interval identification for an already selected cumulative. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp HRS.MC.E213O

/-- The physical window constructor identifies all intervals at once with any
previously selected raw-eta cumulative. The three dual-norm hypotheses are
for the extension, its sum with itself, and its scalar multiple by one. -/
theorem fp81s21_physical_window_covariance_selected (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∃ (Cmix cdec : ℝ) (K : ℝ → ℝ),
        ∀ (a : ℝ) (ha : 0 ≤ a) (N : ℕ) (hN : 2 ≤ N) (A : Particle R N),
        Fp81MovingPhysicalInputs R hN A (a + p.T) →
        ∀ Fj : A.Ω → ℝ → projTensor (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2,
        (∀ᵐ ω ∂A.P, ∀ q s, 0 ≤ q → q ≤ s → s ≤ a + p.T →
          IsR2JValue (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) (a + p.T)
            (fp81s21_movingRawEtaField p R A ω) (Ioc q s)
            (((Fj ω s - Fj ω q : projTensor (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2) :
              TensorDual (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2))) →
        (let z := fun ω => fp81s21_horizonFieldExtension (a + p.T)
            (fp81s21_movingRawEtaField p R A ω)
         let P : ℝ := (p.d : ℝ) + 2
         ∀ᵐ ω ∂A.P,
          AEMeasurable (fun v => dualNormE (2 * p.d + 8) P (z ω v))
            (volume.restrict (Icc (0 : ℝ) (a + p.T))) ∧
          AEMeasurable (fun v => dualNormE (2 * p.d + 8) P ((z ω + z ω) v))
            (volume.restrict (Icc (0 : ℝ) (a + p.T))) ∧
          AEMeasurable (fun v => dualNormE (2 * p.d + 8) P (((1 : ℝ) • z ω) v))
            (volume.restrict (Icc (0 : ℝ) (a + p.T)))) →
        ∀ᵐ ω ∂A.P,
          let z := fp81s21_horizonFieldExtension (a + p.T)
            (fp81s21_movingRawEtaField p R A ω)
          let P : ℝ := (p.d : ℝ) + 2
          ∃ (D : fp81s21_WindowLocalInput (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
                p.T a (2 * p.d + 8) P z Cmix cdec)
            (D' : fp81s21_WindowLocalInput (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
                p.T a (2 * p.d + 8) P z Cmix cdec)
            (Dsum : fp81s21_WindowLocalInput (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
                p.T a (2 * p.d + 8) P (z + z) Cmix cdec)
            (Dsmul : fp81s21_WindowLocalInput (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
                p.T a (2 * p.d + 8) P ((1 : ℝ) • z) Cmix cdec),
            ∀ q s, 0 ≤ q → q ≤ s → s ≤ a + p.T →
              tensorPow' 2 (HRS.MS.ProClosureS111.physicalWindowRestriction
                (d := p.d) (m := (wholeSpaceIndex p.d : ℝ))
                (T := p.T) (H := a + p.T) ha le_rfl)
                (((Fj ω s - Fj ω q : projTensor (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2) :
                  TensorDual (OscPath p.d (wholeSpaceIndex p.d : ℝ) (a + p.T)) 2)) =
                ((fp81s21_window_covariance_measure D q s : projTensor (Window p) 2) :
                  TensorDual (Window p) 2) ∧
              fp81s21_covariance_interval_contract D D' Dsum Dsmul (K P) q s := by
  obtain ⟨δ0, hδ0, hhalf, hmain⟩ := fp81s21_window_covariance_measure_physical p
  refine ⟨δ0, hδ0, hhalf, ?_⟩
  intro δ hδ hδle R
  obtain ⟨Cs0, cdec, Cmix, K, _, _, _, _, _, _, hconstruct⟩ := hmain δ hδ hδle R
  refine ⟨Cmix, cdec, K, ?_⟩
  intro a ha N hN A hphysical Fj hfull hdual
  have hH : 0 < a + p.T := by linarith [p.hT]
  have hN0 : 0 < N := by omega
  have hδhalf : δ ≤ 1 / 2 := hδle.trans hhalf
  have hL1 := fp81s21_moving_raw_eta_horizonL1F_ae p R hH hN A hphysical
  have hcont : ∀ᵐ ω ∂A.P, ∀ k : Fin N,
      Continuous fun t : ℝ≥0 => A.X t ω k := (A.strong (a + p.T)).cont
  filter_upwards [hL1, hcont, hfull, hdual] with ω hL1 hcont hfull hdual
  let z := fp81s21_horizonFieldExtension (a + p.T) (fp81s21_movingRawEtaField p R A ω)
  let P : ℝ := (p.d : ℝ) + 2
  have hP : (p.d : ℝ) < 2 * P := by
    dsimp [P]
    have hd : 0 ≤ (p.d : ℝ) := by positivity
    linarith
  have hm := fp81s21_R2JIntegrandMeas_horizonFieldExtension
    (fp81s21_moving_raw_eta_JIntegrandMeas p R hδ hδhalf hH hN0 A.X ω hcont)
  obtain ⟨D, D', Dsum, Dsmul, hwindow⟩ :=
    hconstruct a ha P hP z z 1 hL1 hL1 hm hm hdual.1 hdual.1 hdual.2.1 hdual.2.2
  refine ⟨D, D', Dsum, Dsmul, ?_⟩
  apply fp81s21_window_covariance_interval_identification p.hT ha D D' Dsum Dsmul (K P) (Fj ω) ?_ hwindow
  intro q s hq hqs hs
  exact fp81s21_JValue_horizonFieldExtension _ _ _ (hfull q s hq hqs hs)

end HRS.Fp81.S21
end
#print axioms HRS.Fp81.S21.fp81s21_physical_window_covariance_selected
