import HRS.MS.Fp81S21RemotePhysicalG2

/-! Packet 38G revision: supplied prediction kernels, with arbitrary realization.
The real-time function is the exact argument consumed by both derivative kernels;
continuous predictions on the full horizon enter through the clipping adapter. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Filter Topology
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.R2Interp HRS.MS.S111K2

local instance fp81s21_remoteG3_complete (p : Parameters) :
    CompleteSpace (projTensor (Window p) 2) :=
  HRS.Fp81.V01.fp81v01_projTensorComplete (Window p) 2
local instance fp81s21_remoteG3_meas (H : ℝ) :
    MeasurableSpace (Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) H))) := borel _
local instance fp81s21_remoteG3_borel (H : ℝ) :
    BorelSpace (Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) H))) := ⟨rfl⟩

/-- The supplied-prediction RS type: two derivative kernels at `Y` and the
literal cumulatives of the supplied histories and retained operators. -/
abbrev fp81s21_remote_G_RS_at {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (Q : fp81s21_Physical35 p R)
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (G : GaussianRealization R) (a : ℝ) (ha : 0 ≤ a)
    (UG UB : G.Ω → Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) (a + p.T))))
    (Φ : Window p → ℝ) (Y : G.Ω → ℝ → Window p) :=
  fp81s21_WindowRS G.P (a + p.T)
    (fun ω t => fderiv ℝ (initialHeat future a ha Φ t)
      (Y ω t))
    (fun ω t => fp81s21_gaussian_Dcum (Q.OD a ha) (add_nonneg ha p.hT.le) UB t ω)
    (fun ω t => fp81s21_covariance_pairingCLM
      (iteratedFDeriv ℝ 2 (initialHeat future a ha Φ t)
        (Y ω t)))
    (fun ω t => fp81s21_gaussian_Jcum (Q.OJ a ha) (add_nonneg ha p.hT.le) UG t ω)

/-- Extend the supplied continuous prediction by clipping the cutoff to its domain.
For `G = Q.src.G0`, this accepts exactly the prediction supplied by packet 36A. -/
def fp81s21_remote_G_extend {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (G : GaussianRealization R) (a : ℝ) (ha : 0 ≤ a)
    (Y : G.Ω → C(Icc (0 : ℝ) (a + p.T), Window p)) : G.Ω → ℝ → Window p :=
  fun ω t => Y ω (projIcc 0 (a + p.T) (add_nonneg ha p.hT.le) t)

/-- On the full RS interval the extension evaluates the supplied path literally. -/
theorem fp81s21_remote_G_extend_at {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (G : GaussianRealization R) (a : ℝ) (ha : 0 ≤ a)
    (Y : G.Ω → C(Icc (0 : ℝ) (a + p.T), Window p))
    (ω : G.Ω) (t : Icc (0 : ℝ) (a + p.T)) :
    fp81s21_remote_G_extend G a ha Y ω t = Y ω t := by
  simp only [fp81s21_remote_G_extend, projIcc_of_mem _ t.property]

/-- The old raw-prediction certificate is definitionally a specialization.
This asserts no continuity or indistinguishability of that raw prediction. -/
theorem fp81s21_remote_G_RS_eq_at {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (Q : fp81s21_Physical35 p R)
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (G : GaussianRealization R) (a : ℝ) (ha : 0 ≤ a)
    (UG UB : G.Ω → Lp r26t6_Coeff 2 (volume.restrict (Icc (0 : ℝ) (a + p.T))))
    (Φ : Window p → ℝ) :
    fp81s21_remote_G_RS Q future G a ha UG UB Φ =
      fp81s21_remote_G_RS_at Q future G a ha UG UB Φ
        (fp81s21_remote_G_prediction Q G a ha) := rfl

#print axioms fp81s21_remote_G_RS_at
#print axioms fp81s21_remote_G_extend
#print axioms fp81s21_remote_G_extend_at
#print axioms fp81s21_remote_G_RS_eq_at
end HRS.Fp81.S21
end
