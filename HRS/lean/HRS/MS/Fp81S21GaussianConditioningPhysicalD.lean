import HRS.MS.Fp81S21GaussianConditioningLimits2
import HRS.MS.Fp81S21GaussianIncrementApprox3
import HRS.MS.Fp81S21GaussianWindowRS2

/-! Packet 36D: condition a literal physical drift increment. The supplied
past representative and future must decompose the retained Z window. The next
file produces these hypotheses for the same prediction stored in GRS. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp

/-- Both integrabilities and the per-cell identity, in RS-consumer order. -/
def fp81s21_D36Cell {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (Q : fp81s21_Physical35 p R)
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (a : ℝ) (ha : 0 ≤ a) (Φ : Window p → ℝ)
    (Y : Q.src.G0.Ω → Window p) (u v : ℝ) : Prop :=
  let U := fun ω => fderiv ℝ Φ (r26t3_Zpath Q.src.G0 a ω)
    (fp81s21_incrementD36 Q a ha u v ω)
  let V := fun ω => fderiv ℝ (initialHeat future a ha Φ v) (Y ω)
    (fp81s21_incrementD36 Q a ha u v ω)
  Integrable V Q.src.G0.P ∧ Integrable U Q.src.G0.P ∧
    (∫ ω, V ω ∂Q.src.G0.P) = ∫ ω, U ω ∂Q.src.G0.P

/-- The common derivative constant is one, before all evaluation points. -/
theorem fp81s21_D36_derivative_bounds
    {p : Parameters}
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (hf : ∀ H v, IsProbabilityMeasure (future H v))
    (a : ℝ) (ha : 0 ≤ a) (Φ : Window p → ℝ) (hΦ : Φ ∈ CbUnitBall (Window p) 5) :
    (∀ z, ‖fderiv ℝ Φ z‖ ≤ 1) ∧
    (∀ v z, ‖fderiv ℝ (initialHeat future a ha Φ v) z‖ ≤ 1) := by
  have hm : MemCb 5 Φ := ⟨hΦ.1, hΦ.2.1⟩
  have hb (z : Window p) : ‖iteratedFDeriv ℝ 1 Φ z‖ ≤ 1 :=
    (HRS.MC.Sec7.S7PIL.S7PIL_le_cbNorm hm (by norm_num) z).trans hΦ.2.2
  constructor
  · intro z
    rw [← norm_iteratedFDeriv_one]
    exact hb z
  · intro v z
    rw [← norm_iteratedFDeriv_one]
    exact ((fp81s21_windowFuture_heat_derivs future hf a ha Φ hm v).2 1
      (by norm_num) z).2.trans (ciSup_le hb)

/-- Apply the finite-to-L¹ wrapper to the actual retained increment; no
conditioning equality or approximation certificate is assumed. -/
theorem fp81s21_gaussian_conditioning_drift_cell_of_decomposition
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (Q : fp81s21_Physical35 p R)
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (hf : ∀ H v, IsProbabilityMeasure (future H v))
    (a : ℝ) (ha : 0 ≤ a) (Φ : Window p → ℝ) (hΦ : Φ ∈ CbUnitBall (Window p) 5)
    (u v : ℝ) (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ a + p.T)
    (Y X : Q.src.G0.Ω → Window p) (hY : Measurable Y)
    (hYpast : Measurable[fp81s21_incrementPast36 Q v] Y)
    (hX : Measurable X)
    (hind : IndepFun (fp81s21_predictionPast Q.tofp81s21_Gaussian35Selection v) X Q.src.G0.P)
    (hlaw : Q.src.G0.P.map X = windowFuture future a ha v)
    (hZ : r26t3_Zpath Q.src.G0 a =ᵐ[Q.src.G0.P] fun ω => Y ω + X ω) :
    fp81s21_D36Cell Q future a ha Φ Y u v := by
  letI : MeasurableSpace Q.src.G0.Ω := Q.src.G0.mΩ
  letI : IsProbabilityMeasure Q.src.G0.P := Q.src.G0.prob
  letI := fp81s21_windowFuture_isProbability future hf a ha v
  obtain ⟨k, h, c, hc, hcpast, hlim⟩ :=
    fp81s21_gaussian_drift_increment_approx Q a ha u v hu huv hv
  have hb := fp81s21_D36_derivative_bounds future hf a ha Φ hΦ
  have he := fp81s21_conditioned_drift_limit Q.src.G0.P
    (fp81s21_predictionPast Q.tofp81s21_Gaussian35Selection v)
    Y X (r26t3_Zpath Q.src.G0 a) hY hYpast hX hind hZ
    (windowFuture future a ha) v hlaw Φ ⟨hΦ.1, hΦ.2.1⟩ 1 zero_le_one
    hb.1 (fun ω => hb.2 v (Y ω)) (fp81s21_incrementD36 Q a ha u v)
    (fp81s21_gaussian_increments_integrable Q a ha u v).1 k h c hc hcpast hlim
  exact ⟨he.2.1, he.1, he.2.2.symm⟩

#print axioms fp81s21_D36_derivative_bounds
#print axioms fp81s21_gaussian_conditioning_drift_cell_of_decomposition
end HRS.Fp81.S21
end
