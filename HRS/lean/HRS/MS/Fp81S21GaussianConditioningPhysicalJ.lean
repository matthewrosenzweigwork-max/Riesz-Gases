import HRS.MS.Fp81S21GaussianConditioningLimits3
import HRS.MS.Fp81S21GaussianIncrementApprox3
import HRS.MS.Fp81S21GaussianWindowRS2

/-! Packet 36J: condition the literal physical projective covariance increment.
The finite common-grid payload is produced from the retained histories; only
its covariance fields are consumed. No extra covariance factor is introduced.
The supplied decomposition is produced for the same GRS prediction in J2. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2Interp

/-- Both integrabilities and the per-cell identity, in RS-consumer order. -/
def fp81s21_J36Cell {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    (Q : fp81s21_Physical35 p R)
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (a : ℝ) (ha : 0 ≤ a) (Φ : Window p → ℝ)
    (Y : Q.src.G0.Ω → Window p) (u v : ℝ) : Prop :=
  let U := fun ω => (fp81s21_incrementJ36 Q a ha u v ω : TensorDual (Window p) 2)
    (iteratedFDeriv ℝ 2 Φ (r26t3_Zpath Q.src.G0 a ω))
  let V := fun ω => (fp81s21_incrementJ36 Q a ha u v ω : TensorDual (Window p) 2)
    (iteratedFDeriv ℝ 2 (initialHeat future a ha Φ v) (Y ω))
  Integrable V Q.src.G0.P ∧ Integrable U Q.src.G0.P ∧
    (∫ ω, V ω ∂Q.src.G0.P) = ∫ ω, U ω ∂Q.src.G0.P

/-- The common Hessian bound is one, before all evaluation points. -/
theorem fp81s21_J36_derivative_bounds
    {p : Parameters}
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d : ℝ) H))
    (hf : ∀ H v, IsProbabilityMeasure (future H v))
    (a : ℝ) (ha : 0 ≤ a) (Φ : Window p → ℝ) (hΦ : Φ ∈ CbUnitBall (Window p) 5) :
    (∀ z, ‖iteratedFDeriv ℝ 2 Φ z‖ ≤ 1) ∧
    (∀ v z, ‖iteratedFDeriv ℝ 2 (initialHeat future a ha Φ v) z‖ ≤ 1) := by
  have hm : MemCb 5 Φ := ⟨hΦ.1, hΦ.2.1⟩
  have hb (z : Window p) : ‖iteratedFDeriv ℝ 2 Φ z‖ ≤ 1 :=
    (HRS.MC.Sec7.S7PIL.S7PIL_le_cbNorm hm (by norm_num) z).trans hΦ.2.2
  exact ⟨hb, fun v z => ((fp81s21_windowFuture_heat_derivs future hf a ha Φ hm v).2 2
    (by norm_num) z).2.trans (ciSup_le hb)⟩

/-- Finite-to-L¹ conditioning of the actual retained covariance increment.
There is no assumed conditioning equality or approximation certificate. -/
theorem fp81s21_gaussian_conditioning_covariance_cell_of_decomposition
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
    fp81s21_J36Cell Q future a ha Φ Y u v := by
  letI : MeasurableSpace Q.src.G0.Ω := Q.src.G0.mΩ
  letI : IsProbabilityMeasure Q.src.G0.P := Q.src.G0.prob
  letI := fp81s21_windowFuture_isProbability future hf a ha v
  obtain ⟨I⟩ := fp81s21_gaussian_increment_approximations Q a ha u v hu huv hv
  have hb := fp81s21_J36_derivative_bounds future hf a ha Φ hΦ
  have he := fp81s21_conditioned_covariance_limit Q.src.G0.P
    (fp81s21_predictionPast Q.tofp81s21_Gaussian35Selection v)
    Y X (r26t3_Zpath Q.src.G0 a) hY hYpast hX hind hZ
    (windowFuture future a ha) v hlaw Φ ⟨hΦ.1, hΦ.2.1⟩ 1 zero_le_one
    hb.1 (fun ω => hb.2 v (Y ω)) (fp81s21_incrementJ36 Q a ha u v)
    I.integrableJ I.k I.h I.cJ I.hcJ I.hcpastJ I.hlimJ
  exact ⟨he.2.1, he.1, he.2.2.symm⟩

#print axioms fp81s21_J36_derivative_bounds
#print axioms fp81s21_gaussian_conditioning_covariance_cell_of_decomposition
end HRS.Fp81.S21
end
