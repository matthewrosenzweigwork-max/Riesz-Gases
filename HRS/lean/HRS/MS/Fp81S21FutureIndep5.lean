import HRS.MS.Fp81S21FutureIndep3
import HRS.MS.Fp81S21FutureIndep4

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole HRS.MS.R26T3 HRS.MS.ProClosureS111

/-- An isonormal source is additive almost surely for each fixed pair of features. -/
theorem fp81s21_source_add_ae {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : E → Ω → ℝ)
    (hWm : ∀ h, Measurable (W h)) (hW2 : ∀ h, MemLp (W h) 2 P)
    (hcomb : ∀ (n : ℕ) (c : Fin n → ℝ) (f : Fin n → E),
      P.map (fun ω => ∑ i, c i * W (f i) ω) =
        gaussianReal 0 (Real.toNNReal (‖∑ i, c i • f i‖ ^ 2)))
    (a b : E) : ∀ᵐ ω ∂P, W (a + b) ω = W a ω + W b ω := by
  let D : Ω → ℝ := fun ω => W (a + b) ω - W a ω - W b ω
  have hD2 : MemLp D 2 P := ((hW2 (a + b)).sub (hW2 a)).sub (hW2 b)
  have hDm : Measurable D := ((hWm (a + b)).sub (hWm a)).sub (hWm b)
  have hlaw := hcomb 3 ![1, -1, -1] ![a + b, a, b]
  have hlaw' : P.map D = gaussianReal 0 0 := by
    simpa [D, Fin.sum_univ_three, sub_eq_add_neg] using hlaw
  have hz : ∫ ω, D ω ^ 2 ∂P = 0 := by
    simpa using s21g2_s11a_second hDm.aemeasurable hlaw'
  have ha := (integral_eq_zero_iff_of_nonneg (fun ω => sq_nonneg (D ω))
    hD2.integrable_sq).1 hz
  filter_upwards [ha] with ω hω
  have hω' : D ω = 0 := sq_eq_zero_iff.mp hω
  dsimp [D] at hω'
  linarith

/-- Past and future noise features, inserted into the noise summand of the
retained initial/noise Hilbert space. -/
def fp81s21_pastNoiseSourceFeature (p : Parameters) {δ : ℝ}
    (R : Trajectory p δ) (r t : ℝ) (φ : Euc p.d → ℝ) :
    Fp81S21GaussFeatureHilbert p R :=
  WithLp.toLp 2 (0, movingNoiseFeature R 0 t φ - movingNoiseFeature R r t φ)

def fp81s21_futureNoiseSourceFeature (p : Parameters) {δ : ℝ}
    (R : Trajectory p δ) (r t : ℝ) (φ : Euc p.d → ℝ) :
    Fp81S21GaussFeatureHilbert p R :=
  WithLp.toLp 2 (0, movingNoiseFeature R r t φ)

/-- The source-level decomposition holds almost surely for each observation. -/
theorem fp81s21_noise_source_decomposition
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (J : Fp81S21GaussFeatureHilbert p R →ₗᵢ[ℝ] GaussianFeatureHilbert)
    (W : GaussianFeatureHilbert → Ω → ℝ)
    (hWm : ∀ h, Measurable (W h)) (hW2 : ∀ h, MemLp (W h) 2 P)
    (hcomb : ∀ (n : ℕ) (c : Fin n → ℝ) (f : Fin n → GaussianFeatureHilbert),
      P.map (fun ω => ∑ i, c i * W (f i) ω) =
        gaussianReal 0 (Real.toNNReal (‖∑ i, c i • f i‖ ^ 2)))
    (r t : ℝ) (φ : Euc p.d → ℝ) :
    ∀ᵐ ω ∂P,
      W (J (WithLp.toLp 2 (0, movingNoiseFeature R 0 t φ))) ω =
        W (J (fp81s21_pastNoiseSourceFeature p R r t φ)) ω +
        W (J (fp81s21_futureNoiseSourceFeature p R r t φ)) ω := by
  have hfeature : fp81s21_pastNoiseSourceFeature p R r t φ +
      fp81s21_futureNoiseSourceFeature p R r t φ =
        (WithLp.toLp 2 (0, movingNoiseFeature R 0 t φ) :
          Fp81S21GaussFeatureHilbert p R) := by
    apply WithLp.ofLp_injective
    simp [fp81s21_pastNoiseSourceFeature, fp81s21_futureNoiseSourceFeature]
  have h := fp81s21_source_add_ae P W hWm hW2 hcomb
    (J (fp81s21_pastNoiseSourceFeature p R r t φ))
    (J (fp81s21_futureNoiseSourceFeature p R r t φ))
  simpa only [← map_add, hfeature] using h

#print axioms fp81s21_source_add_ae
#print axioms fp81s21_noise_source_decomposition

end HRS.Fp81.S21
end
