import HRS.MS.Fp81S21ErrorEnvelopePhysicalData
import HRS.MS.Fp81S21ErrorEnvelopePhysical
import HRS.MS.Fp81S21GaussianWickPackage
import HRS.MS.Fp81S21InitialConsumer6

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.S21E
attribute [local instance] fp81s21_initialMeasure_isProbability
variable {p : Parameters} {δ : ℝ} {R : Trajectory p δ}

abbrev fp81s21_Profile (α : ℕ → ℝ) : Prop :=
  (∀ N, 0 ≤ α N) ∧ Tendsto α atTop (𝓝 0)

abbrev fp81s21_Compatκ (Q : fp81s21_Physical35 p R)
    (O1 : fp81s21_O1_gaussian_wick p.d p.s p.a p.β p.γ p.T R.ρ) : Prop :=
  ∀ a : ℝ, 0 ≤ a → (fp81s21_O1_kappa O1 a : TensorDual (Window p) 3) =
    s21eKappa Q.src.G0.P (initialKappa R a)
      (fp81s21_physical35_D Q.tofp81s21_Gaussian35Selection Q.OD a)
      (r26t3_Zpath Q.src.G0 a)
      (fun ω => (fp81s21_physical35_J Q.tofp81s21_Gaussian35Selection Q.OJ a ω :
        TensorDual (Window p) 2))

abbrev fp81s21_Init (R : Trajectory p δ)
    (future : (H : ℝ) → ℝ → Measure (OscPath p.d (wholeSpaceIndex p.d) H))
    (α : ℕ → ℝ) : Prop :=
  ∀ N : ℕ, 2 ≤ N → ∀ (a : ℝ) (ha : 0 ≤ a) (Φ : Window p → ℝ),
    Φ ∈ CbUnitBall (Window p) 5 → ∀ G : GaussianRealization R,
      |initialRemainder R future N G a ha Φ| ≤ α N

abbrev fp81s21_Dec (R : Trajectory p δ)
    (O1 : fp81s21_O1_gaussian_wick p.d p.s p.a p.β p.γ p.T R.ρ)
    (α : ℕ → ℝ) (C c : ℝ) : Prop :=
  ∀ L : ℝ, 0 < L → ∃ eL : ℕ → ℝ, fp81s21_Profile eL ∧
    ∀ N : ℕ, 2 ≤ N → fp81s21_errorEnvelope p R (fp81s21_O1_kappa O1) N ≤
      α N + eL N + C * Real.exp (-c * L)

/-- Select O1 from the supplied physical package, preserving its cubic tensor. -/
theorem fp81s21_errorEnvelope_select_O1 (Q : fp81s21_Physical35 p R)
    (K : ℝ) (hresp : fp81s21_Response9 R K) (hwick : fp81s21_WickAll Q)
    (hbound : ∀ a : ℝ, 0 ≤ a →
      ‖initialKappa R a‖ + 3 * fp81s21_ID Q a + 3 * fp81s21_IJ Q a ≤
        K ^ 3 + 3 * (Q.MD ^ (1 / 3 : ℝ) * Q.MZ ^ (1 / 2 : ℝ) +
          Q.MJ ^ (1 / 2 : ℝ) * Q.MZ ^ (1 / 4 : ℝ))) :
    ∃ O1 : fp81s21_O1_gaussian_wick p.d p.s p.a p.β p.γ p.T R.ρ,
      fp81s21_Compatκ Q O1 := by
  refine ⟨fp81s21_gaussianO1_of_physical35 Q K hresp hwick hbound, ?_⟩
  exact fp81s21_gaussianO1_kappa_eq Q K hresp hwick hbound

#print axioms fp81s21_errorEnvelope_select_O1
end HRS.Fp81.S21
end
