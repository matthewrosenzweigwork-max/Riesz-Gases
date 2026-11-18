import HRS.MS.Fp81S21BlockValue13

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45 HRS.MS.CovMeas HRS.MS.GenPath

/-- The actual block value has the shifted window covariance evaluations. -/
theorem fp81s21_blockValue_isWindowJValue
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    (hlin : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ a + H →
      ∀ φ ψ : Euc d → ℝ, ∀ c : ℝ,
        IsR2DualCombo m φ → IsR2DualCombo m ψ →
        propagatorW C u t (φ + c • ψ) = propagatorW C u t φ + c • propagatorW C u t ψ)
    {I : Set ℝ} (hI : MeasurableSet I) (k : ℕ) :
    fp81s21_IsWindowJValue C m H a z (Icc (k : ℝ) ((k : ℝ) + 1) ∩ I)
      ((fp81s21_blockValue D I k : projTensor (OscPath d m H) 2) : TensorDual (OscPath d m H) 2) := by
  constructor
  · exact fp81s21_blockValue_mem D I k
  · intro ta tb φa φb l₁ l₂ hφa hφb hta htb h₁ h₂
    obtain ⟨Sa, ca, rfl⟩ := hφa
    obtain ⟨Sb, cb, rfl⟩ := hφb
    exact fp81s21_blockValue_eval_combo D hlin hI k hta htb Sa Sb ca cb l₁ l₂ h₁ h₂

#print axioms fp81s21_blockValue_isWindowJValue
end HRS.Fp81.S21
end
