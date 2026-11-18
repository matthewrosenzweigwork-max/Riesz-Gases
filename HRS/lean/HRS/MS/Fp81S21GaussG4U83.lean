import HRS.MS.Fp81S21CovCoreBound

/-!
# HRS S2.1(iii), G4 U83: trajectory density comparison

The resulting-solution ratio gives the moving-density bound against the fixed
thermal density.  The small-radius assumptions are retained to obtain the
strict positivity of the comparison constant from the trajectory contract.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3

/-- The fixed reference measure used in the G4 density comparisons. -/
abbrev fp81s21_g4_mu {p : Parameters} {δ : ℝ} (R : Trajectory p δ) :
    Measure (Euc p.d) :=
  HRS.Whole.withDensityReal R.ρβ

private theorem fp81s21_g4_withDensityReal_le_smul
    {d : ℕ} {ρ σ : Euc d → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hσ : Measurable σ) (hdom : ∀ x, ρ x ≤ K * σ x) :
    HRS.Whole.withDensityReal ρ ≤
      ENNReal.ofReal K • HRS.Whole.withDensityReal σ := by
  refine Measure.le_iff'.2 fun A => ?_
  unfold HRS.Whole.withDensityReal
  rw [withDensity_apply']
  rw [Measure.smul_apply, smul_eq_mul]
  rw [withDensity_apply']
  calc
    ∫⁻ x in A, ENNReal.ofReal (ρ x) ≤
        ∫⁻ x in A, ENNReal.ofReal K * ENNReal.ofReal (σ x) := by
      apply lintegral_mono
      intro x
      calc
        ENNReal.ofReal (ρ x) ≤ ENNReal.ofReal (K * σ x) :=
          ENNReal.ofReal_le_ofReal (hdom x)
        _ = ENNReal.ofReal K * ENNReal.ofReal (σ x) := ENNReal.ofReal_mul hK
    _ = ENNReal.ofReal K * ∫⁻ x in A, ENNReal.ofReal (σ x) := by
      rw [lintegral_const_mul]
      exact ENNReal.measurable_ofReal.comp hσ

theorem fp81s21_g4_density_comparison
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) :
    0 < p.C₁ ∧
      ∀ r : ℝ, 0 ≤ r →
        (∀ x, R.ρ r x ≤ p.C₁ * R.ρβ x) ∧
        r26t3_mu R r ≤ ENNReal.ofReal p.C₁ • fp81s21_g4_mu R := by
  obtain ⟨_, hC₁, _, _⟩ := r26t3_reference_data p δ hδ hδhalf R
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  have hρβeq : R.ρβ = HRS.Whole.thermalDensity p.d p.s p.a p.β :=
    HRS.MS.Mov0.mv0_rho_eq p.hd p.hs0 hsd p.ha p.hβ R.thermal
  obtain ⟨_, ψ', hψ'⟩ := HRS.MS.S21.s21_schwartz_thermal
    p.hd p.hs0 hsd p.ha p.hβ
  have hρβmeas : Measurable R.ρβ := by
    rw [hρβeq, ← hψ']
    exact ψ'.continuous.measurable
  refine ⟨hC₁, ?_⟩
  intro r hr
  refine ⟨?_, ?_⟩
  · intro x
    exact (R.resulting.ratio r hr x).2
  · have hmeasure :
        HRS.Whole.withDensityReal (R.ρ r) ≤
          ENNReal.ofReal p.C₁ • HRS.Whole.withDensityReal R.ρβ :=
      fp81s21_g4_withDensityReal_le_smul hC₁.le hρβmeas
        (fun x => (R.resulting.ratio r hr x).2)
    simpa [r26t3_mu, fp81s21_g4_mu] using hmeasure

#print axioms fp81s21_g4_density_comparison

end HRS.Fp81.S21
