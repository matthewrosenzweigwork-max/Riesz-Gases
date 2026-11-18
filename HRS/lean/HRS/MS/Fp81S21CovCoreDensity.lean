import HRS.MS.Fp81S21Absorption

/-!
# HRS S2.1(iii), packet 7: moving covariance core density clauses

The resulting solution supplies the timewise density and strict positivity.  The
oscillator tests lie in each moving weighted `L²` space by the upper comparison
with the uniformly bounded thermal density.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3

/-- The first three clauses of `S21eCovCore`, with a common admissible radius
chosen before the trajectory. -/
theorem sol13_covcore_density (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 →
        ∀ R : Trajectory p δ, ∀ r : ℝ, 0 ≤ r →
          Measurable (R.ρ r) ∧ (∀ x, 0 < R.ρ r x) ∧
            ∀ ψ : Euc p.d → ℝ,
              IsOscTest (wholeSpaceIndex p.d : ℝ) ψ →
                MemLp ψ 2 (HRS.Whole.withDensityReal (R.ρ r)) := by
  obtain ⟨δ0, Q, C, c, hδ0, hδ0half, -, -, -, -, _⟩ :=
    sol13_uniform_adjoint_energy p
  obtain ⟨M, hM, hthermalBound⟩ := sol13_uniform_thermal_sup_bound p
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδδ0 R r hr
  have hδhalf : δ ≤ 1 / 2 := le_trans hδδ0 hδ0half
  obtain ⟨_, hC1, hdata, _⟩ := r26t3_reference_data p δ hδ hδhalf R
  have hρmeas : Measurable (R.ρ r) := (R.resulting.regular r hr).measurable
  have hρpos : ∀ x, 0 < R.ρ r x := (hdata r hr).2
  have hρnonneg : ∀ x, 0 ≤ R.ρ r x := fun x => (hρpos x).le
  have hρupper : ∀ x, R.ρ r x ≤ p.C₁ * M := by
    intro x
    calc
      R.ρ r x ≤ p.C₁ * R.ρβ x := (R.resulting.ratio r hr x).2
      _ ≤ p.C₁ * M := mul_le_mul_of_nonneg_left (hthermalBound δ R x) hC1.le
  refine ⟨hρmeas, hρpos, ?_⟩
  intro ψ hψ
  exact HRS.MS.S111X1.x1_osc_memLp hρmeas hρnonneg hρupper hψ

#print axioms sol13_covcore_density

end HRS.Fp81.S21
