import HRS.MS.Fp81S21RespRecon7

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3

/-- Continuous functions equal almost everywhere under the initial reference
measure agree everywhere, because its continuous density is positive. -/
theorem fp81s21_respRecon_ae_to_everywhere
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (f g : Euc p.d → ℝ)
    (hf : Continuous f) (hg : Continuous g)
    (hfg : f =ᵐ[r26t3_mu R 0] g) : f = g := by
  obtain ⟨-, -, hdensity, -⟩ := r26t3_reference_data p δ hδ hδh R
  have hρ := hdensity 0 le_rfl
  have hρmeas : Measurable (fun y : Euc p.d => ENNReal.ofReal (R.ρ 0 y)) :=
    ENNReal.measurable_ofReal.comp hρ.1.measurable
  have hvol : f =ᵐ[(volume : Measure (Euc p.d))] g := by
    have h := (ae_withDensity_iff hρmeas).1 hfg
    filter_upwards [h] with y hy
    exact hy (by simpa using hρ.2 y)
  exact (Continuous.ae_eq_iff_eq (volume : Measure (Euc p.d)) hf hg).1 hvol

#print axioms fp81s21_respRecon_ae_to_everywhere

end HRS.Fp81.S21
end
