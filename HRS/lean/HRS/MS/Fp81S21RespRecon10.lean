import HRS.MS.Fp81S21RespRecon9
import HRS.MS.S111X2Aux13

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.S111X2

/-- A bounded continuous time weight yields a Bochner-integrable L² curve
for the shifted oscillator orbit. -/
theorem fp81s21_respRecon_orbit_L2_integrable (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∀ a : ℝ, 0 ≤ a → ∀ α : MultiIndex p.d,
          ∀ w : ℝ → ℝ, ContinuousOn w (Icc (0 : ℝ) p.T) →
            ∀ C : ℝ, 0 ≤ C → (∀ t ∈ Icc (0 : ℝ) p.T, |w t| ≤ C) →
              IntegrableOn (fun t => s111x2_toLp (r26t3_mu R 0)
                (fun x => w t * r26t3_U R 0 (a + t)
                  (oscTestFun (wholeSpaceIndex p.d : ℝ) α) x))
                (Icc (0 : ℝ) p.T) := by
  obtain ⟨δ0, hδ0, hhalf, horbit⟩ := fp81s21_respRecon_orbit_bounds p
  refine ⟨δ0, hδ0, hhalf, fun δ hδ hδle R a ha α w hw C hC hbound => ?_⟩
  obtain ⟨-, -, -, href⟩ := r26t3_reference_data p δ hδ (hδle.trans hhalf) R
  obtain ⟨M, c, S, hc, hTc⟩ := href 0
  haveI : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hTc.prob
  obtain ⟨B, hB, hreg, hcont⟩ := horbit δ hδ hδle R a ha α
  let f : ℝ → Euc p.d → ℝ := fun t x => w t * r26t3_U R 0 (a + t)
    (oscTestFun (wholeSpaceIndex p.d : ℝ) α) x
  have hf : ∀ t ∈ Icc (0 : ℝ) p.T, MemLp (f t) 2 (r26t3_mu R 0) := by
    intro t ht
    have h := HRS.MS.Tc5.tc5_memLp_of_cb (ν := r26t3_mu R 0) (hreg t ht).1
    exact h.const_mul (w t)
  have hfc : ∀ x, ContinuousOn (fun t => f t x) (Icc (0 : ℝ) p.T) :=
    fun x => hw.mul (hcont x)
  have hfb : ∀ t ∈ Icc (0 : ℝ) p.T, ∀ x, |f t x| ≤ C * B := by
    intro t ht x
    simp only [f, abs_mul]
    exact mul_le_mul (hbound t ht) ((hreg t ht).2 x) (abs_nonneg _) hC
  have hcontinuity : ContinuousOn (fun t => s111x2_toLp (r26t3_mu R 0) (f t))
      (Icc (0 : ℝ) p.T) := by
    intro t ht
    exact s111x2_lp_continuousWithinAt (G := fun _ => C * B) ht hf hfc hfb (memLp_const _)
  exact hcontinuity.integrableOn_Icc

#print axioms fp81s21_respRecon_orbit_L2_integrable

end HRS.Fp81.S21
end
