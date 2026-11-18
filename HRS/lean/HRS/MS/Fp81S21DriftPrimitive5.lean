import HRS.MS.Fp81S21DriftPrimitive4

/-! Integrability of the triangular source bracket. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
namespace HRS.Fp81.S21

/-- An integrable square supplies an integrable triangular row integral. -/
theorem fp81s21_triangular_bracket_integrable {b T : ℝ} (hbT : b ≤ T)
    (Q : ℝ → ℝ) (K : ℝ × ℝ → ℝ)
    (hQ : IntegrableOn Q (Icc b T))
    (hK : Integrable K ((volume.restrict (Icc b T)).prod
      (volume.restrict (Icc b T)))) :
    IntegrableOn (fun s => Q s + ∫ v in b..s, K (v, s)) (Icc b T) := by
  let ν : Measure ℝ := volume.restrict (Icc b T)
  let S : Set (ℝ × ℝ) := {z | b < z.2 ∧ z.2 ≤ z.1}
  have hS : MeasurableSet S :=
    (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_le measurable_snd measurable_fst)
  let F : ℝ × ℝ → ℝ := fun z => K (z.2, z.1)
  let G : ℝ × ℝ → ℝ := S.indicator F
  have hG : Integrable G (ν.prod ν) := by
    exact hK.swap.indicator hS
  have hRow : Integrable (fun s => ∫ v, G (s, v) ∂ν) ν := hG.integral_prod_left
  have hEq : (fun s => ∫ v, G (s, v) ∂ν) =ᵐ[ν]
      (fun s => ∫ v in b..s, K (v, s)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    have hset : Ioc b s ⊆ Icc b T := by
      intro v hv
      exact ⟨hv.1.le, hv.2.trans hs.2⟩
    rw [intervalIntegral.integral_of_le hs.1]
    calc
      (∫ v, G (s, v) ∂ν) = ∫ v, (Ioc b s).indicator (fun v => K (v, s)) v ∂ν := by
        apply integral_congr_ae
        filter_upwards with v
        by_cases hv : v ∈ Ioc b s
        · have hm : (s, v) ∈ S := hv
          rw [show G (s, v) = K (v, s) from indicator_of_mem hm F, indicator_of_mem hv]
        · have hm : (s, v) ∉ S := hv
          rw [show G (s, v) = 0 from indicator_of_notMem hm F, indicator_of_notMem hv]
      _ = ∫ v in Ioc b s, K (v, s) ∂ν := integral_indicator measurableSet_Ioc
      _ = ∫ v in Ioc b s, K (v, s) ∂volume := by
        simp [ν, Measure.restrict_restrict_of_subset hset]
  exact hQ.add (hRow.congr hEq)

#print axioms fp81s21_triangular_bracket_integrable
end HRS.Fp81.S21
end
