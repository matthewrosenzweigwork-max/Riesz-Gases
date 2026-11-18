import HRS.MS.Fp81S21DriftPrimitive5

/-! Pathwise drift identity and continuity from triangular Fubini. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
namespace HRS.Fp81.S21

/-- Given a frozen-source identity and source integrability, the drift is the
primitive of an integrable bracket and is continuous on the window. -/
theorem fp81s21_drift_primitive_of_source_identity
    {b T : ℝ} (hbT : b ≤ T) (Q : ℝ → ℝ) (K : ℝ × ℝ → ℝ)
    (Z : ℝ → ℝ → ℝ)
    (hQ : IntegrableOn Q (Icc b T))
    (hK : Integrable K ((volume.restrict (Icc b T)).prod
      (volume.restrict (Icc b T))))
    (hZ : ∀ t ∈ Icc b T, IntervalIntegrable (fun v => Z v t) volume b t)
    (hFTC : ∀ v t, b ≤ v → v ≤ t → t ≤ T →
      Z v t = Q v + ∫ s in v..t, K (v, s)) :
    (∀ t ∈ Icc b T, (∫ v in b..t, Z v t) =
      ∫ s in b..t, Q s + ∫ v in b..s, K (v, s)) ∧
    ContinuousOn (fun t => ∫ v in b..t, Z v t) (Icc b T) := by
  have hBracket := fp81s21_triangular_bracket_integrable hbT Q K hQ hK
  have hKsq : IntegrableOn (fun z : ℝ × ℝ => K (z.2, z.1))
      (Icc b T ×ˢ Icc b T) (volume.prod volume) := by
    simpa only [IntegrableOn, ← Measure.prod_restrict, Function.comp_def, Prod.swap] using hK.swap
  have hIdentity : ∀ t ∈ Icc b T, (∫ v in b..t, Z v t) =
      ∫ s in b..t, Q s + ∫ v in b..s, K (v, s) := by
    intro t ht
    have hQi : IntervalIntegrable Q volume b t :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).2
        (hQ.mono_set (Icc_subset_Icc le_rfl ht.2))
    have hBi : IntervalIntegrable (fun s => Q s + ∫ v in b..s, K (v, s)) volume b t :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le ht.1).2
        (hBracket.mono_set (Icc_subset_Icc le_rfl ht.2))
    have hTi : IntervalIntegrable (fun s => ∫ v in b..s, K (v, s)) volume b t := by
      have h := hBi.sub hQi
      simpa using h
    have hSi : IntervalIntegrable (fun v => ∫ s in v..t, K (v, s)) volume b t := by
      apply (hZ t ht |>.sub hQi).congr
      intro v hv
      have hv' : v ∈ Ioc b t := by simpa [uIoc_of_le ht.1] using hv
      have he := hFTC v t hv'.1.le hv'.2 ht.2
      dsimp only
      linarith
    calc
      (∫ v in b..t, Z v t) = ∫ v in b..t, Q v + ∫ s in v..t, K (v, s) := by
        apply intervalIntegral.integral_congr
        intro v hv
        have hv' : v ∈ Icc b t := by simpa [uIcc_of_le ht.1] using hv
        exact hFTC v t hv'.1 hv'.2 ht.2
      _ = (∫ v in b..t, Q v) + ∫ v in b..t, ∫ s in v..t, K (v, s) :=
        intervalIntegral.integral_add hQi hSi
      _ = (∫ s in b..t, Q s) + ∫ s in b..t, ∫ v in b..s, K (v, s) := by
        rw [fp81s21_triangular_fubini ht.1 ht.2 hKsq]
      _ = ∫ s in b..t, Q s + ∫ v in b..s, K (v, s) :=
        (intervalIntegral.integral_add hQi hTi).symm
  refine ⟨hIdentity, ?_⟩
  have hc : ContinuousOn (fun t => ∫ s in b..t, Q s + ∫ v in b..s, K (v, s))
      (Icc b T) := by
    have hi : IntegrableOn (fun s => Q s + ∫ v in b..s, K (v, s))
        (uIcc b T) := by simpa [uIcc_of_le hbT] using hBracket
    simpa [uIcc_of_le hbT] using intervalIntegral.continuousOn_primitive_interval hi
  exact hc.congr (fun t ht => hIdentity t ht)

#print axioms fp81s21_drift_primitive_of_source_identity
end HRS.Fp81.S21
end
