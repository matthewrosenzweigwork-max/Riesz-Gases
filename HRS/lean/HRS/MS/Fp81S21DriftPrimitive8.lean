import HRS.MS.Fp81S21DriftPrimitive7

/-! Physical window-mode drift and its measurable fixed-time version. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2WinErr

/-- The physical source inherits the primitive representation from the
Sup48--49 extensions, with fixed-time almost-everywhere measurability. -/
theorem fp81s21_window_mode_drift_primitive (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N, ∀ T : ℝ, 0 < T →
      ∀ α : MultiIndex p.d, ∀ b : ℝ, 0 ≤ b → b ≤ T →
      ∀ Q : ℝ × A.Ω → ℝ, ∀ K : (ℝ × ℝ) × A.Ω → ℝ,
      Measurable Q → Measurable K →
      Integrable Q ((volume.restrict (Icc (0 : ℝ) T)).prod A.P) →
      Integrable K (((volume.restrict (Icc (0 : ℝ) T)).prod
        (volume.restrict (Icc (0 : ℝ) T))).prod A.P) →
      (∀ᵐ ω ∂A.P, ∀ v ∈ Icc (0 : ℝ) T,
        Q (v, ω) = r2QuadField p.s (r26t3_mu R v) A.P A.X v ω
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) →
      (∀ᵐ ω ∂A.P, ∀ v s : ℝ, 0 ≤ v → v ≤ s → s ≤ T →
        K ((v, s), ω) = r2QuadField p.s (r26t3_mu R v) A.P A.X v ω
          (propagatorW (r26t3_coeff R) v s
            (generatorW (r26t3_coeff R) s
              (oscTestFun (wholeSpaceIndex p.d : ℝ) α)))) →
      (∀ᵐ ω ∂A.P, (∀ t ∈ Icc b T,
        IntervalIntegrable (fun v => fp81s21_window_mode_source_field p R A α v t ω)
          volume b t ∧
        (∫ v in b..t, fp81s21_window_mode_source_field p R A α v t ω) =
          ∫ s in b..t, Q (s, ω) + ∫ v in b..s, K ((v, s), ω)) ∧
        ContinuousOn (fun t => ∫ v in b..t,
          fp81s21_window_mode_source_field p R A α v t ω) (Icc b T)) ∧
      ∀ t ∈ Icc b T, AEMeasurable (fun ω => ∫ v in b..t,
        fp81s21_window_mode_source_field p R A α v t ω) A.P := by
  obtain ⟨δ0, hδ0, hδh, hFTC⟩ := fp81s21_window_mode_source_ftc_from_extensions p
  refine ⟨δ0, hδ0, hδh, ?_⟩
  intro δ hδ hδle R N hN A T hT α b hb hbT Q K hQ hK hQprod hKprod hQe hKe
  have hRaw := hFTC δ hδ hδle R N hN A T hT α Q K hQe hKe
  have hEvent := fp81s21_source_drift_primitive_ae hb hbT Q K
    (fp81s21_window_mode_source_field p R A α) A.P hQ hK hQprod hKprod hRaw
  refine ⟨hEvent, ?_⟩
  intro t ht
  have hm := fp81s21_measurable_source_primitive ht.1 Q K hQ hK
  apply hm.aemeasurable.congr
  filter_upwards [hEvent] with ω hω
  exact (hω.1 t ht).2.symm

#print axioms fp81s21_window_mode_drift_primitive
end HRS.Fp81.S21
end
