import HRS.MS.Fp81S21SourceInt4

/-! Transfer the Sup43 frozen-source identity to the measurable zero extensions. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2WinErr

/-- Sup43's elapsed-time FTC, transferred through the Sup48--49 agreements,
gives the frozen-source identity with the actual shifted interval integral. -/
theorem fp81s21_window_mode_source_ftc_from_extensions (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N, ∀ T : ℝ, 0 < T →
      ∀ α : MultiIndex p.d,
      ∀ Q : ℝ × A.Ω → ℝ, ∀ K : (ℝ × ℝ) × A.Ω → ℝ,
      (∀ᵐ ω ∂A.P, ∀ v ∈ Icc (0 : ℝ) T,
        Q (v, ω) = r2QuadField p.s (r26t3_mu R v) A.P A.X v ω
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) →
      (∀ᵐ ω ∂A.P, ∀ v s : ℝ, 0 ≤ v → v ≤ s → s ≤ T →
        K ((v, s), ω) = r2QuadField p.s (r26t3_mu R v) A.P A.X v ω
          (propagatorW (r26t3_coeff R) v s
            (generatorW (r26t3_coeff R) s
              (oscTestFun (wholeSpaceIndex p.d : ℝ) α)))) →
      ∀ᵐ ω ∂A.P, ∀ v ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc v T,
        fp81s21_window_mode_source_field p R A α v t ω =
          Q (v, ω) + ∫ s in v..t, K ((v, s), ω) := by
  obtain ⟨δ0, hδ0, hδ0h, hRawFTC⟩ := fp81s21_window_mode_quad_frozen_ftc p
  refine ⟨δ0, hδ0, hδ0h, ?_⟩
  intro δ hδ hδle R N hN A T hT α Q K hQe hKe
  filter_upwards [hQe, hKe] with ω hQω hKω
  intro v hv t ht
  rcases hv with ⟨hv0, hvT⟩
  rcases ht with ⟨hvt, htT⟩
  let φ : Euc p.d → ℝ := oscTestFun (wholeSpaceIndex p.d : ℝ) α
  let τ : ℝ := t - v
  have hτ : τ ∈ Icc (0 : ℝ) (T - v) := by
    constructor <;> dsimp [τ] <;> linarith
  have hraw := hRawFTC δ hδ hδle R N hN A T v hv0 hvT α τ hτ ω
  have hraw' : fp81s21_window_mode_source_field p R A α v t ω =
      r2QuadField p.s (r26t3_mu R v) A.P A.X v ω φ +
        ∫ u in (0 : ℝ)..τ, r2QuadField p.s (r26t3_mu R v) A.P A.X v ω
          (propagatorW (r26t3_coeff R) v (v + u)
            (generatorW (r26t3_coeff R) (v + u) φ)) := by
    simpa only [fp81s21_window_mode_source_field, φ, τ, add_sub_cancel] using hraw
  have hKshift : (∫ u in (0 : ℝ)..τ, K ((v, v + u), ω)) =
      ∫ s in v..t, K ((v, s), ω) := by
    have h := intervalIntegral.integral_comp_add_left
      (f := fun s => K ((v, s), ω)) (a := (0 : ℝ)) (b := τ) v
    simpa [τ, add_sub_cancel] using h
  have hKreplace : (∫ u in (0 : ℝ)..τ, K ((v, v + u), ω)) =
      ∫ u in (0 : ℝ)..τ, r2QuadField p.s (r26t3_mu R v) A.P A.X v ω
        (propagatorW (r26t3_coeff R) v (v + u)
          (generatorW (r26t3_coeff R) (v + u) φ)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hu' : u ∈ Icc (0 : ℝ) τ := by
      simpa [uIcc_of_le hτ.1] using hu
    exact hKω v (v + u) hv0 (by linarith [hu'.1]) (by linarith [hu'.2, htT])
  have hQeq := hQω v ⟨hv0, hvT⟩
  calc
    fp81s21_window_mode_source_field p R A α v t ω =
        r2QuadField p.s (r26t3_mu R v) A.P A.X v ω φ +
          ∫ u in (0 : ℝ)..τ, r2QuadField p.s (r26t3_mu R v) A.P A.X v ω
            (propagatorW (r26t3_coeff R) v (v + u)
              (generatorW (r26t3_coeff R) (v + u) φ)) := hraw'
    _ = Q (v, ω) + ∫ u in (0 : ℝ)..τ, K ((v, v + u), ω) := by rw [← hQeq, ← hKreplace]
    _ = Q (v, ω) + ∫ s in v..t, K ((v, s), ω) := by rw [hKshift]

#print axioms fp81s21_window_mode_source_ftc_from_extensions
end HRS.Fp81.S21
end
