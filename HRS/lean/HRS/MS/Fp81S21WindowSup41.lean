import HRS.MS.Fp81S21WindowSup40

/-! Physical frozen-source centered FTC from particle sixth slices. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.S53 HRS.MS.R2WinErr HRS.MS.R26T3

/-- For any orbit with the displayed weighted kernel envelopes, the physical
quadratic field satisfies the centered frozen-source FTC. -/
theorem fp81s21_particle_quad_frozen_ftc (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
      ∀ T v : ℝ, 0 ≤ v → v ≤ T → ∀ φ : Euc p.d → ℝ,
      S104nOrbit (r26t3_coeff R) φ T → ∀ B : ℝ, 0 ≤ B →
      (∀ τ ∈ Icc (0 : ℝ) (T - v), IsBoundedPairKernel p.s B
        (commutatorKernel p.d p.s (gradient
          (propagatorW (r26t3_coeff R) v (v + τ) φ)))) →
      (∀ τ ∈ Icc (0 : ℝ) (T - v), IsBoundedPairKernel p.s B
        (commutatorKernel p.d p.s (gradient
          (propagatorW (r26t3_coeff R) v (v + τ)
            (generatorW (r26t3_coeff R) (v + τ) φ))))) →
      ∀ τ ∈ Icc (0 : ℝ) (T - v), ∀ ω,
        r2QuadField p.s (r26t3_mu R v) A.P A.X v ω
          (propagatorW (r26t3_coeff R) v (v + τ) φ) =
        r2QuadField p.s (r26t3_mu R v) A.P A.X v ω
          (propagatorW (r26t3_coeff R) v v φ) +
        ∫ u in (0 : ℝ)..τ, r2QuadField p.s (r26t3_mu R v) A.P A.X v ω
          (propagatorW (r26t3_coeff R) v (v + u)
            (generatorW (r26t3_coeff R) (v + u) φ)) := by
  obtain ⟨δa, hδa, hδah, hSlices⟩ := fp81s21_particle_sixth_slices p
  obtain ⟨δb, hδb, hδbh, hDensity⟩ := fp81s21_uniform_density_moments p
  let δ0 := min δa δb
  have hδ0 : 0 < δ0 := lt_min hδa hδb
  have hδ0h : δ0 ≤ 1 / 2 := (min_le_left _ _).trans hδah
  refine ⟨δ0, hδ0, hδ0h, ?_⟩
  intro δ hδ hδle R N hN A T v hv hvT φ horb B hB hK0 hK1
  obtain ⟨C, hC, hSlice⟩ := hSlices δ hδ (hδle.trans (min_le_left _ _)) R
  obtain ⟨_, _, _, _, Mρ, _, _, _, _, _, _, hRound, _, _⟩ :=
    hDensity δ hδ (hδle.trans (min_le_right _ _)) R
  have hRef := hRound v hv
  obtain ⟨Mrow, hMrow, hrow⟩ := s53_rowConst (le_trans (by norm_num : 1 ≤ 2) p.hd) p.hs0
    (by linarith [p.hs] : p.s < (p.d : ℝ)) hRef.prob hRef.bdd
  have ctx : S53Ctx p.s (R.ρ v) Mrow := ⟨p.hs0, hMrow, hRef.prob, hrow⟩
  have hpos : 0 < N := by omega
  have hX : Measurable (A.X v.toNNReal) := (A.strong (v + 1)).adapted _
  let G0 : ℝ → Euc p.d → ℝ := fun u => propagatorW (r26t3_coeff R) v (v + u) φ
  let G1 : ℝ → Euc p.d → ℝ := fun u => propagatorW (r26t3_coeff R) v (v + u)
    (generatorW (r26t3_coeff R) (v + u) φ)
  have hRaw (G : ℝ → Euc p.d → ℝ)
      (hK : ∀ τ ∈ Icc (0 : ℝ) (T - v), IsBoundedPairKernel p.s B
        (commutatorKernel p.d p.s (gradient (G τ)))) :
      ∀ τ ∈ Icc (0 : ℝ) (T - v), SixthBound A.P
        (fun ω => fp81s21_frozen_raw_field p.s (R.ρ v) G (A.X v.toNNReal) (τ, ω))
        (C * B ^ 6) := by
    intro τ hτ
    have hSix := ((hSlice N hN A v hv B hB).1 _ (hK τ hτ)).1
    have heq : (fun ω => fp81s21_frozen_raw_field p.s (R.ρ v) G
        (A.X v.toNNReal) (τ, ω)) = fun ω => (N : ℝ) * pairEnergy
          (commutatorKernel p.d p.s (gradient (G τ))) (A.X v.toNNReal ω)
          (r26t3_mu R v) := by
      funext ω
      dsimp only [fp81s21_frozen_raw_field, r26t3_mu]
      rw [fp81s21_pairEnergy_eq_half_s53_Dk]
      ring
    rw [heq]
    exact hSix
  have hSix0 := hRaw G0 hK0
  have hSix1 := hRaw G1 hK1
  exact fp81s21_window_quad_frozen_ftc_of_sixth A.P horb ctx hpos hv hvT A.X hX
    (C * B ^ 6) (by positivity) hSix0 hSix1

#print axioms fp81s21_particle_quad_frozen_ftc
end HRS.Fp81.S21
end
