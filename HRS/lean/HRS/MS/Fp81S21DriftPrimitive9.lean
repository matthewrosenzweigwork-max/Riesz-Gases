import HRS.MS.Fp81S21DriftPrimitive8

/-! Construction of all source inputs for the physical drift primitive. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2WinErr HRS.MS.R2WinOrbNL

/-- Uniform sixth-slice bounds supply the extensions and hence the physical
source certificate, primitive identity, continuity and fixed-time measurability. -/
theorem fp81s21_window_mode_drift_constructed (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∃ C L : ℝ, 0 ≤ C ∧ 0 ≤ L ∧
      ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N, ∀ T : ℝ, 0 < T →
      ∀ α : MultiIndex p.d, ∀ b : ℝ, 0 ≤ b → b ≤ T →
      (∀ v ∈ Icc (0 : ℝ) T, SixthBound A.P
        (fun ω => r2QuadField p.s (r26t3_mu R v) A.P A.X v ω
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) (C * (L * s104_b p.d α) ^ 6)) ∧
      (∀ v s : ℝ, 0 ≤ v → v ≤ s → s ≤ T → SixthBound A.P
        (fun ω => r2QuadField p.s (r26t3_mu R v) A.P A.X v ω
          (propagatorW (r26t3_coeff R) v s (generatorW (r26t3_coeff R) s
            (oscTestFun (wholeSpaceIndex p.d : ℝ) α)))) (C * (L * s104_b p.d α) ^ 6)) ∧
      ∃ Q : ℝ × A.Ω → ℝ, ∃ K : (ℝ × ℝ) × A.Ω → ℝ,
      Measurable Q ∧ Measurable K ∧
      (∀ᵐ ω ∂A.P, ∀ v ∈ Icc (0 : ℝ) T,
        Q (v, ω) = r2QuadField p.s (r26t3_mu R v) A.P A.X v ω
          (oscTestFun (wholeSpaceIndex p.d : ℝ) α)) ∧
      (∀ᵐ ω ∂A.P, ∀ v s : ℝ, 0 ≤ v → v ≤ s → s ≤ T →
        K ((v, s), ω) = r2QuadField p.s (r26t3_mu R v) A.P A.X v ω
          (propagatorW (r26t3_coeff R) v s (generatorW (r26t3_coeff R) s
            (oscTestFun (wholeSpaceIndex p.d : ℝ) α)))) ∧
      Integrable Q ((volume.restrict (Icc (0 : ℝ) T)).prod A.P) ∧
      Integrable K (((volume.restrict (Icc (0 : ℝ) T)).prod
        (volume.restrict (Icc (0 : ℝ) T))).prod A.P) ∧
      (∀ᵐ ω ∂A.P, ∀ a t : ℝ, 0 ≤ a → a ≤ t → t ≤ T →
        IntervalIntegrable (fun v => fp81s21_window_mode_source_field p R A α v t ω)
          volume a t) ∧
      (∀ᵐ ω ∂A.P, (∀ t ∈ Icc b T,
        IntervalIntegrable (fun v => fp81s21_window_mode_source_field p R A α v t ω)
          volume b t ∧
        (∫ v in b..t, fp81s21_window_mode_source_field p R A α v t ω) =
          ∫ s in b..t, Q (s, ω) + ∫ v in b..s, K ((v, s), ω)) ∧
        ContinuousOn (fun t => ∫ v in b..t,
          fp81s21_window_mode_source_field p R A α v t ω) (Icc b T)) ∧
      ∀ t ∈ Icc b T, AEMeasurable (fun ω => ∫ v in b..t,
        fp81s21_window_mode_source_field p R A α v t ω) A.P := by
  obtain ⟨δa, hδa, hδah, hSlice⟩ := fp81s21_source_sixth_slices p
  obtain ⟨δb, hδb, hδbh, hPrim⟩ := fp81s21_window_mode_drift_primitive p
  obtain ⟨δc, hδc, hδch, hKernel⟩ := fp81s21_window_terminal_kernel_envelopes p
  obtain ⟨δd, Co, co, hδd, hδdh, hco, hCommon⟩ := fp81s21_common_radius p
  obtain ⟨δe, hδe, hδeh, hFTC⟩ := fp81s21_window_mode_source_ftc_from_extensions p
  let δ0 := min δa (min δb (min δc (min δd δe)))
  have hδ0 : 0 < δ0 := lt_min hδa (lt_min hδb (lt_min hδc (lt_min hδd hδe)))
  have hδ0h : δ0 ≤ 1 / 2 := (min_le_left _ _).trans hδah
  refine ⟨δ0, hδ0, hδ0h, ?_⟩
  intro δ hδ hδle R
  have ha : δ ≤ δa := hδle.trans (min_le_left _ _)
  have hb' : δ ≤ δb := hδle.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hc : δ ≤ δc := hδle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hd : δ ≤ δd := hδle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have he : δ ≤ δe := hδle.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have hδhalf : δ ≤ 1 / 2 := hδle.trans hδ0h
  obtain ⟨C, L, hC, hL, hBounds⟩ := hSlice δ hδ ha R
  obtain ⟨B, hB, hEn⟩ := hKernel δ hδ hc R
  obtain ⟨_, _, hTerm, _⟩ := hCommon δ hδ hd R.ρβ R.thermal
  refine ⟨C, L, hC, hL, ?_⟩
  intro N hN A T hT α b hb hbT
  let φ : Euc p.d → ℝ := oscTestFun (wholeSpaceIndex p.d : ℝ) α
  let W : WholeCoeff p.d := r26t3_coeff R
  have horb : S104nOrbit W φ T :=
    s104b_orbit_of_termRegGen hTerm R.admissible R.resulting α T hT.le
  have hdiag : propagatorW W 0 0 φ = φ :=
    (HRS.MS.Fcau.propagatorW_isClassical (horb.ex0 0 ⟨le_rfl, hT.le⟩)).terminal
  have hkernel : Measurable (fun z : Euc p.d × Euc p.d =>
      commutatorKernel p.d p.s (gradient φ) z.1 z.2) := by
    have h := (hEn 0 0 le_rfl le_rfl α).1
    change IsBoundedPairKernel p.s _ (commutatorKernel p.d p.s
      (gradient (propagatorW W 0 0 φ))) at h
    rw [hdiag] at h
    exact h.measurable
  let M : ℝ := C * (L * s104_b p.d α) ^ 6
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hQslice : ∀ v ∈ Icc (0 : ℝ) T, SixthBound A.P
      (fun ω => r2QuadField p.s (r26t3_mu R v) A.P A.X v ω φ) M := by
    intro v hv
    exact (hBounds N hN A v v hv.1 le_rfl α).1
  have hKslice : ∀ v s : ℝ, 0 ≤ v → v ≤ s → s ≤ T → SixthBound A.P
      (fun ω => r2QuadField p.s (r26t3_mu R v) A.P A.X v ω
        (propagatorW W v s (generatorW W s φ))) M := by
    intro v s hv hvs hs
    exact (hBounds N hN A v s hv hvs α).2
  obtain ⟨Q, K, hQ, hK, hQe, hKe, _, _, hQprod, hKprod, _⟩ :=
    fp81s21_sup48_49_source_integrable p R hδ hδhalf hT hN A φ horb hkernel
      M M hM hM hQslice hKslice (b := 0) hT.le
  have hRaw := hFTC δ hδ he R N hN A T hT α Q K hQe hKe
  have hAll := fp81s21_window_mode_source_interval_integrable_repaired
    p R A α Q K hQ hK hQprod hKprod hRaw
  have hResult := hPrim δ hδ hb' R N hN A T hT α b hb hbT Q K
    hQ hK hQprod hKprod hQe hKe
  exact ⟨hQslice, hKslice, Q, K, hQ, hK, hQe, hKe, hQprod, hKprod, hAll, hResult⟩

#print axioms fp81s21_window_mode_drift_constructed
end HRS.Fp81.S21
end
