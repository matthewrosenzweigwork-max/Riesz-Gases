import HRS.MS.Fp81S21SourceInt

/-! Product integrability for the staged Sup48--49 zero extensions. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2WinErr HRS.MS.R2WinOrbNL

/-- The jointly measurable zero extensions from Sup49 and Sup48 are product
integrable under uniform scalar sixth-moment bounds for their physical slices.
The output also records the common full-measure event of time-section
integrability. -/
theorem fp81s21_sup48_49_source_integrable
    (p : Parameters) {δ T : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (hT : 0 < T)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N)
    (φ : Euc p.d → ℝ)
    (horb : S104nOrbit (r26t3_coeff R) φ T)
    (hkernel : Measurable (fun z : Euc p.d × Euc p.d =>
      commutatorKernel p.d p.s (gradient φ) z.1 z.2))
    (Mq Mk : ℝ) (hMq : 0 ≤ Mq) (hMk : 0 ≤ Mk)
    (hQslice : ∀ v ∈ Icc (0 : ℝ) T, SixthBound A.P
      (fun ω => r2QuadField p.s (r26t3_mu R v) A.P A.X v ω φ) Mq)
    (hKslice : ∀ v s : ℝ, 0 ≤ v → v ≤ s → s ≤ T → SixthBound A.P
      (fun ω => r2QuadField p.s (r26t3_mu R v) A.P A.X v ω
        (propagatorW (r26t3_coeff R) v s
          (generatorW (r26t3_coeff R) s φ))) Mk)
    {b : ℝ} (hbT : b ≤ T) :
    ∃ Q : ℝ × A.Ω → ℝ, ∃ K : (ℝ × ℝ) × A.Ω → ℝ,
      Measurable Q ∧ Measurable K ∧
      (∀ᵐ ω ∂A.P, ∀ v ∈ Icc (0 : ℝ) T,
        Q (v, ω) = r2QuadField p.s (r26t3_mu R v) A.P A.X v ω φ) ∧
      (∀ᵐ ω ∂A.P, ∀ v s : ℝ, 0 ≤ v → v ≤ s → s ≤ T →
        K ((v, s), ω) = r2QuadField p.s (r26t3_mu R v) A.P A.X v ω
          (propagatorW (r26t3_coeff R) v s
            (generatorW (r26t3_coeff R) s φ))) ∧
      (∀ z, z.1 ∉ Icc (0 : ℝ) T → Q z = 0) ∧
      (∀ z, ¬ (0 ≤ z.1.1 ∧ z.1.1 ≤ z.1.2 ∧ z.1.2 ≤ T) → K z = 0) ∧
      Integrable Q ((volume.restrict (Icc b T)).prod A.P) ∧
      Integrable K (((volume.restrict (Icc b T)).prod
        (volume.restrict (Icc b T))).prod A.P) ∧
      ∀ᵐ ω ∂A.P,
        Integrable (fun v => Q (v, ω)) (volume.restrict (Icc b T)) ∧
        Integrable (fun z : ℝ × ℝ => K (z, ω))
          ((volume.restrict (Icc b T)).prod (volume.restrict (Icc b T))) := by
  let ν : Measure ℝ := volume.restrict (Icc b T)
  haveI : IsFiniteMeasure ν := by
    dsimp [ν]
    infer_instance
  obtain ⟨K, hK, hKe, hKzero⟩ :=
    fp81s21_terminal_quad_zero_extension p R hδ hδh hT A φ horb
  obtain ⟨Q, hQ, hQe, hQzero⟩ :=
    fp81s21_baseline_quad_zero_extension p R hδ hδh hT A φ hkernel
  have hQsix : ∀ v, SixthBound A.P (fun ω => Q (v, ω)) Mq := by
    intro v
    by_cases hv : v ∈ Icc (0 : ℝ) T
    · have hEq : (fun ω => Q (v, ω)) =ᵐ[A.P]
          (fun ω => r2QuadField p.s (r26t3_mu R v) A.P A.X v ω φ) := by
        filter_upwards [hQe] with ω hω
        exact hω v hv
      have hEq6 : (fun ω => ‖Q (v, ω)‖ ^ 6) =ᵐ[A.P]
          (fun ω => ‖r2QuadField p.s (r26t3_mu R v) A.P A.X v ω φ‖ ^ 6) := by
        filter_upwards [hEq] with ω hω
        change ‖Q (v, ω)‖ ^ 6 =
          ‖r2QuadField p.s (r26t3_mu R v) A.P A.X v ω φ‖ ^ 6
        rw [hω]
      refine ⟨(hQslice v hv).1.congr hEq6.symm, ?_⟩
      calc
        (∫ ω, ‖Q (v, ω)‖ ^ 6 ∂A.P) =
            ∫ ω, ‖r2QuadField p.s (r26t3_mu R v) A.P A.X v ω φ‖ ^ 6 ∂A.P :=
          integral_congr_ae hEq6
        _ ≤ Mq := (hQslice v hv).2
    · have hEq : (fun ω => Q (v, ω)) = fun _ => (0 : ℝ) := by
        funext ω
        exact hQzero (v, ω) hv
      rw [hEq]
      constructor
      · simpa using (integrable_const (0 : ℝ) : Integrable (fun _ : A.Ω => (0 : ℝ)) A.P)
      · simpa using hMq
  have hKsix : ∀ z : ℝ × ℝ, SixthBound A.P (fun ω => K (z, ω)) Mk := by
    intro z
    by_cases hz : 0 ≤ z.1 ∧ z.1 ≤ z.2 ∧ z.2 ≤ T
    · obtain ⟨hv, hvs, hs⟩ := hz
      have hEq : (fun ω => K (z, ω)) =ᵐ[A.P]
          (fun ω => r2QuadField p.s (r26t3_mu R z.1) A.P A.X z.1 ω
            (propagatorW (r26t3_coeff R) z.1 z.2
              (generatorW (r26t3_coeff R) z.2 φ))) := by
        filter_upwards [hKe] with ω hω
        exact hω z.1 z.2 hv hvs hs
      have hEq6 : (fun ω => ‖K (z, ω)‖ ^ 6) =ᵐ[A.P]
          (fun ω => ‖r2QuadField p.s (r26t3_mu R z.1) A.P A.X z.1 ω
            (propagatorW (r26t3_coeff R) z.1 z.2
              (generatorW (r26t3_coeff R) z.2 φ))‖ ^ 6) := by
        filter_upwards [hEq] with ω hω
        change ‖K (z, ω)‖ ^ 6 =
          ‖r2QuadField p.s (r26t3_mu R z.1) A.P A.X z.1 ω
            (propagatorW (r26t3_coeff R) z.1 z.2
              (generatorW (r26t3_coeff R) z.2 φ))‖ ^ 6
        rw [hω]
      refine ⟨(hKslice z.1 z.2 hv hvs hs).1.congr hEq6.symm, ?_⟩
      calc
        (∫ ω, ‖K (z, ω)‖ ^ 6 ∂A.P) =
            ∫ ω, ‖r2QuadField p.s (r26t3_mu R z.1) A.P A.X z.1 ω
              (propagatorW (r26t3_coeff R) z.1 z.2
                (generatorW (r26t3_coeff R) z.2 φ))‖ ^ 6 ∂A.P :=
          integral_congr_ae hEq6
        _ ≤ Mk := (hKslice z.1 z.2 hv hvs hs).2
    · have hEq : (fun ω => K (z, ω)) = fun _ => (0 : ℝ) := by
        funext ω
        exact hKzero (z, ω) hz
      rw [hEq]
      constructor
      · simpa using (integrable_const (0 : ℝ) : Integrable (fun _ : A.Ω => (0 : ℝ)) A.P)
      · simpa using hMk
  let q : ℝ → A.Ω → ℝ := fun v ω => Q (v, ω)
  let k : ℝ × ℝ → A.Ω → ℝ := fun z ω => K (z, ω)
  have hProd := fp81s21_joint_source_sixth_integrable A.P ν q k
    (by change Measurable Q; exact hQ)
    (by change Measurable K; exact hK)
    Mq Mk hMq hMk hQsix hKsix
  refine ⟨Q, K, hQ, hK, hQe, hKe, hQzero, hKzero, ?_, ?_, ?_⟩
  · change Integrable (Function.uncurry q) (ν.prod A.P)
    exact hProd.1
  · change Integrable (Function.uncurry k) ((ν.prod ν).prod A.P)
    exact hProd.2.1
  · simpa [q, k, ν] using hProd.2.2

#print axioms fp81s21_sup48_49_source_integrable
end HRS.Fp81.S21
end
