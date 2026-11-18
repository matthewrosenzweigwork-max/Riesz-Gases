import HRS.MS.Fp81S21WindowSup30

/-! Physical frozen-source FTC, with the exact Fubini inputs exposed. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.S53 HRS.MS.R2WinErr

/-- The centered physical quadratic field obeys the terminal-orbit FTC once
the displayed raw-field Fubini inputs have been verified. -/
theorem fp81s21_window_quad_frozen_ftc_of_integrability
    {d N : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {σ T v : ℝ} {ρ : Euc d → ℝ} {Mρ : ℝ} {C : WholeCoeff d}
    {φ : Euc d → ℝ} (horb : S104nOrbit C φ T)
    (ctx : S53Ctx σ ρ Mρ) (hN : 0 < N) (hv : 0 ≤ v) (hvT : v ≤ T)
    (X : ℝ≥0 → Ω → EucConfig d N)
    (hF : ∀ τ ∈ Icc (0 : ℝ) (T - v), Integrable (fun ω =>
      (N : ℝ) / 2 * s53_Dk σ ρ (propagatorW C v (v + τ) φ)
        (X v.toNNReal ω)) P)
    (hPath : ∀ τ ∈ Icc (0 : ℝ) (T - v), ∀ ω,
      IntervalIntegrable (fun u => (N : ℝ) / 2 * s53_Dk σ ρ
        (propagatorW C v (v + u) (generatorW C (v + u) φ))
        (X v.toNNReal ω)) volume 0 τ)
    (hMean : ∀ τ ∈ Icc (0 : ℝ) (T - v), IntervalIntegrable (fun u =>
      ∫ ω, (N : ℝ) / 2 * s53_Dk σ ρ
        (propagatorW C v (v + u) (generatorW C (v + u) φ))
        (X v.toNNReal ω) ∂P) volume 0 τ)
    (hProd : ∀ τ ∈ Icc (0 : ℝ) (T - v), Integrable
      (Function.uncurry fun ω u => (N : ℝ) / 2 * s53_Dk σ ρ
        (propagatorW C v (v + u) (generatorW C (v + u) φ))
        (X v.toNNReal ω)) (P.prod (volume.restrict (Ioc (0 : ℝ) τ)))) :
    ∀ τ ∈ Icc (0 : ℝ) (T - v), ∀ ω,
      r2QuadField σ (HRS.Whole.withDensityReal ρ) P X v ω
        (propagatorW C v (v + τ) φ) =
      r2QuadField σ (HRS.Whole.withDensityReal ρ) P X v ω
        (propagatorW C v v φ) +
      ∫ u in (0 : ℝ)..τ, r2QuadField σ (HRS.Whole.withDensityReal ρ) P X v ω
        (propagatorW C v (v + u) (generatorW C (v + u) φ)) := by
  let G0 : ℝ → Euc d → ℝ := fun τ => propagatorW C v (v + τ) φ
  let G1 : ℝ → Euc d → ℝ := fun τ =>
    propagatorW C v (v + τ) (generatorW C (v + τ) φ)
  have hv' : v ∈ Icc (0 : ℝ) T := ⟨hv, hvT⟩
  have h0 : ∀ τ ∈ Icc (0 : ℝ) (T - v), MemCb 2 (G0 τ) :=
    fun τ hτ => horb.cb0 hv' hτ
  have h1 : ∀ τ ∈ Icc (0 : ℝ) (T - v), MemCb 2 (G1 τ) :=
    fun τ hτ => horb.cb1 hv' hτ
  obtain ⟨G2, h2, hd12⟩ := horb.diff12 v hv'
  have hc : S53Cont (T - v) G1 := s53_cont_of_diff h1 h2 hd12
  have hft := fp81s21_centered_frozen_source_s53_ftc P ctx hN
    (show 0 ≤ T - v by linarith) (fun ω => X v.toNNReal ω)
    h0 h1 (horb.diff01 v hv') hc ((N : ℝ) / 2) hF hPath hMean hProd
  have heq (f : Euc d → ℝ) (ω : Ω) :
      r2QuadField σ (HRS.Whole.withDensityReal ρ) P X v ω f =
        (N : ℝ) / 2 * s53_Dk σ ρ f (X v.toNNReal ω) -
          ∫ ω', (N : ℝ) / 2 * s53_Dk σ ρ f (X v.toNNReal ω') ∂P := by
    rw [fp81s21_r2QuadField_eq_scaled_s53_Dk, integral_const_mul]
    ring
  intro τ hτ ω
  rw [heq, heq]
  have hIntegral : (∫ u in (0 : ℝ)..τ,
      r2QuadField σ (HRS.Whole.withDensityReal ρ) P X v ω (G1 u)) =
      ∫ u in (0 : ℝ)..τ, ((N : ℝ) / 2 * s53_Dk σ ρ (G1 u) (X v.toNNReal ω) -
        ∫ ω', (N : ℝ) / 2 * s53_Dk σ ρ (G1 u) (X v.toNNReal ω') ∂P) := by
    apply intervalIntegral.integral_congr
    intro u hu
    exact heq (G1 u) ω
  rw [hIntegral]
  simpa [G0, G1] using hft τ hτ ω

#print axioms fp81s21_window_quad_frozen_ftc_of_integrability
end HRS.Fp81.S21
end
