import HRS.MS.Fp81S21WindowSup39

/-! Frozen-source centered FTC from raw sixth-moment slices. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.S53 HRS.MS.R2WinErr

/-- Uniform raw sixth moments of the orbit and its terminal derivative imply
the actual-law centered frozen-source quadratic-field FTC. -/
theorem fp81s21_window_quad_frozen_ftc_of_sixth
    {d N : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {σ T v : ℝ} {ρ : Euc d → ℝ} {Mρ : ℝ} {C : WholeCoeff d}
    {φ : Euc d → ℝ} (horb : S104nOrbit C φ T)
    (ctx : S53Ctx σ ρ Mρ) (hN : 0 < N) (hv : 0 ≤ v) (hvT : v ≤ T)
    (X : ℝ≥0 → Ω → EucConfig d N) (hX : Measurable (X v.toNNReal))
    (M : ℝ) (hM : 0 ≤ M)
    (hSix0 : ∀ τ ∈ Icc (0 : ℝ) (T - v), SixthBound P
      (fun ω => fp81s21_frozen_raw_field σ ρ
        (fun u => propagatorW C v (v + u) φ) (X v.toNNReal) (τ, ω)) M)
    (hSix1 : ∀ τ ∈ Icc (0 : ℝ) (T - v), SixthBound P
      (fun ω => fp81s21_frozen_raw_field σ ρ
        (fun u => propagatorW C v (v + u) (generatorW C (v + u) φ))
          (X v.toNNReal) (τ, ω)) M) :
    ∀ τ ∈ Icc (0 : ℝ) (T - v), ∀ ω,
      r2QuadField σ (HRS.Whole.withDensityReal ρ) P X v ω
        (propagatorW C v (v + τ) φ) =
      r2QuadField σ (HRS.Whole.withDensityReal ρ) P X v ω
        (propagatorW C v v φ) +
      ∫ u in (0 : ℝ)..τ, r2QuadField σ (HRS.Whole.withDensityReal ρ) P X v ω
        (propagatorW C v (v + u) (generatorW C (v + u) φ)) := by
  let G0 : ℝ → Euc d → ℝ := fun u => propagatorW C v (v + u) φ
  let G1 : ℝ → Euc d → ℝ := fun u =>
    propagatorW C v (v + u) (generatorW C (v + u) φ)
  have hv' : v ∈ Icc (0 : ℝ) T := ⟨hv, hvT⟩
  have hTv : 0 ≤ T - v := by linarith
  have h0 : ∀ u ∈ Icc (0 : ℝ) (T - v), MemCb 2 (G0 u) :=
    fun u hu => horb.cb0 hv' hu
  have h1 : ∀ u ∈ Icc (0 : ℝ) (T - v), MemCb 2 (G1 u) :=
    fun u hu => horb.cb1 hv' hu
  have hc0 : S53Cont (T - v) G0 := s53_cont_of_diff h0 h1 (horb.diff01 v hv')
  obtain ⟨G2, h2, hd12⟩ := horb.diff12 v hv'
  have hc1 : S53Cont (T - v) G1 := s53_cont_of_diff h1 h2 hd12
  have hSlice := fp81s21_frozen_raw_slice_integrable P (σ := σ) hTv ctx.hρ
    G0 h0 hc0 (X v.toNNReal) hX M hSix0
  have hF : ∀ τ ∈ Icc (0 : ℝ) (T - v), Integrable (fun ω =>
      (N : ℝ) / 2 * s53_Dk σ ρ (G0 τ) (X v.toNNReal ω)) P := by
    intro τ hτ
    change Integrable (fun ω => fp81s21_frozen_raw_field σ ρ G0
      (X v.toNNReal) (τ, ω)) P
    exact hSlice τ hτ
  have hFub := fp81s21_frozen_raw_fubini_of_sixth P (σ := σ) hTv ctx.hρ G1 h1 hc1
    (X v.toNNReal) hX M hM hSix1
  have hPath := fp81s21_window_raw_quad_derivative_interval_integrable horb ctx hN hv hvT X
  apply fp81s21_window_quad_frozen_ftc_of_integrability P horb ctx hN hv hvT X hF hPath
  · intro τ hτ
    simpa only [fp81s21_frozen_raw_field, G1] using (hFub τ hτ).2
  · intro τ hτ
    change Integrable (fun z : Ω × ℝ => (N : ℝ) / 2 * s53_Dk σ ρ
      (G1 z.2) (X v.toNNReal z.1)) (P.prod (volume.restrict (Ioc (0 : ℝ) τ)))
    exact (hFub τ hτ).1

#print axioms fp81s21_window_quad_frozen_ftc_of_sixth
end HRS.Fp81.S21
end
