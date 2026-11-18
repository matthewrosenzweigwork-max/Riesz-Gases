import HRS.MS.Fp81S21WindowSup31

/-! Path integrability for the frozen-source commutator derivative. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
open scoped NNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.S53 HRS.MS.R2WinErr

/-- The terminal derivative of the raw commutator is continuous in elapsed
time and therefore interval integrable for every particle configuration. -/
theorem fp81s21_window_raw_quad_derivative_interval_integrable
    {d N : ℕ} {Ω : Type} [MeasurableSpace Ω]
    {σ T v : ℝ} {ρ : Euc d → ℝ} {Mρ : ℝ} {C : WholeCoeff d}
    {φ : Euc d → ℝ} (horb : S104nOrbit C φ T)
    (ctx : S53Ctx σ ρ Mρ) (hN : 0 < N) (hv : 0 ≤ v) (hvT : v ≤ T)
    (X : ℝ≥0 → Ω → EucConfig d N) :
    ∀ τ ∈ Icc (0 : ℝ) (T - v), ∀ ω,
      IntervalIntegrable (fun u => (N : ℝ) / 2 * s53_Dk σ ρ
        (propagatorW C v (v + u) (generatorW C (v + u) φ))
        (X v.toNNReal ω)) volume 0 τ := by
  let G1 : ℝ → Euc d → ℝ := fun u =>
    propagatorW C v (v + u) (generatorW C (v + u) φ)
  have hv' : v ∈ Icc (0 : ℝ) T := ⟨hv, hvT⟩
  have h1 : ∀ u ∈ Icc (0 : ℝ) (T - v), MemCb 2 (G1 u) :=
    fun u hu => horb.cb1 hv' hu
  obtain ⟨G2, h2, hd12⟩ := horb.diff12 v hv'
  have hc : S53Cont (T - v) G1 := s53_cont_of_diff h1 h2 hd12
  intro τ hτ ω
  have hcont := s53_Dk_continuousOn ctx.hs0 ctx.hM0 ctx.hρ ctx.hrow hN
    h1 hc (X v.toNNReal ω)
  have hint : IntervalIntegrable (fun u => s53_Dk σ ρ (G1 u)
      (X v.toNNReal ω)) volume 0 τ :=
    (hcont.mono (Icc_subset_Icc_right hτ.2)).intervalIntegrable_of_Icc hτ.1
  exact hint.const_mul ((N : ℝ) / 2)

#print axioms fp81s21_window_raw_quad_derivative_interval_integrable
end HRS.Fp81.S21
end
