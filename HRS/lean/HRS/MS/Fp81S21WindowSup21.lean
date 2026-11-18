import HRS.MS.Fp81S21WindowSup20

/-!
# S2.1(iii), packet 9d: the frozen-source centered commutator FTC

At a fixed physical source time, `s53_ftc` differentiates the commutator
functional along a terminal-time family. The normalization proved in file 16
identifies the particle quadratic field with `(N/2)` times the centered `s53_Dk`
observable. The product-integrability assumptions below are precisely those
needed to pass this pathwise identity through the actual particle expectation.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.S53

/-- The quadratic field at a fixed time is `(N/2)` times the centered S5.3
commutator functional. -/
theorem fp81s21_r2QuadField_eq_scaled_s53_Dk
    {d N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (s : ℝ) (ρ : Euc d → ℝ) (P : Measure Ω)
    (X : ℝ≥0 → Ω → EucConfig d N) (u : ℝ) (ω : Ω)
    (f : Euc d → ℝ) :
    HRS.Whole.r2QuadField s (HRS.Whole.withDensityReal ρ) P X u ω f =
      (N : ℝ) / 2 *
        (HRS.MS.S53.s53_Dk s ρ f (X u.toNNReal ω) -
          ∫ ω', HRS.MS.S53.s53_Dk s ρ f (X u.toNNReal ω') ∂P) := by
  unfold HRS.Whole.r2QuadField
  simp_rw [fp81s21_pairEnergy_eq_half_s53_Dk]
  rw [integral_const_mul]
  ring

/-- Center the fixed-source S5.3 FTC by the actual probability law. The
terminal-time family and its derivative need only satisfy the compiled S5.3
regularity conditions; the remaining hypotheses are product-integrability
adapters for applying Fubini on each finite interval. -/
theorem fp81s21_centered_frozen_source_s53_ftc
    {d N : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {s : ℝ} {ρ : Euc d → ℝ} {Mρ : ℝ}
    (ctx : S53Ctx s ρ Mρ) (hN : 0 < N)
    {T : ℝ} (hT : 0 ≤ T)
    (X : Ω → EucConfig d N)
    {G0 G1 : ℝ → Euc d → ℝ}
    (hG0 : ∀ t ∈ Icc (0 : ℝ) T, MemCb 2 (G0 t))
    (hG1 : ∀ t ∈ Icc (0 : ℝ) T, MemCb 2 (G1 t))
    (hdiff : S53Diff T G0 G1) (hc1 : S53Cont T G1)
    (c : ℝ)
    (hF : ∀ t ∈ Icc (0 : ℝ) T,
      Integrable (fun ω => c * s53_Dk s ρ (G0 t) (X ω)) P)
    (hGpath : ∀ t ∈ Icc (0 : ℝ) T, ∀ ω,
      IntervalIntegrable (fun u => c * s53_Dk s ρ (G1 u) (X ω)) volume 0 t)
    (hGmean : ∀ t ∈ Icc (0 : ℝ) T,
      IntervalIntegrable (fun u =>
        ∫ ω, c * s53_Dk s ρ (G1 u) (X ω) ∂P) volume 0 t)
    (hGprod : ∀ t ∈ Icc (0 : ℝ) T,
      Integrable
        (Function.uncurry fun ω u => c * s53_Dk s ρ (G1 u) (X ω))
        (P.prod (volume.restrict (Ioc (0 : ℝ) t)))) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ ω,
      c * s53_Dk s ρ (G0 t) (X ω) -
          ∫ ω', c * s53_Dk s ρ (G0 t) (X ω') ∂P =
        c * s53_Dk s ρ (G0 0) (X ω) -
          ∫ ω', c * s53_Dk s ρ (G0 0) (X ω') ∂P +
          ∫ u in (0 : ℝ)..t,
            (c * s53_Dk s ρ (G1 u) (X ω) -
              ∫ ω', c * s53_Dk s ρ (G1 u) (X ω') ∂P) := by
  let F : ℝ → Ω → ℝ := fun t ω => c * s53_Dk s ρ (G0 t) (X ω)
  let G : ℝ → Ω → ℝ := fun u ω => c * s53_Dk s ρ (G1 u) (X ω)
  have hrep : ∀ t ∈ Icc (0 : ℝ) T, ∀ ω,
      F t ω = F 0 ω + ∫ u in (0 : ℝ)..t, G u ω := by
    intro t ht ω
    have hftc := s53_ftc ctx.hs0 ctx.hM0 ctx.hρ ctx.hrow hN
      hG0 hG1 hdiff hc1 (X ω) ht
    have hftc' : s53_Dk s ρ (G0 t) (X ω) =
        s53_Dk s ρ (G0 0) (X ω) +
          ∫ u in (0 : ℝ)..t, s53_Dk s ρ (G1 u) (X ω) := by
      rw [intervalIntegral.integral_of_le ht.1]
      exact hftc
    dsimp [F, G]
    calc
      c * s53_Dk s ρ (G0 t) (X ω) =
          c * (s53_Dk s ρ (G0 0) (X ω) +
            ∫ u in (0 : ℝ)..t, s53_Dk s ρ (G1 u) (X ω)) := by rw [hftc']
      _ = c * s53_Dk s ρ (G0 0) (X ω) +
          ∫ u in (0 : ℝ)..t, c * s53_Dk s ρ (G1 u) (X ω) := by
            rw [intervalIntegral.integral_const_mul]
            ring
  have hcent := fp81s21_centered_ftc_of_product_integrable
    P hT F G hF hGpath hGmean hGprod hrep
  simpa [F, G] using hcent

#print axioms fp81s21_r2QuadField_eq_scaled_s53_Dk
#print axioms fp81s21_centered_frozen_source_s53_ftc

end HRS.Fp81.S21

end
