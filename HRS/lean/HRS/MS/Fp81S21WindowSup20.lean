import HRS.MS.Fp81S21WindowSup19

/-!
# S2.1(iii), packet 9d: centering a pathwise FTC by Fubini

This adapter separates the pathwise S5.3 FTC from the actual-law centering.
The product-integrability premise is stated on each finite interval, exactly
where Fubini is used. The hypotheses retain integrability of each centered
slice and the mean derivative, so the resulting interval identity is an
ordinary Bochner-integral equality.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Set

namespace HRS.Fp81.S21

/-- Center a pathwise integral identity by the actual probability law. -/
theorem fp81s21_centered_ftc_of_product_integrable
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {T : ℝ} (hT : 0 ≤ T)
    (F G : ℝ → Ω → ℝ)
    (hF : ∀ t ∈ Icc (0 : ℝ) T, Integrable (F t) P)
    (hGpath : ∀ t ∈ Icc (0 : ℝ) T, ∀ ω,
      IntervalIntegrable (fun s => G s ω) volume 0 t)
    (hGmean : ∀ t ∈ Icc (0 : ℝ) T,
      IntervalIntegrable (fun s => ∫ ω, G s ω ∂P) volume 0 t)
    (hGprod : ∀ t ∈ Icc (0 : ℝ) T,
      Integrable (Function.uncurry (fun ω s => G s ω))
        (P.prod (volume.restrict (Ioc (0 : ℝ) t))))
    (hrep : ∀ t ∈ Icc (0 : ℝ) T, ∀ ω,
      F t ω = F 0 ω + ∫ s in (0 : ℝ)..t, G s ω) :
    ∀ t ∈ Icc (0 : ℝ) T, ∀ ω,
      F t ω - ∫ ω', F t ω' ∂P =
        F 0 ω - ∫ ω', F 0 ω' ∂P +
          ∫ s in (0 : ℝ)..t, (G s ω - ∫ ω', G s ω' ∂P) := by
  intro t ht ω
  let J : Ω → ℝ := fun ω => ∫ s in (0 : ℝ)..t, G s ω
  have hF0 : Integrable (F 0) P := hF 0 ⟨le_rfl, hT⟩
  have hFt : Integrable (F t) P := hF t ht
  have hJ : Integrable J P := by
    refine (hFt.sub hF0).congr (Filter.Eventually.of_forall fun ω' => ?_)
    dsimp [J]
    rw [hrep t ht ω']
    ring
  have hFtIntegral :
      (∫ ω', F t ω' ∂P) = ∫ ω', F 0 ω' + J ω' ∂P := by
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω' => by
      dsimp [J]
      exact hrep t ht ω')
  have hswap := integral_integral_swap (μ := P)
    (ν := volume.restrict (Ioc (0 : ℝ) t))
    (f := fun ω' s => G s ω') (hGprod t ht)
  have hswapI :
      (∫ ω', J ω' ∂P) =
        ∫ s in (0 : ℝ)..t, ∫ ω', G s ω' ∂P := by
    dsimp [J]
    simpa only [intervalIntegral.integral_of_le ht.1] using hswap
  have hsub := intervalIntegral.integral_sub (hGpath t ht ω) (hGmean t ht)
  calc
    F t ω - ∫ ω', F t ω' ∂P =
        (F 0 ω + J ω) - ((∫ ω', F 0 ω' ∂P) + ∫ ω', J ω' ∂P) := by
          rw [hrep t ht ω, hFtIntegral, integral_add hF0 hJ]
    _ = F 0 ω - ∫ ω', F 0 ω' ∂P +
          ((∫ s in (0 : ℝ)..t, G s ω) -
            ∫ s in (0 : ℝ)..t, ∫ ω', G s ω' ∂P) := by
          rw [hswapI]
          dsimp [J]
          ring
    _ = F 0 ω - ∫ ω', F 0 ω' ∂P +
          ∫ s in (0 : ℝ)..t, (G s ω - ∫ ω', G s ω' ∂P) := by
          rw [← hsub]

#print axioms fp81s21_centered_ftc_of_product_integrable

end HRS.Fp81.S21

end
