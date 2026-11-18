import HRS.MS.UniqN2aE
import HRS.MH.ScreenedF1
import HRS.MH.ScreenedF3

/-!
# N2a of `UniqPlan.md`, part (f): the final statement in terms of `LocMass A f`

The cell quantity `S` of `n2a_main` is replaced by the uniform local mass: every flow cell is inside a
ball of radius `R = e^{CF T}√d + 1` (`flowCell_geometry_proof`, `flow_lip_sep_proof`), which is covered by
`N` unit balls (`exists_ball_sq_bound`), so `S² = N A²`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqN2a

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqN0 HRS.MS.UniqM1
  HRS.MS.UniqT3

variable {d : ℕ}

theorem n2a_main_locmass (hd : 1 ≤ d) (s : ℝ) (hs1 : (d : ℝ) - 1 < s) (hsd : s < d)
    (m : ℕ) (Cb T : ℝ) :
    ∀ χ χh : Euc d → ℝ, IsCutoffPair χ χh →
    ∃ (C : ℝ) (N : ℕ), ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d),
      HRS.Whole.IsAdvectingDrift m Cb T b → HRS.Whole.IsNegDriftFlow T b Ψ →
      ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ z : Euc d, ∀ Lχ : ℝ,
        HRS.PDE.ToolboxRd.IsLipschitz Lχ (advCutoff χ Ψ τ z) →
      ∀ (i : Fin d) (La Λ : ℝ) (a f : Euc d → ℝ), HRS.PDE.ToolboxRd.IsLipschitz La a →
        (∀ x, jbracket x ^ ((d : ℝ) + 3) * |a x| ≤ Λ) → Measurable f →
      ∀ A : ℝ, LocMass A f →
      ContDiff ℝ 1 (fun x => advCutoff χ Ψ τ z x ^ 2 * f x) →
      HasCompactSupport (fun x => advCutoff χ Ψ τ z x ^ 2 * f x) →
      Integrable (fun y => f y * a y *
        kernelConvDeriv d s i (fun x => advCutoff χ Ψ τ z x ^ 2 * f x) y) ∧
      ∫ y, f y * a y * kernelConvDeriv d s i (fun x => advCutoff χ Ψ τ z x ^ 2 * f x) y =
        - symPairing (fun w => rieszKernelGrad d s w i) a f
            (fun x => advCutoff χ Ψ τ z x ^ 2) ∧
      |∫ y, f y * a y * kernelConvDeriv d s i (fun x => advCutoff χ Ψ τ z x ^ 2 * f x) y| ≤
        C * max 1 s * (La + Λ) * (1 + Lχ) ^ 2 * ((N : ℝ) * A ^ 2) * (C * Real.exp (C * d * τ)) := by
  intro χ χh hχ
  obtain ⟨C, hC⟩ := n2a_main hd s hs1 hsd m Cb T χ χh hχ
  obtain ⟨CF, hCF0, hCF⟩ := HRS.MH.Screened.flow_lip_sep_proof hd m Cb T χ χh hχ
  set R : ℝ := Real.exp (CF * T) * Real.sqrt d + 1 with hR
  obtain ⟨N, hN⟩ := exists_ball_sq_bound d R
  refine ⟨C, N, fun b Ψ hb hΨ τ hτ z Lχ hLχ i La Λ a f ha haΛ hf A hA hψ hψc => ?_⟩
  set S : ℝ := Real.sqrt N * |A| with hS
  have hS0 : 0 ≤ S := by positivity
  have hS2 : S ^ 2 = (N : ℝ) * A ^ 2 := by
    rw [hS, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N), sq_abs]
  have hgeo := HRS.MH.Screened.flowCell_geometry_proof Ψ τ (Real.exp (CF * τ)) (Real.exp_pos _).le
    (hΨ.bij τ hτ) (hCF b Ψ hb hΨ τ hτ).1
  have hLle : Real.exp (CF * τ) ≤ Real.exp (CF * T) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hτ.2 hCF0)
  have hcell : ∀ z' : Fin d → ℤ,
      eLpNorm ((flowCell Ψ τ z').indicator f) 2 volume ≤ ENNReal.ofReal S := by
    intro z'
    have hmeas : MeasurableSet (flowCell Ψ τ z') := hgeo.2.1 z'
    have hsub : flowCell Ψ τ z' ⊆ ball (Ψ τ (latticePt z')) R := by
      intro y hy
      have h1 := hgeo.2.2.1 z' hy
      rw [mem_closedBall, dist_eq_norm] at h1
      rw [mem_ball, dist_eq_norm]
      have : Real.exp (CF * τ) * Real.sqrt d ≤ Real.exp (CF * T) * Real.sqrt d :=
        mul_le_mul_of_nonneg_right hLle (Real.sqrt_nonneg _)
      linarith
    have hind : AEStronglyMeasurable ((flowCell Ψ τ z').indicator f) volume :=
      hf.aestronglyMeasurable.indicator hmeas
    have hsq : eLpNorm ((flowCell Ψ τ z').indicator f) 2 volume ^ 2 ≤ ENNReal.ofReal S ^ 2 := by
      rw [sq_eLpNorm_two hind]
      have hl : ∫⁻ y, ‖(flowCell Ψ τ z').indicator f y‖ₑ ^ 2 =
          ∫⁻ y in flowCell Ψ τ z', ‖f y‖ₑ ^ 2 := by
        rw [← lintegral_indicator hmeas]
        refine lintegral_congr fun y => ?_
        by_cases hy : y ∈ flowCell Ψ τ z' <;> simp [hy]
      rw [hl]
      calc ∫⁻ y in flowCell Ψ τ z', ‖f y‖ₑ ^ 2
          ≤ ∫⁻ y in ball (Ψ τ (latticePt z')) R, ‖f y‖ₑ ^ 2 := lintegral_mono_set hsub
        _ ≤ (N : ℝ≥0∞) * ENNReal.ofReal (A ^ 2) := hN A f hA _
        _ = ENNReal.ofReal S ^ 2 := by
            rw [← ENNReal.ofReal_pow hS0, hS2, ENNReal.ofReal_mul (Nat.cast_nonneg N),
              ENNReal.ofReal_natCast]
    by_contra hlt
    exact absurd hsq (not_le.2 (ENNReal.pow_lt_pow_left two_ne_zero (not_le.1 hlt)))
  obtain ⟨h1, h2, h3⟩ := hC b Ψ hb hΨ τ hτ z Lχ hLχ i La Λ a f ha haΛ hf A hA hψ hψc S hS0 hcell
  exact ⟨h1, h2, by rw [hS2] at h3; exact h3⟩

end HRS.MS.UniqN2a
