import HRS.MS.UniqN2aD

/-!
# N2a of `UniqPlan.md`, part (e): the final statement (hypothesis `S` form)

`n2a_main`: with the hypotheses of `same_function_rd_weighted` (for `κ = ∂_i g`, `K₀ = max 1 s`,
`ς = (advCutoff χ Ψ τ z)²`, `w = f`), and `ψ = ς f ∈ C¹_c`,
`∫ f a kernelConvDeriv d s i ψ = - symPairing κ a f ς`, with the weighted same-function bound.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqN2a

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqN0 HRS.MS.UniqM1
  HRS.MS.UniqT3

variable {d : ℕ}

theorem n2a_main (hd : 1 ≤ d) (s : ℝ) (hs1 : (d : ℝ) - 1 < s) (hsd : s < d)
    (m : ℕ) (Cb T : ℝ) :
    ∀ χ χh : Euc d → ℝ, IsCutoffPair χ χh →
    ∃ C : ℝ, ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d),
      HRS.Whole.IsAdvectingDrift m Cb T b → HRS.Whole.IsNegDriftFlow T b Ψ →
      ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ z : Euc d, ∀ Lχ : ℝ,
        HRS.PDE.ToolboxRd.IsLipschitz Lχ (advCutoff χ Ψ τ z) →
      ∀ (i : Fin d) (La Λ : ℝ) (a f : Euc d → ℝ), HRS.PDE.ToolboxRd.IsLipschitz La a →
        (∀ x, jbracket x ^ ((d : ℝ) + 3) * |a x| ≤ Λ) → Measurable f →
      ∀ A : ℝ, LocMass A f →
      ContDiff ℝ 1 (fun x => advCutoff χ Ψ τ z x ^ 2 * f x) →
      HasCompactSupport (fun x => advCutoff χ Ψ τ z x ^ 2 * f x) →
      ∀ S : ℝ, 0 ≤ S → (∀ z' : Fin d → ℤ,
        eLpNorm ((flowCell Ψ τ z').indicator f) 2 volume ≤ ENNReal.ofReal S) →
      Integrable (fun y => f y * a y *
        kernelConvDeriv d s i (fun x => advCutoff χ Ψ τ z x ^ 2 * f x) y) ∧
      ∫ y, f y * a y * kernelConvDeriv d s i (fun x => advCutoff χ Ψ τ z x ^ 2 * f x) y =
        - symPairing (fun w => rieszKernelGrad d s w i) a f
            (fun x => advCutoff χ Ψ τ z x ^ 2) ∧
      |∫ y, f y * a y * kernelConvDeriv d s i (fun x => advCutoff χ Ψ τ z x ^ 2 * f x) y| ≤
        C * max 1 s * (La + Λ) * (1 + Lχ) ^ 2 * S ^ 2 * (C * Real.exp (C * d * τ)) := by
  intro χ χh hχ
  have hs0 : 0 < s := by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hs1' : (d : ℝ) < s + 1 := by linarith
  obtain ⟨C, hC⟩ := Sf8.same_function_rd_weighted_proof hd s hs1 hsd m Cb T χ χh hχ
  refine ⟨C, fun b Ψ hb hΨ τ hτ z Lχ hLχ i La Λ a f ha haΛ hf A hA hψ hψc S hS hcell => ?_⟩
  obtain ⟨_, hTend, hBound⟩ := hC b Ψ hb hΨ τ hτ z Lχ hLχ (fun w => rieszKernelGrad d s w i)
    (max 1 s) (kap_neg s i) (kap_contDiffOn s i) (fun w hw => kap_bound hs0.le i hw) La Λ a f
    ha haΛ hf S hS hcell
  have hac : Continuous a := lip_continuous ha
  have haf : Integrable (fun y => a y * f y) := af_integrable hac haΛ hA
  have hT := trunc_tendsto hs0 hsd hs1' i (ς := fun x => advCutoff χ Ψ τ z x ^ 2) hac hf haf hψ hψc
  have hlim : ∫ y, f y * a y * kernelConvDeriv d s i (fun x => advCutoff χ Ψ τ z x ^ 2 * f x) y =
      - symPairing (fun w => rieszKernelGrad d s w i) a f (fun x => advCutoff χ Ψ τ z x ^ 2) := by
    have := tendsto_nhds_unique hT hTend
    linarith
  refine ⟨?_, hlim, ?_⟩
  · obtain ⟨C0, hC0⟩ := kcd_bounded hs0 hsd hs1' i hψ hψc
    have hfa : Integrable (fun y => f y * a y) :=
      haf.congr (Eventually.of_forall fun y => mul_comm _ _)
    refine (hfa.norm.mul_const C0).mono'
      ((hf.aestronglyMeasurable.mul hac.aestronglyMeasurable).mul (kcd_aesm s i hψ))
      (Eventually.of_forall fun y => ?_)
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_left
      (by simpa [Real.norm_eq_abs] using hC0 y) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  · rw [hlim, abs_neg]
    exact hBound

end HRS.MS.UniqN2a
