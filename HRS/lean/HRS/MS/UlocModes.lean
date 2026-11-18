import HRS.MS.UlocMWAux2
import HRS.Whole.AppendixALemmas

/-!
# MS-ULOC-MW (A): Lemma S.A.31(ii), the plane waves `cos(2π k·x)`, `sin(2π k·x)` in `H^m_uloc`

`‖cos(2π k·), sin(2π k·)‖_{H^m_uloc} ≤ C (1+|k|)^m`.  Route: translation invariance of `H^m`
(`χ(x - z) cos(2π k·x) = τ_z[χ cos(2π k·y + 2π k·z)]`) reduces to the modulated cutoffs
`χ(y) cos(2π k·y + φ)` (`UlocMWAux2.lean`: the Fourier transform of `χ e^{±2πi k·y}` is the translate of
`χ̂`, plus Peetre's inequality).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff ComplexConjugate

open HRS.Whole.AppendixA

namespace HRS.MS.UlocModes
open HRS.MS.UlocMW HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

/-- the uniform bound for a translated modulated cutoff -/
theorem um_trans_bound (m : ℕ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (k : Euc d) (z : Euc d) (ψ : ℝ) :
    HRS.Whole.sobolevNormE (m : ℝ) (fun x => χ (x - z) * Real.cos (2 * Real.pi * inner ℝ k x + ψ)) ≤
      ENNReal.ofReal ((HRS.Whole.sobolevNormE (m : ℝ) χ).toReal *
        (Real.sqrt 2 * (1 + 2 * Real.pi)) ^ m * (1 + ‖k‖) ^ m) := by
  have hfin := um_chi_finite hχ.1 hχ.2.1 (s := (m : ℝ)) (Nat.cast_nonneg m)
  set N := (HRS.Whole.sobolevNormE (m : ℝ) χ).toReal with hN
  have e : (fun x => χ (x - z) * Real.cos (2 * Real.pi * inner ℝ k x + ψ)) =
      fun x => (fun y => χ y * Real.cos (2 * Real.pi * inner ℝ k y +
        (2 * Real.pi * inner ℝ k z + ψ))) (x - z) := by
    ext x
    simp only [inner_sub_right]
    congr 2
    ring
  rw [e]
  refine (HRS.MS.SobMul.sobolevNormE_translate (m : ℝ) (fun y => χ y * Real.cos (2 * Real.pi * inner ℝ k y +
    (2 * Real.pi * inner ℝ k z + ψ))) z).le.trans ?_
  calc _ ≤ ENNReal.ofReal (Real.sqrt (2 ^ (m : ℝ) * wt k ^ (m : ℝ))) *
        HRS.Whole.sobolevNormE (m : ℝ) χ := um_mod_bound' hχ.1 hχ.2.1 (Nat.cast_nonneg m) k _
    _ = ENNReal.ofReal (Real.sqrt (2 ^ (m : ℝ) * wt k ^ (m : ℝ)) * N) := by
        rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _), hN, ENNReal.ofReal_toReal hfin]
    _ ≤ _ := by
        apply ENNReal.ofReal_le_ofReal
        have h0 : 0 ≤ N := ENNReal.toReal_nonneg
        calc Real.sqrt (2 ^ (m : ℝ) * wt k ^ (m : ℝ)) * N
            ≤ ((Real.sqrt 2 * (1 + 2 * Real.pi)) ^ m * (1 + ‖k‖) ^ m) * N :=
              mul_le_mul_of_nonneg_right (um_sqrt_le m k) h0
          _ = _ := by ring

/-- Lemma S.A.31(ii) -/
theorem uloc_embedding_modes_proof (m : ℕ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, ∀ k : Euc d,
      ulocNormE m χ (fun x => Real.cos (2 * Real.pi * inner ℝ k x)) ≤
        ENNReal.ofReal (C * (1 + ‖k‖) ^ m) ∧
      ulocNormE m χ (fun x => Real.sin (2 * Real.pi * inner ℝ k x)) ≤
        ENNReal.ofReal (C * (1 + ‖k‖) ^ m) := by
  refine ⟨(HRS.Whole.sobolevNormE (m : ℝ) χ).toReal * (Real.sqrt 2 * (1 + 2 * Real.pi)) ^ m, fun k => ?_⟩
  constructor
  · unfold ulocNormE
    refine iSup_le fun z => ?_
    have := um_trans_bound m χ hχ k z 0
    simpa [mul_assoc] using this
  · unfold ulocNormE
    refine iSup_le fun z => ?_
    have := um_trans_bound m χ hχ k z (-(Real.pi / 2))
    have e : (fun x => χ (x - z) * Real.cos (2 * Real.pi * inner ℝ k x + -(Real.pi / 2))) =
        fun x => χ (x - z) * Real.sin (2 * Real.pi * inner ℝ k x) := by
      ext x
      rw [← sub_eq_add_neg, Real.cos_sub_pi_div_two]
    rw [e] at this
    simpa [mul_assoc] using this

example := (@uloc_embedding_modes_proof : type_of% @HRS.Whole.AppendixALemmas.uloc_embedding_modes)

end HRS.MS.UlocModes
