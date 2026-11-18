import Mathlib

/-!
# S21G2 S26 -- mixed-coupling estimate (R26-T3.S26)

`|E F(X)(A) - E F(Y)(A')| ≤ E‖A - A'‖ + ‖A'‖_{L²} ‖X - Y‖_{L²}` for a map `F` into the unit ball of the dual with
`F` 1-Lipschitz.  Split `F(X)A - F(Y)A' = F(X)(A - A') + (F(X) - F(Y))A'`, then Cauchy-Schwarz.
The contract is taken verbatim.  Helper names carry the prefix `s21g2_s26_`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace HRS.MS.R26T3

theorem r26t3_mixed_coupling {B E : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace B] [BorelSpace B]
    [MeasurableSpace E] [BorelSpace E] {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → B) (A A' : Ω → E)
    (F : B → E →L[ℝ] ℝ) (hF : ∀ x, ‖F x‖ ≤ 1)
    (hLip : ∀ x y, ‖F x-F y‖ ≤ ‖x-y‖)
    (hm : AEStronglyMeasurable X P ∧ AEStronglyMeasurable Y P ∧
      AEStronglyMeasurable A P ∧ AEStronglyMeasurable A' P)
    (h2 : MemLp (fun ω => X ω-Y ω) 2 P ∧ MemLp A 2 P ∧ MemLp A' 2 P) :
    |(∫ ω, F (X ω) (A ω) ∂P)-(∫ ω, F (Y ω) (A' ω) ∂P)| ≤
      (∫ ω, ‖A ω-A' ω‖ ∂P) +
      Real.sqrt (∫ ω, ‖A' ω‖^2 ∂P)*Real.sqrt (∫ ω, ‖X ω-Y ω‖^2 ∂P) := by
  obtain ⟨hX, hY, hA, hA'⟩ := hm
  obtain ⟨hXY, hA2, hA'2⟩ := h2
  have hFc : Continuous F := LipschitzWith.continuous (LipschitzWith.of_dist_le_mul (K := 1)
    fun x y => by simpa [dist_eq_norm] using hLip x y)
  have hc : Continuous (fun q : (E →L[ℝ] ℝ) × E => q.1 q.2) :=
    (isBoundedBilinearMap_apply (𝕜 := ℝ) (E := E) (F := ℝ)).continuous
  have hap : ∀ (U : Ω → B) (V : Ω → E), AEStronglyMeasurable U P → AEStronglyMeasurable V P →
      AEStronglyMeasurable (fun ω => F (U ω) (V ω)) P := fun U V hU hV =>
    hc.comp_aestronglyMeasurable ((hFc.comp_aestronglyMeasurable hU).prodMk hV)
  have iA : Integrable (fun ω => ‖A ω‖) P := (hA2.integrable one_le_two).norm
  have iA' : Integrable (fun ω => ‖A' ω‖) P := (hA'2.integrable one_le_two).norm
  have iL : ∀ (U : Ω → B) (V : Ω → E), AEStronglyMeasurable U P → AEStronglyMeasurable V P →
      Integrable (fun ω => ‖V ω‖) P → Integrable (fun ω => F (U ω) (V ω)) P :=
    fun U V hU hV hi => hi.mono' (hap U V hU hV) (ae_of_all _ fun ω => by
      calc ‖F (U ω) (V ω)‖ ≤ ‖F (U ω)‖ * ‖V ω‖ := (F (U ω)).le_opNorm _
        _ ≤ 1 * ‖V ω‖ := by gcongr; exact hF _
        _ = ‖V ω‖ := one_mul _)
  have i1 := iL X A hX hA iA
  have i2 := iL Y A' hY hA' iA'
  have iDA : Integrable (fun ω => ‖A ω - A' ω‖) P := (hA2.sub hA'2).integrable one_le_two |>.norm
  have hfg : Integrable (fun ω => ‖A' ω‖ * ‖X ω - Y ω‖) P := hA'2.norm.integrable_mul hXY.norm
  have pw : ∀ ω, |F (X ω) (A ω) - F (Y ω) (A' ω)| ≤ ‖A ω - A' ω‖ + ‖A' ω‖ * ‖X ω - Y ω‖ := fun ω => by
    have e : F (X ω) (A ω) - F (Y ω) (A' ω) =
        F (X ω) (A ω - A' ω) + (F (X ω) - F (Y ω)) (A' ω) := by
      simp only [map_sub, ContinuousLinearMap.sub_apply]; ring
    rw [e]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · calc |F (X ω) (A ω - A' ω)| ≤ ‖F (X ω)‖ * ‖A ω - A' ω‖ := (F (X ω)).le_opNorm _
        _ ≤ 1 * ‖A ω - A' ω‖ := by gcongr; exact hF _
        _ = ‖A ω - A' ω‖ := one_mul _
    · calc |(F (X ω) - F (Y ω)) (A' ω)| ≤ ‖F (X ω) - F (Y ω)‖ * ‖A' ω‖ := (F (X ω) - F (Y ω)).le_opNorm _
        _ ≤ ‖X ω - Y ω‖ * ‖A' ω‖ := by gcongr; exact hLip _ _
        _ = ‖A' ω‖ * ‖X ω - Y ω‖ := mul_comm _ _
  have iS : Integrable (fun ω => ‖A ω - A' ω‖ + ‖A' ω‖ * ‖X ω - Y ω‖) P := iDA.add hfg
  rw [← integral_sub i1 i2]
  refine (abs_integral_le_integral_abs).trans ?_
  refine (integral_mono (i1.sub i2).abs iS pw).trans ?_
  rw [integral_add iDA hfg]
  gcongr
  have := integral_mul_le_Lp_mul_Lq_of_nonneg (p := 2) (q := 2) Real.HolderConjugate.two_two
    (ae_of_all _ fun ω => norm_nonneg (A' ω)) (ae_of_all _ fun ω => norm_nonneg (X ω - Y ω))
    (by simpa using hA'2.norm) (by simpa using hXY.norm)
  simpa [Real.sqrt_eq_rpow, Real.rpow_two] using this

end HRS.MS.R26T3
