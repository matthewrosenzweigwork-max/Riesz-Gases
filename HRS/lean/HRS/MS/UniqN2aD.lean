import HRS.MS.UniqN2aC
import HRS.MS.Sf8

/-!
# N2a of `UniqPlan.md`, part (d): the identity `∫ f a H_i = - symPairing` and the `S.B.8` bound

`n2a_main` combines `trunc_tendsto` (part (c)) with `Sf8.same_function_rd_weighted_proof`: for
`ς = (advCutoff χ Ψ τ z)²`, `ψ = ς f ∈ C¹_c`, `H_i = kernelConvDeriv d s i ψ`,
`∫ f a H_i = - symPairing (∂_i g) a f ς` and the weighted same-function bound.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqN2a

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.UniqN0 HRS.MS.UniqM1
  HRS.MS.UniqT3

variable {d : ℕ}

theorem lip_continuous {La : ℝ} {a : Euc d → ℝ} (ha : HRS.PDE.ToolboxRd.IsLipschitz La a) :
    Continuous a := by
  have : LipschitzWith (Real.toNNReal La) a := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, dist_eq_norm, Real.coe_toNNReal']
    exact (ha x y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  exact this.continuous

/-- `a f` is integrable when `a` decays like `⟨x⟩^{-(d+3)}` and `f` has uniformly bounded local mass. -/
theorem af_integrable {Λ A : ℝ} {a f : Euc d → ℝ} (hac : Continuous a)
    (haΛ : ∀ x, jbracket x ^ ((d : ℝ) + 3) * |a x| ≤ Λ) (hA : LocMass A f) :
    Integrable (fun y => a y * f y) := by
  obtain ⟨Cc, hCc0, hCc⟩ := n0_cell_decay_mul (d := d) (κ := (d : ℝ) + 3) (by linarith)
  have hj : ∀ x : Euc d, 0 < jbracket x := fun x => by unfold jbracket; positivity
  have hΛ0 : 0 ≤ Λ := le_trans (by have := hj 0; positivity) (haΛ 0)
  have hbd : ∀ y : Euc d, |a y| ≤ (Λ * Real.sqrt 2 ^ ((d : ℝ) + 3)) *
      (1 + ‖y - 0‖) ^ (-((d : ℝ) + 3)) := by
    intro y
    have h1 : |a y| ≤ Λ * jbracket y ^ (-((d : ℝ) + 3)) := by
      rw [Real.rpow_neg (hj y).le]
      have hp : 0 < jbracket y ^ ((d : ℝ) + 3) := Real.rpow_pos_of_pos (hj y) _
      rw [← div_eq_mul_inv, le_div_iff₀ hp]
      linarith [haΛ y]
    calc |a y| ≤ Λ * jbracket y ^ (-((d : ℝ) + 3)) := h1
      _ ≤ Λ * (Real.sqrt 2 ^ ((d : ℝ) + 3) * (1 + ‖y‖) ^ (-((d : ℝ) + 3))) :=
          mul_le_mul_of_nonneg_left (n0_jbracket_rpow_le (by positivity) y) hΛ0
      _ = _ := by simp only [sub_zero]; ring
  have h := hCc 0 (Λ * Real.sqrt 2 ^ ((d : ℝ) + 3)) A f a (by positivity) hA hbd
  exact ((h.2 hac.aestronglyMeasurable).1).congr (Eventually.of_forall fun y => mul_comm _ _)

theorem kcd_bounded {s : ℝ} (hs0 : 0 < s) (hsd : s < d) (hs1 : (d : ℝ) < s + 1) (i : Fin d)
    {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    ∃ C0 : ℝ, ∀ y, |kernelConvDeriv d s i ψ y| ≤ C0 := by
  obtain ⟨C0, hC0⟩ := pv_bound hs0 hsd hs1 i hψ hψc
  refine ⟨C0, fun y => ?_⟩
  refine le_of_tendsto (pv_tendsto hs0 hsd hs1 i hψ hψc y).abs ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε using hC0 y hε

theorem kcd_aesm (s : ℝ) (i : Fin d) {ψ : Euc d → ℝ} (hψ : ContDiff ℝ 1 ψ) :
    AEStronglyMeasurable (kernelConvDeriv d s i ψ) volume := by
  have hm : Measurable (fun p : Euc d × Euc d =>
      rieszKernel d s (p.1 - p.2) * fderiv ℝ ψ p.2 (EuclideanSpace.single i (1 : ℝ))) :=
    ((g_meas s).comp (measurable_fst.sub measurable_snd)).mul
      ((((hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const).measurable).comp
        measurable_snd)
  exact (hm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable

end HRS.MS.UniqN2a
