import HRS.MS.WrPress
import HRS.MS.WrEntAux1

/-!
# HRS.MS.WrEntAux2 -- the tilt identity for `pairGibbs` on `EucConfig d N` (WR-9, part 2)

Packet WR-9 of `docs/SUPP_FOUND_PACKETS.md` (Track D), namespace `HRS.MS.Wr`.

* `wr9_measurable_pairEnergy`, `wr9_rieszKernel_meas`: measurability of `X ↦ F_N^k(X,μ)` and of `g`.
* `wr9_ok_of_gwd`, `wr9_ok_of_sub`: `Wr8Ok` for `G` from `GibbsWellDefined`, and for `H` from
  `GibbsWellDefined (G - θ H)` with `θ ≠ 0` (integrability of the `h`-rows is *derived*, not assumed).
* `wr9_pairEnergy_sub`: `F^{G - θ H} = F^G - θ F^H` (exact, no diagonal fuss: the energy only sees the
  rows and the double integral, all integrable).
* `wr9_gibbs_prob`: `pairGibbs G N b μ` is a probability measure under `GibbsWellDefined`.
* `wr9_tilt`: `E_Q[e^{Ψ}] = K⁻¹ ∫ e^{W2} dμ^{⊗N}` whenever `Ψ - bN F^G = W2` pointwise
  (`N:eq:tilt-partition`, in `lintegral` form so that no junk Bochner value can occur).
* `wr9_ratio_bound`: `|log K| ≤ A`, `|log K'| ≤ A` imply `K⁻¹ K' ≤ e^{2A}` in `ℝ≥0∞`.

Helper lemmas carry the prefix `wr9_`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Function Set
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

open HRS.Whole

variable {d N : ℕ}

theorem wr9_rieszKernel_meas (s : ℝ) : Measurable (rieszKernel d s) := by
  unfold rieszKernel
  by_cases hs : s = 0
  · simp only [hs, ↓reduceIte]
    exact (Real.measurable_log.comp measurable_norm).neg
  · simp only [hs, ↓reduceIte]
    exact measurable_norm.pow_const _

theorem wr9_rieszKernel_pair_meas (s : ℝ) :
    Measurable (Function.uncurry fun x y : Euc d => rieszKernel d s (x - y)) :=
  (wr9_rieszKernel_meas s).comp (measurable_fst.sub measurable_snd)

theorem wr9_measurable_pairEnergy {μ : Measure (Euc d)} [SFinite μ] {k : Euc d → Euc d → ℝ}
    (hk : Measurable (Function.uncurry k)) :
    Measurable (fun X : EucConfig d N => pairEnergy k X μ) := by
  unfold pairEnergy
  have h1 : Measurable (fun X : EucConfig d N => ∑ i, ∑ j ∈ Finset.univ.erase i, k (X i) (X j)) :=
    Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => by
      have := hk.comp (f := fun X : EucConfig d N => (X i, X j))
        ((measurable_pi_apply i).prodMk (measurable_pi_apply j))
      exact this
  have h2 : Measurable (fun X : EucConfig d N => ∑ i, ∫ y, k (X i) y ∂μ) :=
    Finset.measurable_sum _ fun i _ =>
      (hk.stronglyMeasurable.integral_prod_right' (ν := μ)).measurable.comp (measurable_pi_apply i)
  exact ((h1.const_mul _).sub (h2.const_mul _)).add_const _

theorem wr9_ok_of_gwd {μ : Measure (Euc d)} {G : Euc d → Euc d → ℝ} {b : ℝ}
    (hm : Measurable (Function.uncurry G)) (hW : GibbsWellDefined G N b μ) : Wr8Ok μ G :=
  ⟨hm, hW.conv_integrable, hW.pair_integrable⟩

theorem wr9_ok_of_sub {μ : Measure (Euc d)} {G H : Euc d → Euc d → ℝ} {θ b : ℝ}
    (hG : Wr8Ok μ G) (hH : Measurable (Function.uncurry H)) (hθ : θ ≠ 0)
    (hW : GibbsWellDefined (fun x y => G x y - θ * H x y) N b μ) : Wr8Ok μ H := by
  refine ⟨hH, fun x => ?_, ?_⟩
  · have := ((hG.int x).sub (hW.conv_integrable x)).const_mul θ⁻¹
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.sub_apply]
    field_simp
    ring
  · have := ((hG.prod).sub hW.pair_integrable).const_mul θ⁻¹
    refine this.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, Pi.sub_apply]
    field_simp
    ring

theorem wr9_pairEnergy_sub {μ : Measure (Euc d)} [IsFiniteMeasure μ] {G H : Euc d → Euc d → ℝ}
    (hG : Wr8Ok μ G) (hH : Wr8Ok μ H) (θ : ℝ) (X : EucConfig d N) :
    pairEnergy (fun x y => G x y - θ * H x y) X μ = pairEnergy G X μ - θ * pairEnergy H X μ := by
  have hθH : Wr8Ok μ (fun x y => (-θ) * H x y) :=
    ⟨measurable_const.mul hH.meas, fun x => (hH.int x).const_mul _, hH.prod.const_mul _⟩
  have e1 := wr8_modEnergyE_add (N := N) hG hθH X
  have e2 : modEnergyE (fun x y => (-θ) * H x y) X μ = (-θ) * modEnergyE H X μ := by
    unfold modEnergyE
    simp only [← Finset.mul_sum, integral_const_mul]
    ring
  have e3 : (fun x y => G x y - θ * H x y) = fun x y => G x y + (-θ) * H x y := by
    funext x y; ring
  rw [e3]
  show modEnergyE (fun x y => G x y + (-θ) * H x y) X μ = modEnergyE G X μ - θ * modEnergyE H X μ
  rw [e1, e2]
  ring

theorem wr9_partition {μ : Measure (Euc d)} {G : Euc d → Euc d → ℝ} {b : ℝ}
    (hW : GibbsWellDefined G N b μ) :
    ∫⁻ X : EucConfig d N, ENNReal.ofReal (Real.exp (-b * N * pairEnergy G X μ))
        ∂(Measure.pi fun _ : Fin N => μ) = ENNReal.ofReal (pairNormalizer G N b μ) := by
  unfold pairNormalizer
  exact (ofReal_integral_eq_lintegral_ofReal hW.weight_integrable
    (Filter.Eventually.of_forall fun X => (Real.exp_pos _).le)).symm

theorem wr9_gibbs_prob {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {G : Euc d → Euc d → ℝ} {b : ℝ}
    (hW : GibbsWellDefined G N b μ) : IsProbabilityMeasure (pairGibbs G N b μ) := by
  constructor
  unfold pairGibbs
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    wr9_partition hW, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 hW.normalizer_pos).ne' ENNReal.ofReal_ne_top

/-- **Tilt identity** (`N:eq:tilt-partition`): if `Ψ - bN F^G = W2` pointwise then
`∫ e^{Ψ} dQ = K⁻¹ ∫ e^{W2} dμ^{⊗N}` in `ℝ≥0∞`. -/
theorem wr9_tilt {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {G : Euc d → Euc d → ℝ} {b : ℝ}
    (hGm : Measurable (Function.uncurry G))
    {Ψ W2 : EucConfig d N → ℝ} (hΨ : Measurable Ψ)
    (hrel : ∀ X, Ψ X - b * N * pairEnergy G X μ = W2 X) :
    ∫⁻ X, ENNReal.ofReal (Real.exp (Ψ X)) ∂(pairGibbs G N b μ) =
      (ENNReal.ofReal (pairNormalizer G N b μ))⁻¹ *
        ∫⁻ X, ENNReal.ofReal (Real.exp (W2 X)) ∂(Measure.pi fun _ : Fin N => μ) := by
  have hwm : Measurable (fun X : EucConfig d N =>
      ENNReal.ofReal (Real.exp (-b * N * pairEnergy G X μ))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul (wr9_measurable_pairEnergy hGm)))
  have hgm : Measurable (fun X : EucConfig d N => ENNReal.ofReal (Real.exp (Ψ X))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp hΨ)
  unfold pairGibbs
  rw [lintegral_smul_measure, smul_eq_mul]
  congr 1
  refine (lintegral_withDensity_eq_lintegral_mul _ hwm hgm).trans ?_
  refine lintegral_congr fun X => ?_
  simp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ← hrel X]
  congr 2
  ring

theorem wr9_ratio_bound {K K' A : ℝ} (hK : 0 < K) (hK' : 0 < K') (h1 : |Real.log K| ≤ A)
    (h2 : |Real.log K'| ≤ A) :
    (ENNReal.ofReal K)⁻¹ * ENNReal.ofReal K' ≤ ENNReal.ofReal (Real.exp (2 * A)) := by
  rw [← ENNReal.ofReal_inv_of_pos hK, ← ENNReal.ofReal_mul (inv_nonneg.2 hK.le)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hu : K' ≤ Real.exp A := (Real.log_le_iff_le_exp hK').1 (le_trans (le_abs_self _) h2)
  have hl : Real.exp (-A) ≤ K := (Real.le_log_iff_exp_le hK).1 (by linarith [neg_abs_le (Real.log K)])
  have hA : 0 ≤ A := le_trans (abs_nonneg _) h1
  calc K⁻¹ * K' ≤ (Real.exp (-A))⁻¹ * Real.exp A := by
        refine mul_le_mul (inv_anti₀ (Real.exp_pos _) hl) hu hK'.le (by positivity)
    _ = Real.exp (2 * A) := by
        rw [← Real.exp_neg, neg_neg, ← Real.exp_add]; congr 1; ring

end HRS.MS.Wr
