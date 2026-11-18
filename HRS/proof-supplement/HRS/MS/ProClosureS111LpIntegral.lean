import Mathlib.MeasureTheory.Function.AEEqOfIntegral
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod

/-!
Interchanging an L³-valued Bochner integral and scalar representatives.
The proof tests against all measurable spatial sets. It never treats
point evaluation as a continuous functional on L³, and never assumes a
common spatial null set for all parameter values.
-/
set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section
open Classical MeasureTheory Filter Set
open scoped ENNReal NNReal Topology

namespace HRS.MS.ProClosureS111

variable {X A : Type*} [MeasurableSpace X] [MeasurableSpace A]
local instance : Fact ((1 : ℝ≥0∞) ≤ 3) := ⟨by norm_num⟩

theorem L3_integral_norm_le (mu : Measure X) [IsProbabilityMeasure mu]
    (f : X → ℝ) (hf : MemLp f 3 mu) :
    (∫ x, ‖f x‖ ∂mu) ≤ (eLpNorm f 3 mu).toReal := by
  rw [integral_norm_eq_lintegral_enorm hf.aestronglyMeasurable,
    ← eLpNorm_one_eq_lintegral_enorm hf.aestronglyMeasurable]
  exact ENNReal.toReal_mono hf.ne (eLpNorm_le_eLpNorm_of_exponent_le (by norm_num))

/-- Set integration is a bounded functional on L³ of a probability measure. -/
def L3SetIntegral (mu : Measure X) [IsProbabilityMeasure mu]
    (s : Set X) : Lp ℝ 3 mu →L[ℝ] ℝ := by
  let L : Lp ℝ 3 mu →ₗ[ℝ] ℝ :=
    { toFun := fun F => ∫ x in s, F x ∂mu
      map_add' := by
        intro F G
        calc
          (∫ x in s, (F + G) x ∂mu) = ∫ x in s, F x + G x ∂mu :=
            integral_congr_ae (Lp.coeFn_add F G).restrict
          _ = (∫ x in s, F x ∂mu) + ∫ x in s, G x ∂mu :=
            integral_add ((Lp.memLp F).integrable (by norm_num)).restrict
              ((Lp.memLp G).integrable (by norm_num)).restrict
      map_smul' := by
        intro c F
        change (∫ x in s, (c • F) x ∂mu) = c * ∫ x in s, F x ∂mu
        calc
          _ = ∫ x in s, c • F x ∂mu := integral_congr_ae (Lp.coeFn_smul c F).restrict
          _ = _ := by simp only [smul_eq_mul, integral_const_mul] }
  refine L.mkContinuous 1 (fun F => ?_)
  change ‖∫ x in s, F x ∂mu‖ ≤ 1 * ‖F‖
  rw [one_mul, Lp.norm_def]
  calc
    _ ≤ ∫ x in s, ‖F x‖ ∂mu := norm_integral_le_integral_norm _
    _ ≤ ∫ x, ‖F x‖ ∂mu :=
      setIntegral_le_integral ((Lp.memLp F).integrable (by norm_num)).norm
        (ae_of_all _ fun x => norm_nonneg _)
    _ ≤ _ := L3_integral_norm_le mu F (Lp.memLp F)

@[simp] theorem L3SetIntegral_apply (mu : Measure X) [IsProbabilityMeasure mu]
    (s : Set X) (F : Lp ℝ 3 mu) :
    L3SetIntegral mu s F = ∫ x in s, F x ∂mu := rfl

/-- A jointly measurable scalar representative of an integrable L³ family
is integrable on the product, and its scalar integral represents the
Bochner integral. Almost-everywhere correctness in the parameter is enough
for this theorem; applications retain the stronger every-parameter identity. -/
theorem L3_integral_representative (mu : Measure X) [IsProbabilityMeasure mu]
    (nu : Measure A) [SFinite nu]
    (G : A → Lp ℝ 3 mu) (hG : Integrable G nu)
    (g : A × X → ℝ) (hgm : AEStronglyMeasurable g (nu.prod mu))
    (hrep : ∀ᵐ a ∂nu, (fun x => g (a, x)) =ᵐ[mu] (G a : X → ℝ)) :
    Integrable g (nu.prod mu) ∧
      (fun x => ∫ a, g (a, x) ∂nu) =ᵐ[mu]
        ((∫ a, G a ∂nu : Lp ℝ 3 mu) : X → ℝ) := by
  have hsection : ∀ᵐ a ∂nu, MemLp (fun x => g (a, x)) 3 mu := by
    filter_upwards [hrep] with a ha
    exact (memLp_congr_ae ha).2 (Lp.memLp (G a))
  have hnorm : ∀ᵐ a ∂nu, (∫ x, ‖g (a, x)‖ ∂mu) ≤ ‖G a‖ := by
    filter_upwards [hrep, hsection] with a ha hm
    calc
      _ ≤ (eLpNorm (fun x => g (a, x)) 3 mu).toReal := L3_integral_norm_le mu _ hm
      _ = ‖G a‖ := by rw [eLpNorm_congr_ae ha, Lp.norm_def]
  have hnormint : Integrable (fun a => ∫ x, ‖g (a, x)‖ ∂mu) nu := by
    apply hG.norm.mono' hgm.norm.integral_prod_right'
    filter_upwards [hnorm] with a ha
    have hnonneg : (0 : ℝ) ≤ ∫ x : X, ‖g (a, x)‖ ∂mu :=
      integral_nonneg (fun x => norm_nonneg (g (a, x)))
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact ha
  have hprod : Integrable g (nu.prod mu) :=
    (integrable_prod_iff hgm).2 ⟨hsection.mono (fun a ha => ha.integrable (by norm_num)), hnormint⟩
  refine ⟨hprod, Integrable.ae_eq_of_forall_setIntegral_eq _ _
    hprod.integral_prod_right
    ((Lp.memLp (∫ a, G a ∂nu : Lp ℝ 3 mu)).integrable (by norm_num)) ?_⟩
  intro s hs hsfin
  have hprodS : Integrable g (nu.prod (mu.restrict s)) :=
    hprod.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  calc
    (∫ x in s, ∫ a, g (a, x) ∂nu ∂mu) =
        ∫ a, ∫ x in s, g (a, x) ∂mu ∂nu :=
      (integral_integral_swap (f := fun a x => g (a, x)) hprodS).symm
    _ = ∫ a, L3SetIntegral mu s (G a) ∂nu := by
      apply integral_congr_ae
      filter_upwards [hrep] with a ha
      exact integral_congr_ae ha.restrict
    _ = L3SetIntegral mu s (∫ a, G a ∂nu) :=
      (L3SetIntegral mu s).integral_comp_comm hG
    _ = _ := rfl

end HRS.MS.ProClosureS111

#print axioms HRS.MS.ProClosureS111.L3_integral_representative
