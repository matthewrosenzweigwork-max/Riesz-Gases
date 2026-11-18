import HRS.MS.SpecAux61
import HRS.Stochastic.Integral

/-!
# S8R: an Itô inequality for `ℓ²`-valued stochastic integrals against a cylindrical Brownian motion (S8.7, packet C6)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  Generic helpers:

* `s8p_itoIntegral_congr`: the Itô integral only sees the integrand on `[0,∞)`;
* `s8p_isProgressive_mul`: product of a progressive process with a measurable function of time;
* `s8p_enorm_sq_eq`, `s8p_seq_enorm_sq`: `‖x‖ₑ² = ofReal (x²)`, and `‖z‖ₑ² = ∑_l ofReal (z_l²)` on `ℓ²`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace HRS.MS.Spec

open HRS HRS.Whole

theorem s8p_itoIntegral_congr {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*} [Fintype ι]
    (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ι → ℝ) {Φ Φ' : ℝ → Ω → ι → ℝ}
    (h : ∀ r, 0 ≤ r → ∀ w k, Φ r w k = Φ' r w k) :
    itoIntegral P ℱ W Φ = itoIntegral P ℱ W Φ' := by
  have hsq : ∀ (Ψ : ℝ → Ω → ι → ℝ) (t : ℝ), 0 ≤ t →
      sqIntegralOn P (fun s ω => Ψ s ω - Φ s ω) t = sqIntegralOn P (fun s ω => Ψ s ω - Φ' s ω) t := by
    intro Ψ t ht
    unfold sqIntegralOn
    refine lintegral_congr fun ω => ?_
    refine setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Pi.sub_apply, h s hs.1 ω k]
  have hP : IsItoIntegral P ℱ W Φ = IsItoIntegral P ℱ W Φ' := by
    funext M
    apply propext
    constructor
    · intro hM
      refine ⟨hM.cont, hM.adapted, hM.zero, fun t ht Ψ hΨ => hM.approx t ht Ψ ?_⟩
      have e : (fun n => sqIntegralOn P (fun s ω => (Ψ n).toFun s ω - Φ s ω) t) =
          fun n => sqIntegralOn P (fun s ω => (Ψ n).toFun s ω - Φ' s ω) t :=
        funext fun n => hsq (Ψ n).toFun t ht
      rw [e]; exact hΨ
    · intro hM
      refine ⟨hM.cont, hM.adapted, hM.zero, fun t ht Ψ hΨ => hM.approx t ht Ψ ?_⟩
      have e : (fun n => sqIntegralOn P (fun s ω => (Ψ n).toFun s ω - Φ s ω) t) =
          fun n => sqIntegralOn P (fun s ω => (Ψ n).toFun s ω - Φ' s ω) t :=
        funext fun n => hsq (Ψ n).toFun t ht
      rw [← e]; exact hΨ
  unfold itoIntegral
  rw [hP]

theorem s8p_isProgressive_mul {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ mΩ}
    {f : ℝ → Ω → ℝ} (hf : IsProgressive ℱ f) {g : ℝ → ℝ} (hg : Measurable g) :
    IsProgressive ℱ (fun r w => g r * f r w) := by
  intro i
  have h1 : Measurable[Subtype.instMeasurableSpace.prod (ℱ i)] fun p : Set.Iic i × Ω => g (p.1 : ℝ) :=
    hg.comp (measurable_subtype_coe.comp (@measurable_fst _ _ Subtype.instMeasurableSpace (ℱ i)))
  exact h1.mul (hf i)

theorem s8p_enorm_sq_eq (x : ℝ) : ‖x‖ₑ ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), Real.norm_eq_abs, sq_abs]

theorem s8p_seq_enorm_sq (z : SeqL2) :
    ‖z‖ₑ ^ 2 = ∑' l, ENNReal.ofReal (SeqL2.coord z l ^ 2) := by
  rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _), ← u11_norm_sq z,
    ENNReal.ofReal_tsum_of_nonneg (fun l => sq_nonneg _) (u11_coord_summable z)]

end HRS.MS.Spec
