import HRS.MS.GapRevAux1

/-!
# S81R, packet R2: the test class `s81r_S` (bounded `C²` functions with bounded derivatives up to order 2)

* closed under products (`s81r_S_mul`), contains constants, preserved by the Pois semigroup `sg` (`s81r_S_sg`);
* `cos ∘ ℓ`, `sin ∘ ℓ` for a continuous linear form `ℓ` belong to it (`s81r_S_cos`, `s81r_S_sin`).
-/

noncomputable section

open MeasureTheory
open scoped ContDiff NNReal
open HRS HRS.MS.Gap HRS.MS.PoisSg

namespace HRS.MS.S81R

variable {d : ℕ}

/-- bounded `C²` functions with all derivatives of order `≤ 2` bounded -/
def s81r_S (f : Euc d → ℝ) : Prop := ∃ M : ℝ, gap234_Sm M f

theorem s81r_S_one : s81r_S (fun _ : Euc d => (1 : ℝ)) := by
  refine ⟨1, contDiff_const, fun i hi y => ?_⟩
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · simp
  · rw [iteratedFDeriv_const_of_ne hpos.ne']
    simp

theorem s81r_S_mul {f g : Euc d → ℝ} (hf : s81r_S f) (hg : s81r_S g) :
    s81r_S (fun x => f x * g x) := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨M', hM'⟩ := hg
  have h0 := gap234_sm_nonneg hM
  have h0' := gap234_sm_nonneg hM'
  refine ⟨4 * (M * M'), hM.1.mul hM'.1, fun i hi y => ?_⟩
  refine (norm_iteratedFDeriv_mul_le hM.1 hM'.1 y (by exact_mod_cast hi)).trans ?_
  have hb : ∀ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j f y‖ *
      ‖iteratedFDeriv ℝ (i - j) g y‖ ≤ (i.choose j : ℝ) * (M * M') := by
    intro j hj
    have hj' : j ≤ 2 := by have := Finset.mem_range.1 hj; omega
    have hij : i - j ≤ 2 := by omega
    have e1 := hM.2 j hj' y
    have e2 := hM'.2 (i - j) hij y
    have e3 : ‖iteratedFDeriv ℝ j f y‖ * ‖iteratedFDeriv ℝ (i - j) g y‖ ≤ M * M' :=
      mul_le_mul e1 e2 (norm_nonneg _) h0
    calc (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j f y‖ * ‖iteratedFDeriv ℝ (i - j) g y‖
        = (i.choose j : ℝ) * (‖iteratedFDeriv ℝ j f y‖ * ‖iteratedFDeriv ℝ (i - j) g y‖) := by ring
      _ ≤ (i.choose j : ℝ) * (M * M') := mul_le_mul_of_nonneg_left e3 (Nat.cast_nonneg _)
  refine (Finset.sum_le_sum hb).trans ?_
  rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
  have h2 : (2 : ℝ) ^ i ≤ 4 := by interval_cases i <;> norm_num
  push_cast
  nlinarith [mul_nonneg h0 h0']

theorem s81r_S_sg {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ mΩ}
    {W : ℝ≥0 → Ω → Fin d → ℝ} [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    {q Mb : ℝ} (hq : 0 < q) {B : Euc d → Euc d} (hB : Whole.HasCbBound 2 Mb B) {t : ℝ} (ht : 0 ≤ t)
    {f : Euc d → ℝ} (hf : s81r_S f) : s81r_S (sg P W q B t f) := by
  obtain ⟨M, hM⟩ := hf
  obtain ⟨C, -, hC⟩ := gap234_sg_sm hW hq hB ht
  exact ⟨C * M, hC hM t ⟨ht, le_rfl⟩⟩

theorem s81r_S_cont {f : Euc d → ℝ} (hf : s81r_S f) : Continuous f :=
  (hf.choose_spec.1).continuous

theorem s81r_S_bdd {f : Euc d → ℝ} (hf : s81r_S f) : ∃ M : ℝ, ∀ y, |f y| ≤ M := by
  obtain ⟨M, hM⟩ := hf
  exact ⟨M, fun y => by simpa using gap234_sm_zero hM y⟩

/-- trigonometric functions composed with a linear form -/
theorem s81r_S_trig {f : ℝ → ℝ} (hc : ContDiff ℝ 2 f) (hf : ∀ n x, |iteratedDeriv n f x| ≤ 1)
    (ℓ : Euc d →L[ℝ] ℝ) : s81r_S (fun x => f (ℓ x)) := by
  have hbd : ∀ i : ℕ, i ≤ 2 → ∀ x : Euc d, ‖iteratedFDeriv ℝ i (fun x => f (ℓ x)) x‖ ≤ ‖ℓ‖ ^ i := by
    intro i hi x
    have e := ℓ.iteratedFDeriv_comp_right hc x (i := i) (by exact_mod_cast hi)
    have e' : (fun x => f (ℓ x)) = f ∘ ℓ := rfl
    rw [e', e]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have h1 : ‖iteratedFDeriv ℝ i f (ℓ x)‖ ≤ 1 := by
      rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
      simpa using hf i (ℓ x)
    calc ‖iteratedFDeriv ℝ i f (ℓ x)‖ * ‖ℓ‖ ^ i ≤ 1 * ‖ℓ‖ ^ i :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = ‖ℓ‖ ^ i := one_mul _
  refine ⟨1 + ‖ℓ‖ + ‖ℓ‖ ^ 2, hc.comp ℓ.contDiff, fun i hi x => ?_⟩
  refine (hbd i hi x).trans ?_
  have h0 : 0 ≤ ‖ℓ‖ := norm_nonneg _
  interval_cases i <;> simp <;> nlinarith [sq_nonneg ‖ℓ‖]

theorem s81r_S_cos (ℓ : Euc d →L[ℝ] ℝ) : s81r_S (fun x => Real.cos (ℓ x)) :=
  s81r_S_trig Real.contDiff_cos Real.abs_iteratedDeriv_cos_le_one ℓ

theorem s81r_S_sin (ℓ : Euc d →L[ℝ] ℝ) : s81r_S (fun x => Real.sin (ℓ x)) :=
  s81r_S_trig Real.contDiff_sin Real.abs_iteratedDeriv_sin_le_one ℓ

end HRS.MS.S81R
