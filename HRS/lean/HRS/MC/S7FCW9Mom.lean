import HRS.MC.S7FCW9Lem

/-!
# S7FCW9Mom: moment bounds for the proof of `s7_FC_C4_field_all_t` (FC-C4)

* `S7FCW9_jensen_fin`: finite weighted power-mean inequality `(∑ aᵢ zᵢ)^m ≤ A^(m-1) ∑ aᵢ zᵢ^m`.
* `S7FCW9_lint_jensen`: the same inequality integrated, with the `L^{2m}` moment bounds of the Wick
  coordinates as input; output an `L^m`-bound of the weighted sum of squares, uniform in the cube.
* `S7FCW9_lint_of_chaos`: from the `L^p` bound of `HRS.MC.QRSpec.Chaos` (finite-section form with `F = ∅`)
  to a lintegral bound.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7FCW9

open HRS HRS.Sec7 HRS.MC.QRSpec

variable {d : ℕ}

theorem S7FCW9_tailHS_nonneg {ι : Type*} (A : ι → ι → ℝ) (F : Finset ι) : 0 ≤ tailHS A F := by
  unfold tailHS
  refine tsum_nonneg fun p => ?_
  split_ifs
  · exact le_refl 0
  · exact sq_nonneg _

theorem S7FCW9_jensen_fin {ι : Type*} (S : Finset ι) (a z : ι → ℝ) (A m : ℝ)
    (ha : ∀ i ∈ S, 0 ≤ a i) (hz : ∀ i ∈ S, 0 ≤ z i) (hA : ∑ i ∈ S, a i ≤ A) (hm : 1 ≤ m) :
    (∑ i ∈ S, a i * z i) ^ m ≤ A ^ (m - 1) * ∑ i ∈ S, a i * z i ^ m := by
  have hsnn : 0 ≤ ∑ i ∈ S, a i := Finset.sum_nonneg ha
  have hA0 : 0 ≤ A := hsnn.trans hA
  have hzsum : 0 ≤ ∑ i ∈ S, a i * z i ^ m :=
    Finset.sum_nonneg fun i hi => mul_nonneg (ha i hi) (Real.rpow_nonneg (hz i hi) _)
  rcases hsnn.eq_or_lt with hs0 | hspos
  · have hzero : ∀ i ∈ S, a i = 0 := (Finset.sum_eq_zero_iff_of_nonneg ha).1 hs0.symm
    have h0 : ∑ i ∈ S, a i * z i = 0 :=
      Finset.sum_eq_zero fun i hi => by rw [hzero i hi, zero_mul]
    rw [h0, Real.zero_rpow (by linarith)]
    exact mul_nonneg (Real.rpow_nonneg hA0 _) hzsum
  · set s := ∑ i ∈ S, a i with hs
    have hw : ∀ i ∈ S, 0 ≤ a i / s := fun i hi => div_nonneg (ha i hi) hspos.le
    have hw1 : ∑ i ∈ S, a i / s = 1 := by
      rw [← Finset.sum_div]
      exact div_self hspos.ne'
    have hX : ∑ i ∈ S, a i * z i = s * ∑ i ∈ S, a i / s * z i := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    have hJ : (∑ i ∈ S, a i / s * z i) ^ m ≤ ∑ i ∈ S, a i / s * z i ^ m :=
      Real.rpow_arith_mean_le_arith_mean_rpow S (fun i => a i / s) z hw hw1 (fun i hi => hz i hi) hm
    have hXnn : 0 ≤ ∑ i ∈ S, a i / s * z i :=
      Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (hz i hi)
    have hsm : s ^ m = s ^ (m - 1) * s := by
      rw [Real.rpow_sub_one hspos.ne']
      field_simp
    have e2 : s ^ m * ∑ i ∈ S, a i / s * z i ^ m = s ^ (m - 1) * ∑ i ∈ S, a i * z i ^ m := by
      rw [hsm, mul_assoc]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      field_simp
    have hsA : s ^ (m - 1) ≤ A ^ (m - 1) := Real.rpow_le_rpow hsnn hA (by linarith)
    calc (∑ i ∈ S, a i * z i) ^ m = s ^ m * (∑ i ∈ S, a i / s * z i) ^ m := by
          rw [hX, Real.mul_rpow hsnn hXnn]
      _ ≤ s ^ m * ∑ i ∈ S, a i / s * z i ^ m :=
          mul_le_mul_of_nonneg_left hJ (Real.rpow_nonneg hsnn _)
      _ = s ^ (m - 1) * ∑ i ∈ S, a i * z i ^ m := e2
      _ ≤ A ^ (m - 1) * ∑ i ∈ S, a i * z i ^ m := mul_le_mul_of_nonneg_right hsA hzsum

theorem S7FCW9_lint_jensen {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) {ι : Type*} (S : Finset ι)
    (a σ : ι → ℝ) (f : ι → Ω → ℝ) (A Dm m : ℝ)
    (hf : ∀ i, Measurable (f i)) (ha : ∀ i, 0 ≤ a i) (hσ : ∀ i, 0 < σ i)
    (hA : ∑ i ∈ S, a i ≤ A) (hA0 : 0 < A) (hm : 1 ≤ m) (hDm : 0 ≤ Dm)
    (hmom : ∀ i ∈ S, ∫⁻ ω, ENNReal.ofReal (|f i ω| ^ (2 * m)) ∂P ≤ ENNReal.ofReal (σ i ^ m * Dm)) :
    ∫⁻ ω, ENNReal.ofReal ((∑ i ∈ S, a i * (f i ω ^ 2 / σ i)) ^ m) ∂P ≤
      ENNReal.ofReal (A ^ m * Dm) := by
  have hAm1 : 0 ≤ A ^ (m - 1) := Real.rpow_nonneg hA0.le _
  have hcoef : ∀ i, 0 ≤ a i / σ i ^ m := fun i =>
    div_nonneg (ha i) (Real.rpow_nonneg (hσ i).le _)
  have hpt : ∀ ω, ENNReal.ofReal ((∑ i ∈ S, a i * (f i ω ^ 2 / σ i)) ^ m) ≤
      ∑ i ∈ S, ENNReal.ofReal (A ^ (m - 1) * (a i / σ i ^ m)) * ENNReal.ofReal (|f i ω| ^ (2 * m)) := by
    intro ω
    have hz : ∀ i ∈ S, 0 ≤ f i ω ^ 2 / σ i := fun i _ => div_nonneg (sq_nonneg _) (hσ i).le
    have J := S7FCW9_jensen_fin S a (fun i => f i ω ^ 2 / σ i) A m (fun i _ => ha i) hz hA hm
    beta_reduce at J
    have e : ∀ i ∈ S, a i * (f i ω ^ 2 / σ i) ^ m = (a i / σ i ^ m) * |f i ω| ^ (2 * m) := by
      intro i _
      rw [Real.div_rpow (sq_nonneg _) (hσ i).le, S7FCW9_sq_rpow]
      ring
    rw [Finset.sum_congr rfl e] at J
    have hnn : ∀ i ∈ S, 0 ≤ A ^ (m - 1) * ((a i / σ i ^ m) * |f i ω| ^ (2 * m)) := fun i _ =>
      mul_nonneg hAm1 (mul_nonneg (hcoef i) (Real.rpow_nonneg (abs_nonneg _) _))
    calc ENNReal.ofReal ((∑ i ∈ S, a i * (f i ω ^ 2 / σ i)) ^ m)
        ≤ ENNReal.ofReal (A ^ (m - 1) * ∑ i ∈ S, (a i / σ i ^ m) * |f i ω| ^ (2 * m)) :=
          ENNReal.ofReal_le_ofReal J
      _ = ENNReal.ofReal (∑ i ∈ S, A ^ (m - 1) * ((a i / σ i ^ m) * |f i ω| ^ (2 * m))) := by
          rw [Finset.mul_sum]
      _ = ∑ i ∈ S, ENNReal.ofReal (A ^ (m - 1) * ((a i / σ i ^ m) * |f i ω| ^ (2 * m))) :=
          ENNReal.ofReal_sum_of_nonneg hnn
      _ = ∑ i ∈ S, ENNReal.ofReal (A ^ (m - 1) * (a i / σ i ^ m)) *
            ENNReal.ofReal (|f i ω| ^ (2 * m)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← mul_assoc, ENNReal.ofReal_mul (mul_nonneg hAm1 (hcoef i))]
  have hmeas : ∀ i, Measurable fun ω => ENNReal.ofReal (|f i ω| ^ (2 * m)) := fun i =>
    ENNReal.measurable_ofReal.comp ((continuous_abs.measurable.comp (hf i)).pow_const _)
  calc ∫⁻ ω, ENNReal.ofReal ((∑ i ∈ S, a i * (f i ω ^ 2 / σ i)) ^ m) ∂P
      ≤ ∫⁻ ω, ∑ i ∈ S, ENNReal.ofReal (A ^ (m - 1) * (a i / σ i ^ m)) *
          ENNReal.ofReal (|f i ω| ^ (2 * m)) ∂P := lintegral_mono hpt
    _ = ∑ i ∈ S, ENNReal.ofReal (A ^ (m - 1) * (a i / σ i ^ m)) *
          ∫⁻ ω, ENNReal.ofReal (|f i ω| ^ (2 * m)) ∂P := by
          rw [lintegral_finset_sum' S fun i _ =>
            ((hmeas i).const_mul (ENNReal.ofReal (A ^ (m - 1) * (a i / σ i ^ m)))).aemeasurable]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [lintegral_const_mul _ (hmeas i)]
    _ ≤ ∑ i ∈ S, ENNReal.ofReal (A ^ (m - 1) * (a i / σ i ^ m)) *
          ENNReal.ofReal (σ i ^ m * Dm) := by
          refine Finset.sum_le_sum fun i hi => ?_
          exact mul_le_mul_of_nonneg_left (hmom i hi) zero_le'
    _ = ∑ i ∈ S, ENNReal.ofReal (A ^ (m - 1) * a i * Dm) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← ENNReal.ofReal_mul (mul_nonneg hAm1 (hcoef i))]
          congr 1
          have : σ i ^ m ≠ 0 := (Real.rpow_pos_of_pos (hσ i) _).ne'
          field_simp
    _ = ENNReal.ofReal (∑ i ∈ S, A ^ (m - 1) * a i * Dm) := by
          rw [ENNReal.ofReal_sum_of_nonneg]
          intro i _
          exact mul_nonneg (mul_nonneg hAm1 (ha i)) hDm
    _ ≤ ENNReal.ofReal (A ^ m * Dm) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hsum : ∑ i ∈ S, A ^ (m - 1) * a i * Dm = A ^ (m - 1) * Dm * ∑ i ∈ S, a i := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by ring
          rw [hsum]
          have hAm : A ^ (m - 1) * A = A ^ m := by
            rw [Real.rpow_sub_one hA0.ne']
            field_simp
          have hD : 0 ≤ A ^ (m - 1) * Dm := mul_nonneg hAm1 hDm
          calc A ^ (m - 1) * Dm * ∑ i ∈ S, a i ≤ A ^ (m - 1) * Dm * A :=
                mul_le_mul_of_nonneg_left hA hD
            _ = A ^ m * Dm := by rw [← hAm]; ring

theorem S7FCW9_lint_of_chaos {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (p Cp K T : ℝ) (hp : 2 ≤ p) (hK : 0 ≤ K) (hC0 : 0 ≤ Cp)
    (hT : 0 ≤ T) (h : eLpNorm f (ENNReal.ofReal p) P ≤ ENNReal.ofReal (Cp * K * Real.sqrt T)) :
    ∫⁻ ω, ENNReal.ofReal (|f ω| ^ p) ∂P ≤ ENNReal.ofReal ((Cp * K) ^ p * T ^ (p / 2)) := by
  have hp0 : 0 < p := by linarith
  have hX : 0 ≤ Cp * K * Real.sqrt T := mul_nonneg (mul_nonneg hC0 hK) (Real.sqrt_nonneg _)
  have hA : ∫⁻ ω, ENNReal.ofReal (|f ω| ^ p) ∂P ≤ ENNReal.ofReal ((Cp * K * Real.sqrt T) ^ p) := by
    have hp0' : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.2 hp0).ne'
    have hpt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
    have hfm : AEStronglyMeasurable f P :=
      aestronglyMeasurable_of_eLpNorm_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top h)
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0' hpt hfm, ENNReal.toReal_ofReal hp0.le] at h
    have h2 : ∫⁻ ω, ‖f ω‖ₑ ^ p ∂P ≤ (ENNReal.ofReal (Cp * K * Real.sqrt T)) ^ p := by
      have := ENNReal.rpow_le_rpow h hp0.le
      rwa [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp0.ne', ENNReal.rpow_one] at this
    calc ∫⁻ ω, ENNReal.ofReal (|f ω| ^ p) ∂P = ∫⁻ ω, ‖f ω‖ₑ ^ p ∂P := by
          refine lintegral_congr fun ω => ?_
          rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp0.le]
      _ ≤ (ENNReal.ofReal (Cp * K * Real.sqrt T)) ^ p := h2
      _ = ENNReal.ofReal ((Cp * K * Real.sqrt T) ^ p) :=
          (ENNReal.ofReal_rpow_of_nonneg hX hp0.le)
  refine hA.trans (ENNReal.ofReal_le_ofReal (le_of_eq ?_))
  rw [Real.mul_rpow (mul_nonneg hC0 hK) (Real.sqrt_nonneg _), Real.sqrt_eq_rpow,
    ← Real.rpow_mul hT]
  congr 2
  ring

end HRS.MC.Sec7.S7FCW9

end
