import HRS.MS.Fp81S21BV05
import HRS.MS.Fp81S21RSValue4

/-! Domination of finite right-endpoint Stieltjes sums by variation. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace HRS.Fp81.S21

/-- Every monotone finite partition is controlled by the total variation. -/
theorem fp81s21_rs_sum_le_variation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H B : ℝ) (hB : 0 ≤ B) (A : ℝ → E →L[ℝ] ℝ) (F : ℝ → E)
    (hA : ∀ t ∈ Icc 0 H, ‖A t‖ ≤ B)
    (hF : BoundedVariationOn F (Icc 0 H))
    (N : ℕ) (t : ℕ → ℝ)
    (ht : ∀ i ≤ N, t i ∈ Icc 0 H)
    (htmono : ∀ i, i < N → t i ≤ t (i + 1)) :
    ‖∑ i ∈ Finset.range N, A (t (i + 1)) (F (t (i + 1)) - F (t i))‖ ≤
      B * (eVariationOn F (Icc 0 H)).toReal := by
  have hm : MonotoneOn t (Iic N) := by
    apply monotoneOn_of_le_succ (ordConnected_Iic)
    intro i _ hi hi'
    exact htmono i (by simpa using hi')
  have hv := eVariationOn.sum_le_of_monotoneOn_Iic (f := F) hm ht
  have hv' : (∑ i ∈ Finset.range N, ‖F (t (i + 1)) - F (t i)‖) ≤
      (eVariationOn F (Icc 0 H)).toReal := by
    have h := ENNReal.toReal_mono hF hv
    rw [ENNReal.toReal_sum (fun i hi => edist_ne_top _ _)] at h
    simpa only [edist_dist, dist_eq_norm, ENNReal.toReal_ofReal (norm_nonneg _)] using h
  calc
    _ ≤ ∑ i ∈ Finset.range N, ‖A (t (i + 1)) (F (t (i + 1)) - F (t i))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range N, B * ‖F (t (i + 1)) - F (t i)‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact ((A (t (i + 1))).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hA _ (ht _ (by have := Finset.mem_range.mp hi; omega)))
          (norm_nonneg _))
    _ = B * (∑ i ∈ Finset.range N, ‖F (t (i + 1)) - F (t i)‖) := by rw [Finset.mul_sum]
    _ ≤ B * (eVariationOn F (Icc 0 H)).toReal := mul_le_mul_of_nonneg_left hv' hB

/-- An integrable transported BV path dominates every finite partition sum. -/
theorem fp81s21_rs_sum_transport_domination
    {Ω E U : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    (P : Measure Ω) (H : ℝ) (hH : 0 ≤ H) (B : ℝ) (hB : 0 ≤ B)
    (X : Ω → U) (hX : Integrable X P)
    (L : U →L[ℝ] fp81s21_BV0 (E := E) hH)
    (A : Ω → ℝ → E →L[ℝ] ℝ) (F : Ω → ℝ → E)
    (hFL : ∀ᵐ ω ∂P, ∀ t ∈ Icc 0 H,
      F ω t = fp81s21_bvExt hH (L (X ω)) t)
    (hAb : ∀ ω t, ‖A ω t‖ ≤ B)
    (N : ℕ → ℕ) (t : ℕ → ℕ → ℝ)
    (ht0 : ∀ n, t n 0 = 0) (htN : ∀ n, t n (N n) = H)
    (htmono : ∀ n i, i < N n → t n i ≤ t n (i + 1)) :
    Integrable (fun ω => B * ‖L‖ * ‖X ω‖) P ∧
      ∀ n, ∀ᵐ ω ∂P,
        ‖∑ i ∈ Finset.range (N n),
          A ω (t n (i + 1)) (F ω (t n (i + 1)) - F ω (t n i))‖ ≤
          B * ‖L‖ * ‖X ω‖ := by
  refine ⟨hX.norm.const_mul (B * ‖L‖), ?_⟩
  intro n
  have hm : MonotoneOn (t n) (Iic (N n)) := by
    apply monotoneOn_of_le_succ ordConnected_Iic
    intro i _ hi hi'
    exact htmono n i (by simpa using hi')
  have ht : ∀ i ≤ N n, t n i ∈ Icc 0 H := by
    intro i hi
    constructor
    · simpa [ht0 n] using hm (show 0 ∈ Iic (N n) from Nat.zero_le _) hi (Nat.zero_le i)
    · simpa [htN n] using hm hi (show N n ∈ Iic (N n) from by simp) hi
  filter_upwards [hFL] with ω hω
  have hvar : eVariationOn (F ω) (Icc 0 H) =
      eVariationOn (fp81s21_bvExt hH (L (X ω))) (Icc 0 H) :=
    eVariationOn.congr hω
  have hBV : BoundedVariationOn (F ω) (Icc 0 H) := by
    change eVariationOn (F ω) (Icc 0 H) ≠ ⊤
    rw [hvar]
    exact fp81s21_bvExt_bv hH (L (X ω))
  calc
    _ ≤ B * (eVariationOn (F ω) (Icc 0 H)).toReal :=
      fp81s21_rs_sum_le_variation H B hB (A ω) (F ω)
        (fun t _ => hAb ω t) hBV (N n) (t n) ht (htmono n)
    _ = B * ‖L (X ω)‖ := by rw [hvar]; rfl
    _ ≤ B * (‖L‖ * ‖X ω‖) := mul_le_mul_of_nonneg_left (L.le_opNorm _) hB
    _ = B * ‖L‖ * ‖X ω‖ := by ring

#print axioms fp81s21_rs_sum_le_variation
#print axioms fp81s21_rs_sum_transport_domination
end HRS.Fp81.S21
end
