import HRS.Whole.AppendixAAdjoint
import Mathlib.Analysis.InnerProductSpace.NormPow

/-!
# S.A.16 T1, part 1: pointwise calculus of `v ↦ ‖v‖^p` in an inner product space (`p ≥ 2`)

With `g(v) = ‖v‖^{p-2} v` (so `D‖·‖^p (v) = p ⟪g v, ·⟫`):
* `sa16v_g_lip`: `‖g u - g w‖ ≤ (p-1) (‖u‖+‖w‖)^{p-2} ‖u - w‖`;
* `sa16v_tangent_lower/upper`: `p⟪g a, b⟫ ≤ ‖a+b‖^p - ‖a‖^p ≤ p⟪g (a+b), b⟫` (convexity).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.Whole.AppendixA.Phase2SA16V

section Pointwise
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- `g(v) = ‖v‖^r v` -/
def sa16v_g (r : ℝ) (v : V) : V := ‖v‖ ^ r • v

lemma sa16v_alg (r a b : ℝ) (hr : 0 ≤ r) (hb : 0 ≤ b) (hba : b ≤ a) :
    (a ^ r - b ^ r) * b ≤ r * a ^ r * (a - b) := by
  rcases eq_or_lt_of_le hb with rfl | hbpos
  · simp only [mul_zero]
    have : 0 ≤ a := hba
    have h1 : 0 ≤ a ^ r := Real.rpow_nonneg this r
    positivity
  have hapos : 0 < a := lt_of_lt_of_le hbpos hba
  have hbr : 0 < b ^ r := Real.rpow_pos_of_pos hbpos r
  have har : 0 < a ^ r := Real.rpow_pos_of_pos hapos r
  have hmono : b ^ r ≤ a ^ r := Real.rpow_le_rpow hb hba hr
  rcases le_total r 1 with hr1 | hr1
  · -- concave case
    have hs : (-1 : ℝ) ≤ (a - b) / b := by
      have : 0 ≤ (a - b) / b := div_nonneg (by linarith) hb
      linarith
    have h := rpow_one_add_le_one_add_mul_self hs hr hr1
    have e : 1 + (a - b) / b = a / b := by field_simp; ring
    rw [e, Real.div_rpow hapos.le hb] at h
    rw [div_le_iff₀ hbr] at h
    have h2 : a ^ r ≤ (1 + r * ((a - b) / b)) * b ^ r := h
    have h3 : (a ^ r - b ^ r) * b ≤ r * (a - b) * b ^ r := by
      have : (a ^ r - b ^ r) ≤ r * ((a - b) / b) * b ^ r := by nlinarith [h2]
      calc (a ^ r - b ^ r) * b ≤ (r * ((a - b) / b) * b ^ r) * b :=
            mul_le_mul_of_nonneg_right this hb
        _ = r * (a - b) * b ^ r := by field_simp
    calc (a ^ r - b ^ r) * b ≤ r * (a - b) * b ^ r := h3
      _ ≤ r * (a - b) * a ^ r :=
          mul_le_mul_of_nonneg_left hmono (mul_nonneg hr (by linarith))
      _ = r * a ^ r * (a - b) := by ring
  · -- convex case
    have hs : (-1 : ℝ) ≤ (b - a) / a := by
      rw [le_div_iff₀ hapos]; linarith
    have h := one_add_mul_self_le_rpow_one_add hs hr1
    have e : 1 + (b - a) / a = b / a := by field_simp; ring
    rw [e, Real.div_rpow hb hapos.le] at h
    rw [le_div_iff₀ har] at h
    have h4 : (1 + r * ((b - a) / a)) * a ^ r ≤ b ^ r := h
    have h5 : a ^ r - b ^ r ≤ r * ((a - b) / a) * a ^ r := by
      have : (1 + r * ((b - a) / a)) * a ^ r = a ^ r - r * ((a - b) / a) * a ^ r := by
        have : (b - a) / a = -((a - b) / a) := by ring
        rw [this]; ring
      linarith
    have h6 : (a ^ r - b ^ r) * b ≤ (r * ((a - b) / a) * a ^ r) * b := mul_le_mul_of_nonneg_right h5 hb
    have h7 : (r * ((a - b) / a) * a ^ r) * b ≤ (r * ((a - b) / a) * a ^ r) * a :=
      mul_le_mul_of_nonneg_left hba (by
        have : 0 ≤ (a - b) / a := div_nonneg (by linarith) hapos.le
        positivity)
    calc (a ^ r - b ^ r) * b ≤ (r * ((a - b) / a) * a ^ r) * a := h6.trans h7
      _ = r * a ^ r * (a - b) := by field_simp

lemma sa16v_g_lip (r : ℝ) (hr : 0 ≤ r) (u w : V) :
    ‖sa16v_g r u - sa16v_g r w‖ ≤ (1 + r) * (‖u‖ + ‖w‖) ^ r * ‖u - w‖ := by
  wlog hwu : ‖w‖ ≤ ‖u‖ generalizing u w
  · have h := this w u (le_of_not_ge hwu)
    rw [norm_sub_rev (sa16v_g r u), norm_sub_rev u, add_comm ‖u‖]
    exact h
  have hsum : ‖u‖ ^ r ≤ (‖u‖ + ‖w‖) ^ r :=
    Real.rpow_le_rpow (norm_nonneg _) (by linarith [norm_nonneg w]) hr
  have e : sa16v_g r u - sa16v_g r w = ‖u‖ ^ r • (u - w) + (‖u‖ ^ r - ‖w‖ ^ r) • w := by
    unfold sa16v_g; rw [smul_sub, sub_smul]; abel
  rw [e]
  have h1 : ‖‖u‖ ^ r • (u - w) + (‖u‖ ^ r - ‖w‖ ^ r) • w‖ ≤
      ‖u‖ ^ r * ‖u - w‖ + (‖u‖ ^ r - ‖w‖ ^ r) * ‖w‖ := by
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    · rw [norm_smul, Real.norm_of_nonneg (sub_nonneg.2 (Real.rpow_le_rpow (norm_nonneg _) hwu hr))]
  have h2 := sa16v_alg r ‖u‖ ‖w‖ hr (norm_nonneg _) hwu
  have h3 : ‖u‖ - ‖w‖ ≤ ‖u - w‖ := by
    have := norm_sub_norm_le u w
    exact this
  calc ‖‖u‖ ^ r • (u - w) + (‖u‖ ^ r - ‖w‖ ^ r) • w‖
      ≤ ‖u‖ ^ r * ‖u - w‖ + (‖u‖ ^ r - ‖w‖ ^ r) * ‖w‖ := h1
    _ ≤ ‖u‖ ^ r * ‖u - w‖ + r * ‖u‖ ^ r * (‖u‖ - ‖w‖) := by linarith
    _ ≤ ‖u‖ ^ r * ‖u - w‖ + r * ‖u‖ ^ r * ‖u - w‖ := by
        gcongr
    _ = (1 + r) * ‖u‖ ^ r * ‖u - w‖ := by ring
    _ ≤ (1 + r) * (‖u‖ + ‖w‖) ^ r * ‖u - w‖ := by gcongr

lemma sa16v_inner_g (r : ℝ) (x b : V) : ⟪sa16v_g r x, b⟫ = ‖x‖ ^ r * ⟪x, b⟫ := by
  unfold sa16v_g; rw [real_inner_smul_left]

lemma sa16v_hasDerivAt_line {p : ℝ} (hp : 1 < p) (a b : V) (t : ℝ) :
    HasDerivAt (fun t : ℝ => ‖a + t • b‖ ^ p) (p * ⟪sa16v_g (p - 2) (a + t • b), b⟫) t := by
  have h1 : HasDerivAt (fun t : ℝ => a + t • b) b t := by
    simpa using ((hasDerivAt_id t).smul_const b).const_add a
  have h2 := hasFDerivAt_norm_rpow (a + t • b) hp
  have h3 := h2.comp_hasDerivAt t h1
  have e : ((p * ‖a + t • b‖ ^ (p - 2)) • innerSL ℝ (a + t • b)) b =
      p * ⟪sa16v_g (p - 2) (a + t • b), b⟫ := by
    rw [ContinuousLinearMap.smul_apply, innerSL_apply_apply, sa16v_inner_g, smul_eq_mul, mul_assoc]
  rw [e] at h3
  exact h3

lemma sa16v_convexOn_normpow {p : ℝ} (hp : 1 ≤ p) : ConvexOn ℝ univ (fun v : V => ‖v‖ ^ p) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have hp0 : 0 ≤ p := by linarith
  calc ‖a • x + b • y‖ ^ p ≤ (a * ‖x‖ + b * ‖y‖) ^ p := by
        refine Real.rpow_le_rpow (norm_nonneg _) ?_ hp0
        calc ‖a • x + b • y‖ ≤ ‖a • x‖ + ‖b • y‖ := norm_add_le _ _
          _ = a * ‖x‖ + b * ‖y‖ := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
    _ ≤ a * ‖x‖ ^ p + b * ‖y‖ ^ p :=
        (convexOn_rpow hp).2 (mem_Ici.2 (norm_nonneg x)) (mem_Ici.2 (norm_nonneg y)) ha hb hab

lemma sa16v_convexOn_line {p : ℝ} (hp : 1 ≤ p) (a b : V) :
    ConvexOn ℝ univ (fun t : ℝ => ‖a + t • b‖ ^ p) := by
  refine ⟨convex_univ, fun s _ t _ α β hα hβ hαβ => ?_⟩
  have e : a + (α • s + β • t) • b = α • (a + s • b) + β • (a + t • b) := by
    have : a = (α + β) • a := by rw [hαβ, one_smul]
    conv_lhs => rw [this]
    simp only [smul_eq_mul, add_smul, mul_smul, smul_add]
    abel
  have := (sa16v_convexOn_normpow (V := V) hp).2 (mem_univ (a + s • b)) (mem_univ (a + t • b)) hα hβ hαβ
  show ‖a + (α • s + β • t) • b‖ ^ p ≤ α • ‖a + s • b‖ ^ p + β • ‖a + t • b‖ ^ p
  rw [e]
  simpa using this

lemma sa16v_tangent_lower {p : ℝ} (hp : 1 < p) (a b : V) :
    p * ⟪sa16v_g (p - 2) a, b⟫ ≤ ‖a + b‖ ^ p - ‖a‖ ^ p := by
  have hc := sa16v_convexOn_line hp.le a b
  have h := hc.le_slope_of_hasDerivAt (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ)) zero_lt_one
    (by simpa using sa16v_hasDerivAt_line hp a b 0)
  simpa [slope_def_field] using h

lemma sa16v_tangent_upper {p : ℝ} (hp : 1 < p) (a b : V) :
    ‖a + b‖ ^ p - ‖a‖ ^ p ≤ p * ⟪sa16v_g (p - 2) (a + b), b⟫ := by
  have hc := sa16v_convexOn_line hp.le a b
  have h := hc.slope_le_of_hasDerivAt (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ)) zero_lt_one
    (by simpa using sa16v_hasDerivAt_line hp a b 1)
  simpa [slope_def_field] using h

end Pointwise

end HRS.Whole.AppendixA.Phase2SA16V
