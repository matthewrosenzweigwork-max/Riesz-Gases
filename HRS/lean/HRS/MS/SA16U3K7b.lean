import HRS.MS.SA16U3K7a
import HRS.MS.SA16StrongSL2
import HRS.MS.CzPvAsmAux2

/-!
# S.A.16 K7, part (b): the decomposition for `θ = 1` (worker SA16U3)

For `θ = 1` the commutator kernel `(μ(x)-μ(x-z)) |z|^{-(d+1)}` is not integrable near zero, so the gradient term is
isolated: with `Ktr ε = pvkKtr (pvasmK d i) ε`,
`F x = ∫ kA(x,z) W(x-z) dz + ∑_i ∂_iμ(x) (T_δ^i W - T_1^i W)(x)`, where `kA` is the Taylor remainder kernel on
`δ < |z| ≤ 1` plus the bounded difference kernel on `|z| > 1` (both dominated by an `L^1` kernel independent of `δ`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Cutoff
open HRS HRS.Whole HRS.Whole.AppendixA HRS.CZ.Pv HRS.CZ.Pvk HRS.CZ.PvAsm HRS.CZ.ElemA Phase2SA16

section K7b
variable {d : ℕ}

lemma sa16u3_Ktr_formula {ε : ℝ} (hε : 0 ≤ ε) (i : Fin d) (z : Euc d) :
    pvkKtr (pvasmK d i) ε z = if ε < ‖z‖ then z i / ‖z‖ ^ ((d : ℝ) + 1) else 0 := by
  unfold pvkKtr
  by_cases hz : ε < ‖z‖
  · rw [if_pos hz, if_pos hz]
    have hn : 0 < ‖z‖ := hε.trans_lt hz
    unfold pvasmK pvkOmegaK
    simp only [PiLp.smul_apply, smul_eq_mul]
    rw [Real.rpow_add hn, Real.rpow_one, Real.rpow_natCast]
    field_simp
  · rw [if_neg hz, if_neg hz]

/-- Taylor remainder kernel on `δ < |z| ≤ 1`, difference kernel on `|z| > 1` -/
def sa16u3_kA (d : ℕ) (μ : Euc d → ℝ) (δ : ℝ) (x z : Euc d) : ℝ :=
  if δ < ‖z‖ ∧ ‖z‖ ≤ 1 then elema_R μ x z / ‖z‖ ^ ((d : ℝ) + 1)
  else if 1 < ‖z‖ then (μ x - μ (x - z)) / ‖z‖ ^ ((d : ℝ) + 1) else 0

/-- the integrable majorant, independent of `δ` -/
def sa16u3_m (d : ℕ) (B0 B2 : ℝ) (z : Euc d) : ℝ :=
  B2 / 2 * (closedBall (0 : Euc d) 1).indicator (fun z => ‖z‖ ^ (2 - ((d : ℝ) + 1))) z +
    2 * B0 * {z : Euc d | 1 < ‖z‖}.indicator (fun z => ‖z‖ ^ (-((d : ℝ) + 1))) z

lemma sa16u3_m_nonneg {B0 B2 : ℝ} (hB0 : 0 ≤ B0) (hB2 : 0 ≤ B2) (z : Euc d) :
    0 ≤ sa16u3_m d B0 B2 z := by
  unfold sa16u3_m
  have h1 : 0 ≤ (closedBall (0 : Euc d) 1).indicator (fun z => ‖z‖ ^ (2 - ((d : ℝ) + 1))) z :=
    Set.indicator_nonneg (fun w _ => Real.rpow_nonneg (norm_nonneg _) _) z
  have h2 : 0 ≤ {z : Euc d | 1 < ‖z‖}.indicator (fun z => ‖z‖ ^ (-((d : ℝ) + 1))) z :=
    Set.indicator_nonneg (fun w _ => Real.rpow_nonneg (norm_nonneg _) _) z
  positivity

lemma sa16u3_m_meas (B0 B2 : ℝ) : Measurable (sa16u3_m d B0 B2) := by
  unfold sa16u3_m
  exact (measurable_const.mul ((measurable_norm.pow_const _).indicator measurableSet_closedBall)).add
    (measurable_const.mul ((measurable_norm.pow_const _).indicator
      (measurableSet_lt measurable_const measurable_norm)))

lemma sa16u3_m_int (hd : 1 ≤ d) (B0 B2 : ℝ) : Integrable (sa16u3_m d B0 B2) := by
  obtain ⟨I0, hI0, hI⟩ := sa16s_moment (d := d) hd (θ := 1) (by norm_num)
  have h1 := (hI 1 one_pos).1
  have h2 : Integrable ({z : Euc d | 1 < ‖z‖}.indicator (fun z => ‖z‖ ^ (-((d : ℝ) + 1)))) := by
    rw [integrable_indicator_iff (measurableSet_lt measurable_const measurable_norm)]
    exact pvapi_integrableOn_rpow_outside hd (s := (d : ℝ) + 1) (by linarith) one_pos
  exact (h1.const_mul _).add (h2.const_mul _)

lemma sa16u3_kA_meas {μ : Euc d → ℝ} (hμ : Continuous μ) (δ : ℝ) (x : Euc d) :
    Measurable (sa16u3_kA d μ δ x) := by
  unfold sa16u3_kA elema_R
  have hR : Measurable (fun z : Euc d => μ x - μ (x - z) - fderiv ℝ μ x z) :=
    (measurable_const.sub (hμ.measurable.comp (measurable_const.sub measurable_id))).sub
      (fderiv ℝ μ x).continuous.measurable
  have hD : Measurable (fun z : Euc d => (μ x - μ (x - z)) / ‖z‖ ^ ((d : ℝ) + 1)) :=
    (measurable_const.sub (hμ.measurable.comp (measurable_const.sub measurable_id))).div
      (measurable_norm.pow_const _)
  exact Measurable.ite ((measurableSet_lt measurable_const measurable_norm).inter
      (measurableSet_le measurable_norm measurable_const))
    (hR.div (measurable_norm.pow_const _))
    (Measurable.ite (measurableSet_lt measurable_const measurable_norm) hD measurable_const)

lemma sa16u3_kA_le {μ : Euc d → ℝ} (hμ : ContDiff ℝ 2 μ) {B0 B2 : ℝ} (hB0 : 0 ≤ B0) (hB2 : 0 ≤ B2)
    (h0 : ∀ y, |μ y| ≤ B0) (h2 : ∀ y, ‖iteratedFDeriv ℝ 2 μ y‖ ≤ B2) {δ : ℝ} (hδ : 0 < δ)
    (x z : Euc d) : |sa16u3_kA d μ δ x z| ≤ sa16u3_m d B0 B2 z := by
  have hm0 := sa16u3_m_nonneg (d := d) hB0 hB2 z
  unfold sa16u3_kA
  by_cases h1 : δ < ‖z‖ ∧ ‖z‖ ≤ 1
  · rw [if_pos h1]
    have hn : 0 < ‖z‖ := hδ.trans h1.1
    have hD : 0 < ‖z‖ ^ ((d : ℝ) + 1) := Real.rpow_pos_of_pos hn _
    have hT := elema_taylor hμ h2 x z
    have hzb : z ∈ closedBall (0 : Euc d) 1 := by simpa using h1.2
    have hzo : z ∉ {z : Euc d | 1 < ‖z‖} := fun h => absurd (show 1 < ‖z‖ from h) (not_lt.2 h1.2)
    unfold sa16u3_m
    rw [Set.indicator_of_mem hzb, Set.indicator_of_notMem hzo, mul_zero, add_zero]
    rw [abs_div, abs_of_pos hD, div_le_iff₀ hD]
    calc |elema_R μ x z| ≤ B2 / 2 * ‖z‖ ^ 2 := hT
      _ = B2 / 2 * ‖z‖ ^ (2 - ((d : ℝ) + 1)) * ‖z‖ ^ ((d : ℝ) + 1) := by
          rw [mul_assoc (B2 / 2), ← Real.rpow_add hn]
          have : (2 - ((d : ℝ) + 1) + ((d : ℝ) + 1)) = ((2 : ℕ) : ℝ) := by push_cast; ring
          rw [this, Real.rpow_natCast]
  · rw [if_neg h1]
    by_cases h2' : 1 < ‖z‖
    · rw [if_pos h2']
      have hn : 0 < ‖z‖ := one_pos.trans h2'
      have hD : 0 < ‖z‖ ^ ((d : ℝ) + 1) := Real.rpow_pos_of_pos hn _
      have hzo : z ∈ {z : Euc d | 1 < ‖z‖} := h2'
      have hzb : z ∉ closedBall (0 : Euc d) 1 := by simpa using h2'
      have e1 : |μ x - μ (x - z)| ≤ 2 * B0 := by
        have a1 := h0 x
        have a2 := h0 (x - z)
        calc |μ x - μ (x - z)| ≤ |μ x| + |μ (x - z)| := abs_sub _ _
          _ ≤ 2 * B0 := by linarith
      unfold sa16u3_m
      rw [Set.indicator_of_notMem hzb, Set.indicator_of_mem hzo, mul_zero, zero_add]
      rw [abs_div, abs_of_pos hD, Real.rpow_neg hn.le, ← div_eq_mul_inv]
      exact div_le_div_of_nonneg_right e1 hD.le
    · rw [if_neg h2', abs_zero]; exact hm0

lemma sa16u3_kA_int (hd : 1 ≤ d) {μ : Euc d → ℝ} (hμ : ContDiff ℝ 2 μ) {B0 B2 : ℝ} (hB0 : 0 ≤ B0)
    (hB2 : 0 ≤ B2) (h0 : ∀ y, |μ y| ≤ B0) (h2 : ∀ y, ‖iteratedFDeriv ℝ 2 μ y‖ ≤ B2) {δ : ℝ}
    (hδ : 0 < δ) (W : SchwartzMap (Euc d) ℝ) (x : Euc d) :
    Integrable (fun z => sa16u3_kA d μ δ x z * W (x - z)) := by
  obtain ⟨BW, LW, MW, hpvW⟩ := PvC2.of_schwartz W
  refine Integrable.mono' ((sa16u3_m_int hd B0 B2).mul_const BW)
    ((sa16u3_kA_meas hμ.continuous δ x).aestronglyMeasurable.mul
      (W.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (Eventually.of_forall fun z => ?_)
  rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact mul_le_mul (sa16u3_kA_le hμ hB0 hB2 h0 h2 hδ x z) (hpvW.bdd _) (abs_nonneg _)
    (sa16u3_m_nonneg hB0 hB2 z)

end K7b
end HRS.Whole.AppendixA.Phase2SA16Cutoff
