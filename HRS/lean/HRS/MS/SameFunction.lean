import HRS.Whole.AppendixBKernel
import HRS.PDE.ToolboxRd.Weighted

/-!
# Lemma S.B.8(i) (`same_function_rd`) on `ℝ^d` (packet MS-SAMEFN-I)

`same_function_rd_proof` restates `HRS.Whole.same_function_rd` (frozen in
`HRS/Whole/AppendixBKernel.lean`, statement copied verbatim) and proves it in the style of the torus
analogue `HRS/PDE/Toolbox/SameFunction.lean`.  Majorant of the symmetrized kernel:
`|κ(x-y)| |a(y)-a(x)| ≤ K₀ (La 1_{|z|<1}|z|^{-s} + 2Λ 1_{|z|≥1}|z|^{-s-1})`, integrable because
`s < d` and `s + 1 > d`; Schur's bound (`HRS.PDE.ToolboxRd.WeightAux.schur_bound`) gives absolute
convergence and the estimate with `C = ∫1_{|z|<1}|z|^{-s} + ∫1_{|z|≥1}|z|^{-s-1}` (depends on `d, s`).
The truncations are integrable (majorant `K₀Λ(ε⁻¹ 1_{|z|<1}|z|^{-s} + 1_{|z|≥1}|z|^{-s-1})`) and tend to
the symmetrized integral by oddness of `κ` and dominated convergence.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.SameFunction

open HRS.Whole

variable {d : ℕ}

/-- The inner kernel `1_{|z|<1} |z|^{-s}`. -/
def msf_I1 (s : ℝ) (z : Euc d) : ℝ :=
  Set.indicator (Metric.ball (0 : Euc d) 1) (fun z : Euc d => ‖z‖ ^ (-s)) z

/-- The outer kernel `1_{|z|≥1} |z|^{-s-1}`. -/
def msf_I2 (s : ℝ) (z : Euc d) : ℝ :=
  Set.indicator (Metric.ball (0 : Euc d) 1)ᶜ (fun z : Euc d => ‖z‖ ^ (-s - 1)) z

theorem msf_I1_nonneg (s : ℝ) (z : Euc d) : 0 ≤ msf_I1 s z :=
  Set.indicator_nonneg (fun z _ => Real.rpow_nonneg (norm_nonneg _) _) z

theorem msf_I2_nonneg (s : ℝ) (z : Euc d) : 0 ≤ msf_I2 s z :=
  Set.indicator_nonneg (fun z _ => Real.rpow_nonneg (norm_nonneg _) _) z

theorem msf_I1_lt {s : ℝ} {z : Euc d} (h : ‖z‖ < 1) : msf_I1 s z = ‖z‖ ^ (-s) :=
  Set.indicator_of_mem (mem_ball_zero_iff.2 h) _

theorem msf_I1_ge {s : ℝ} {z : Euc d} (h : 1 ≤ ‖z‖) : msf_I1 s z = 0 :=
  Set.indicator_of_notMem (fun h' => by linarith [mem_ball_zero_iff.1 h']) _

theorem msf_I2_lt {s : ℝ} {z : Euc d} (h : ‖z‖ < 1) : msf_I2 s z = 0 :=
  Set.indicator_of_notMem (fun h' => (Set.mem_compl_iff _ _).1 h' (mem_ball_zero_iff.2 h)) _

theorem msf_I2_ge {s : ℝ} {z : Euc d} (h : 1 ≤ ‖z‖) : msf_I2 s z = ‖z‖ ^ (-s - 1) :=
  Set.indicator_of_mem (Set.mem_compl (fun h' => by linarith [mem_ball_zero_iff.1 h'])) _

theorem msf_exists_ne (hd : 1 ≤ d) : ∃ z : Euc d, z ≠ 0 := by
  have : Nontrivial (Euc d) := by
    apply Module.nontrivial_of_finrank_pos (R := ℝ)
    rw [finrank_euclideanSpace_fin]; omega
  exact exists_ne 0

/-- Integrability of `1_{|z|<1}|z|^{-s}` for `s < d`. -/
theorem msf_I1_int (hd : 1 ≤ d) {s : ℝ} (hsd : s < d) :
    Integrable (fun z : Euc d => msf_I1 s z) := by
  have hfr : Module.finrank ℝ (Euc d) = d := finrank_euclideanSpace_fin
  have hon : IntegrableOn (fun z : Euc d => ‖z‖ ^ (-s)) (Metric.ball (0 : Euc d) 1) := by
    refine integrableOn_ball_of_norm_le_rpow (C := 1) (α := s) (r := 1) (by rw [hfr]; omega)
      (by rw [hfr]; exact hsd) (Filter.Eventually.of_forall fun z => ?_)
      (measurable_norm.pow_const _).aestronglyMeasurable
    show ‖‖z‖ ^ (-s)‖ ≤ 1 * ‖z‖ ^ (-s)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), one_mul]
  exact (integrable_indicator_iff measurableSet_ball).2 hon

/-- `t^{-r} ≤ 2^r (1+t)^{-r}` for `t ≥ 1`, `r ≥ 0`. -/
theorem msf_rpow_tail {t r : ℝ} (ht : 1 ≤ t) (hr : 0 ≤ r) :
    t ^ (-r) ≤ 2 ^ r * (1 + t) ^ (-r) := by
  have ht0 : 0 < t := by linarith
  have h1 : (2 * t) ^ (-r) ≤ (1 + t) ^ (-r) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by linarith)
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) ht0.le] at h1
  have h2 : (2 : ℝ) ^ r * (2 : ℝ) ^ (-r) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]; simp
  calc t ^ (-r) = 2 ^ r * (2 ^ (-r) * t ^ (-r)) := by rw [← mul_assoc, h2, one_mul]
    _ ≤ 2 ^ r * (1 + t) ^ (-r) := mul_le_mul_of_nonneg_left h1 (by positivity)

/-- Integrability of `1_{|z|≥1}|z|^{-s-1}` for `s + 1 > d`. -/
theorem msf_I2_int {s : ℝ} (hs : (d : ℝ) < s + 1) :
    Integrable (fun z : Euc d => msf_I2 s z) := by
  have hfr : Module.finrank ℝ (Euc d) = d := finrank_euclideanSpace_fin
  have h1 : Integrable (fun z : Euc d => (1 + ‖z‖) ^ (-(s + 1))) :=
    integrable_one_add_norm (by rw [hfr]; exact hs)
  have hdom : Integrable (fun z : Euc d => (2 : ℝ) ^ (s + 1) * (1 + ‖z‖) ^ (-(s + 1))) :=
    h1.const_mul _
  refine hdom.mono' ((measurable_norm.pow_const _).indicator measurableSet_ball.compl).aestronglyMeasurable
    (Filter.Eventually.of_forall fun z => ?_)
  show ‖Set.indicator (Metric.ball (0 : Euc d) 1)ᶜ (fun z : Euc d => ‖z‖ ^ (-s - 1)) z‖ ≤ _
  by_cases hz : z ∈ (Metric.ball (0 : Euc d) 1)ᶜ
  · have h1' : 1 ≤ ‖z‖ := not_lt.1 (fun h => (Set.mem_compl_iff _ _).1 hz (mem_ball_zero_iff.2 h))
    rw [Set.indicator_of_mem hz, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
    have e : -s - 1 = -(s + 1) := by ring
    rw [e]
    exact msf_rpow_tail h1' (by linarith)
  · rw [Set.indicator_of_notMem hz, norm_zero]
    positivity

/-- The truncation majorant: `|z|^{-s-1} ≤ ε⁻¹ 1_{|z|<1}|z|^{-s} + 1_{|z|≥1}|z|^{-s-1}` when `ε < |z|`. -/
theorem msf_trunc_majorant {s ε : ℝ} (hε : 0 < ε) {z : Euc d} (hz : ε < ‖z‖) :
    ‖z‖ ^ (-s - 1) ≤ ε⁻¹ * msf_I1 s z + msf_I2 s z := by
  have ht : 0 < ‖z‖ := hε.trans hz
  rcases lt_or_ge ‖z‖ 1 with h1 | h1
  · rw [msf_I1_lt h1, msf_I2_lt h1, add_zero]
    calc ‖z‖ ^ (-s - 1) = ‖z‖ ^ (-s) * ‖z‖⁻¹ := by
          rw [Real.rpow_sub_one ht.ne', div_eq_mul_inv]
      _ ≤ ‖z‖ ^ (-s) * ε⁻¹ :=
          mul_le_mul_of_nonneg_left (inv_anti₀ hε hz.le) (Real.rpow_nonneg ht.le _)
      _ = ε⁻¹ * ‖z‖ ^ (-s) := mul_comm _ _
  · rw [msf_I1_ge h1, msf_I2_ge h1, mul_zero, zero_add]

/-- `|a x| ≤ Λ` from the weighted bound `⟨x⟩^{d+3} |a x| ≤ Λ`. -/
theorem msf_abs_le {a : Euc d → ℝ} {Λ : ℝ}
    (H : ∀ x, jbracket x ^ ((d : ℝ) + 3) * |a x| ≤ Λ) (x : Euc d) : |a x| ≤ Λ := by
  have hj : 1 ≤ jbracket x := by
    unfold HRS.Whole.jbracket
    have h0 : 0 ≤ 1 + ‖x‖ ^ 2 := by positivity
    have h1 := Real.sq_sqrt h0
    have h2 := Real.sqrt_nonneg (1 + ‖x‖ ^ 2)
    nlinarith [sq_nonneg ‖x‖]
  have hp : 1 ≤ jbracket x ^ ((d : ℝ) + 3) := Real.one_le_rpow hj (by positivity)
  have h3 := H x
  have h0 := abs_nonneg (a x)
  nlinarith [mul_nonneg (sub_nonneg.2 hp) h0]

/-- Pointwise majorant of the symmetrized kernel. -/
theorem msf_pair_bound {κ : Euc d → ℝ} {s K₀ La Λ : ℝ} (hK : 0 ≤ K₀) (hL : 0 ≤ La) (hΛ : 0 ≤ Λ)
    (hκ0 : κ 0 = 0) (hκ : ∀ z : Euc d, z ≠ 0 → |κ z| ≤ K₀ * ‖z‖ ^ (-s - 1))
    {a : Euc d → ℝ} (ha : HRS.PDE.ToolboxRd.IsLipschitz La a) (haΛ : ∀ x, |a x| ≤ Λ)
    (x y : Euc d) :
    |κ (x - y)| * |a y - a x| ≤ K₀ * (La * msf_I1 s (x - y) + 2 * Λ * msf_I2 s (x - y)) := by
  by_cases hxy : x = y
  · have h0 : |κ (x - y)| * |a y - a x| = 0 := by
      rw [hxy, sub_self, hκ0, abs_zero, zero_mul]
    rw [h0]
    exact mul_nonneg hK (add_nonneg (mul_nonneg hL (msf_I1_nonneg s _))
      (mul_nonneg (mul_nonneg (by norm_num) hΛ) (msf_I2_nonneg s _)))
  · have hz : x - y ≠ 0 := sub_ne_zero.2 hxy
    have ht : 0 < ‖x - y‖ := norm_pos_iff.2 hz
    have hΔ1 : |a y - a x| ≤ La * ‖x - y‖ := by
      rw [abs_sub_comm]; exact ha x y
    have hΔ2 : |a y - a x| ≤ 2 * Λ := by
      have h1 : |a y - a x| ≤ |a y| + |a x| := by
        rw [sub_eq_add_neg, ← abs_neg (a x)]; exact abs_add_le _ _
      linarith [haΛ x, haΛ y]
    rcases lt_or_ge ‖x - y‖ 1 with h1 | h1
    · rw [msf_I1_lt h1, msf_I2_lt h1, mul_zero, add_zero]
      have e : ‖x - y‖ ^ (-s - 1) * ‖x - y‖ = ‖x - y‖ ^ (-s) := by
        rw [Real.rpow_sub_one ht.ne', div_mul_cancel₀ _ ht.ne']
      calc |κ (x - y)| * |a y - a x|
          ≤ (K₀ * ‖x - y‖ ^ (-s - 1)) * (La * ‖x - y‖) :=
            mul_le_mul (hκ _ hz) hΔ1 (abs_nonneg _) (mul_nonneg hK (Real.rpow_nonneg (norm_nonneg _) _))
        _ = K₀ * (La * ‖x - y‖ ^ (-s)) := by rw [← e]; ring
    · rw [msf_I1_ge h1, msf_I2_ge h1, mul_zero, zero_add]
      calc |κ (x - y)| * |a y - a x| ≤ (K₀ * ‖x - y‖ ^ (-s - 1)) * (2 * Λ) :=
            mul_le_mul (hκ _ hz) hΔ2 (abs_nonneg _) (mul_nonneg hK (Real.rpow_nonneg (norm_nonneg _) _))
        _ = K₀ * (2 * Λ * ‖x - y‖ ^ (-s - 1)) := by ring

theorem same_function_rd_proof (hd : 1 ≤ d) (s : ℝ) (hs1 : (d : ℝ) - 1 < s) (hsd : s < d) :
    ∃ C : ℝ, ∀ (κ : Euc d → ℝ) (K₀ : ℝ), (∀ z, κ (-z) = -κ z) →
      ContDiffOn ℝ ∞ κ {z | z ≠ 0} → (∀ z : Euc d, z ≠ 0 → |κ z| ≤ K₀ * ‖z‖ ^ (-s - 1)) →
      ∀ (La Λ : ℝ) (a w : Euc d → ℝ), HRS.PDE.ToolboxRd.IsLipschitz La a →
        (∀ x, jbracket x ^ ((d : ℝ) + 3) * |a x| ≤ Λ) → MemLp w 2 volume →
      Integrable (fun p : Euc d × Euc d => κ (p.1 - p.2) * w p.1 * w p.2 * (a p.2 - a p.1)) ∧
      (∀ ε : ℝ, 0 < ε → Integrable (fun p : Euc d × Euc d =>
        if ε < ‖p.1 - p.2‖ then κ (p.1 - p.2) * a p.2 * w p.2 * w p.1 else 0)) ∧
      Tendsto (fun ε => truncPairing ε κ a w (fun _ => 1)) (𝓝[>] 0)
        (𝓝 (symPairing κ a w (fun _ => 1))) ∧
      |symPairing κ a w (fun _ => 1)| ≤ C * K₀ * (La + Λ) * ∫ x, w x ^ 2 := by
  refine ⟨(∫ z : Euc d, msf_I1 s z) + ∫ z : Euc d, msf_I2 s z, ?_⟩
  intro κ K₀ hodd hsm hbd La Λ a w ha hjb hw
  have hs2 : (d : ℝ) < s + 1 := by linarith
  have hκm : Measurable κ := HRS.PDE.ToolboxRd.WeightAux.measurable_of_smooth hsm
  have hκ0 : κ 0 = 0 := by
    have h := hodd 0
    rw [neg_zero] at h
    linarith
  have hacont : Continuous a := HRS.PDE.ToolboxRd.WeightAux.isLipschitz_continuous ha
  have haΛ : ∀ x, |a x| ≤ Λ := fun x => msf_abs_le hjb x
  obtain ⟨z₀, hz₀⟩ := msf_exists_ne hd
  have hK : 0 ≤ K₀ := by
    have h1 := hbd z₀ hz₀
    have h2 : 0 < ‖z₀‖ ^ (-s - 1) := Real.rpow_pos_of_pos (norm_pos_iff.2 hz₀) _
    by_contra hneg
    push_neg at hneg
    linarith [abs_nonneg (κ z₀), mul_neg_of_neg_of_pos hneg h2]
  have hL : 0 ≤ La := by
    have h1 := ha 0 z₀
    rw [zero_sub, norm_neg] at h1
    have hpos : 0 < ‖z₀‖ := norm_pos_iff.2 hz₀
    by_contra hneg
    push_neg at hneg
    linarith [abs_nonneg (a 0 - a z₀), mul_neg_of_neg_of_pos hneg hpos]
  have hΛ0 : 0 ≤ Λ := (abs_nonneg (a 0)).trans (haΛ 0)
  -- measurability
  have hwm : AEStronglyMeasurable w volume := hw.aestronglyMeasurable
  have hw1 : AEStronglyMeasurable (fun p : Euc d × Euc d => w p.1)
      (volume : Measure (Euc d × Euc d)) :=
    hwm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hw2 : AEStronglyMeasurable (fun p : Euc d × Euc d => w p.2)
      (volume : Measure (Euc d × Euc d)) :=
    hwm.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hk : AEStronglyMeasurable (fun p : Euc d × Euc d => κ (p.1 - p.2))
      (volume : Measure (Euc d × Euc d)) :=
    (hκm.comp (measurable_fst.sub measurable_snd)).aestronglyMeasurable
  have ha1 : AEStronglyMeasurable (fun p : Euc d × Euc d => a p.1)
      (volume : Measure (Euc d × Euc d)) :=
    (hacont.measurable.comp measurable_fst).aestronglyMeasurable
  have ha2 : AEStronglyMeasurable (fun p : Euc d × Euc d => a p.2)
      (volume : Measure (Euc d × Euc d)) :=
    (hacont.measurable.comp measurable_snd).aestronglyMeasurable
  have hsetm : ∀ ε : ℝ, MeasurableSet {p : Euc d × Euc d | ε < ‖p.1 - p.2‖} := fun ε =>
    measurableSet_lt measurable_const (measurable_fst.sub measurable_snd).norm
  -- the symmetrized integrand
  set F : Euc d × Euc d → ℝ := fun p => κ (p.1 - p.2) * w p.1 * w p.2 * (a p.2 - a p.1)
    with hFdef
  have hFm : AEStronglyMeasurable F (volume : Measure (Euc d × Euc d)) :=
    ((hk.mul hw1).mul hw2).mul (ha2.sub ha1)
  have hρ1int : Integrable (fun z : Euc d => K₀ * (La * msf_I1 s z + 2 * Λ * msf_I2 s z)) :=
    (((msf_I1_int hd hsd).const_mul La).add ((msf_I2_int hs2).const_mul (2 * Λ))).const_mul K₀
  have hρ1nn : ∀ z : Euc d, 0 ≤ K₀ * (La * msf_I1 s z + 2 * Λ * msf_I2 s z) := fun z =>
    mul_nonneg hK (add_nonneg (mul_nonneg hL (msf_I1_nonneg s z))
      (mul_nonneg (mul_nonneg (by norm_num) hΛ0) (msf_I2_nonneg s z)))
  have hFbd : ∀ p : Euc d × Euc d, |F p| ≤
      (K₀ * (La * msf_I1 s (p.1 - p.2) + 2 * Λ * msf_I2 s (p.1 - p.2))) * (|w p.1| * |w p.2|) := by
    intro p
    have hb := msf_pair_bound (s := s) hK hL hΛ0 hκ0 hbd ha haΛ p.1 p.2
    have e : |F p| = |κ (p.1 - p.2)| * |a p.2 - a p.1| * (|w p.1| * |w p.2|) := by
      simp only [hFdef, abs_mul]; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right hb (by positivity)
  obtain ⟨hFint, hFbound⟩ := HRS.PDE.ToolboxRd.WeightAux.schur_bound hρ1int hρ1nn hw hFm hFbd
  have hρint : ∫ z : Euc d, K₀ * (La * msf_I1 s z + 2 * Λ * msf_I2 s z) =
      K₀ * (La * (∫ z : Euc d, msf_I1 s z) + 2 * Λ * (∫ z : Euc d, msf_I2 s z)) := by
    rw [integral_const_mul, integral_add ((msf_I1_int hd hsd).const_mul La)
      ((msf_I2_int hs2).const_mul (2 * Λ)), integral_const_mul, integral_const_mul]
  rw [hρint] at hFbound
  -- truncations
  set T : ℝ → Euc d × Euc d → ℝ := fun ε p =>
    if ε < ‖p.1 - p.2‖ then κ (p.1 - p.2) * a p.2 * w p.2 * w p.1 else 0 with hTdef
  set T' : ℝ → Euc d × Euc d → ℝ := fun ε p =>
    if ε < ‖p.1 - p.2‖ then κ (p.1 - p.2) * a p.1 * w p.2 * w p.1 else 0 with hT'def
  set G : ℝ → Euc d × Euc d → ℝ := fun ε p =>
    if ε < ‖p.1 - p.2‖ then F p else 0 with hGdef
  have hTm : ∀ ε : ℝ, AEStronglyMeasurable (T ε) (volume : Measure (Euc d × Euc d)) := by
    intro ε
    have e : T ε = Set.indicator {p : Euc d × Euc d | ε < ‖p.1 - p.2‖}
        (fun p => κ (p.1 - p.2) * a p.2 * w p.2 * w p.1) := by
      funext p; simp only [hTdef, Set.indicator, Set.mem_setOf_eq]
    rw [e]
    exact (((hk.mul ha2).mul hw2).mul hw1).indicator (hsetm ε)
  have hTint : ∀ ε : ℝ, 0 < ε → Integrable (T ε) := by
    intro ε hε
    have hρε : Integrable (fun z : Euc d => K₀ * Λ * (ε⁻¹ * msf_I1 s z + msf_I2 s z)) :=
      (((msf_I1_int hd hsd).const_mul ε⁻¹).add (msf_I2_int hs2)).const_mul (K₀ * Λ)
    have hρεnn : ∀ z : Euc d, 0 ≤ K₀ * Λ * (ε⁻¹ * msf_I1 s z + msf_I2 s z) := fun z =>
      mul_nonneg (mul_nonneg hK hΛ0)
        (add_nonneg (mul_nonneg (inv_nonneg.2 hε.le) (msf_I1_nonneg s z)) (msf_I2_nonneg s z))
    refine (HRS.PDE.ToolboxRd.WeightAux.schur_bound hρε hρεnn hw (hTm ε) ?_).1
    intro p
    by_cases hlt : ε < ‖p.1 - p.2‖
    · have hne : p.1 - p.2 ≠ 0 := by
        intro h; rw [h, norm_zero] at hlt; linarith
      have hk1 := hbd _ hne
      have hD : ‖p.1 - p.2‖ ^ (-s - 1) ≤ ε⁻¹ * msf_I1 s (p.1 - p.2) + msf_I2 s (p.1 - p.2) :=
        msf_trunc_majorant hε hlt
      have hk2 : |κ (p.1 - p.2)| ≤ K₀ * (ε⁻¹ * msf_I1 s (p.1 - p.2) + msf_I2 s (p.1 - p.2)) :=
        hk1.trans (mul_le_mul_of_nonneg_left hD hK)
      have hD0 : 0 ≤ ε⁻¹ * msf_I1 s (p.1 - p.2) + msf_I2 s (p.1 - p.2) :=
        add_nonneg (mul_nonneg (inv_nonneg.2 hε.le) (msf_I1_nonneg _ _)) (msf_I2_nonneg _ _)
      have e : |κ (p.1 - p.2) * a p.2 * w p.2 * w p.1|
          = |κ (p.1 - p.2)| * |a p.2| * (|w p.1| * |w p.2|) := by
        simp only [abs_mul]; ring
      have hT : |T ε p| = |κ (p.1 - p.2) * a p.2 * w p.2 * w p.1| := by
        simp only [hTdef, if_pos hlt]
      rw [hT, e]
      refine le_trans (mul_le_mul (mul_le_mul hk2 (haΛ p.2) (abs_nonneg _)
        (mul_nonneg hK hD0)) le_rfl (by positivity) (mul_nonneg (mul_nonneg hK hD0) hΛ0)) (le_of_eq ?_)
      ring
    · have hT : T ε p = 0 := by simp only [hTdef, if_neg hlt]
      rw [hT, abs_zero]
      exact mul_nonneg (hρεnn _) (by positivity)
  -- symmetrization of the truncations
  have hsym : ∀ ε : ℝ, 0 < ε → ∫ p, T ε p = (1 / 2) * ∫ p, G ε p := by
    intro ε hε
    have hswap : ∀ p : Euc d × Euc d, T' ε p = -(T ε (Prod.swap p)) := by
      intro p
      simp only [hT'def, hTdef, Prod.fst_swap, Prod.snd_swap]
      rw [norm_sub_rev p.2 p.1]
      split_ifs with h
      · have : κ (p.2 - p.1) = -κ (p.1 - p.2) := by rw [← neg_sub, hodd]
        rw [this]; ring
      · simp
    have hT'int : Integrable (T' ε) := by
      have h2 := (hTint ε hε).swap.neg
      refine h2.congr (Eventually.of_forall fun p => ?_)
      exact (hswap p).symm
    have hGsplit : ∀ p, G ε p = T ε p - T' ε p := by
      intro p
      simp only [hGdef, hTdef, hT'def, hFdef]
      split_ifs
      · ring
      · simp
    have h1 : ∫ p, G ε p = (∫ p, T ε p) - ∫ p, T' ε p := by
      rw [show (fun p => G ε p) = fun p => T ε p - T' ε p from funext hGsplit]
      exact integral_sub (hTint ε hε) hT'int
    have h2 : ∫ p, T' ε p = -∫ p, T ε p := by
      rw [show (fun p => T' ε p) = fun p => -(T ε (Prod.swap p)) from funext hswap, integral_neg]
      congr 1
      exact integral_prod_swap (μ := (volume : Measure (Euc d))) (ν := (volume : Measure (Euc d)))
        (T ε)
    rw [h1, h2]; ring
  have hGint : ∀ ε : ℝ, Integrable (G ε) := by
    intro ε
    refine hFint.norm.mono' ?_ (Eventually.of_forall fun p => ?_)
    · have e : G ε = Set.indicator {p : Euc d × Euc d | ε < ‖p.1 - p.2‖} F := by
        funext p; simp only [hGdef, Set.indicator, Set.mem_setOf_eq]
      rw [e]
      exact hFm.indicator (hsetm ε)
    · simp only [hGdef]
      split_ifs
      · exact le_rfl
      · simp
  have hlim : Tendsto (fun ε : ℝ => ∫ p, G ε p) (𝓝[>] 0) (𝓝 (∫ p, F p)) := by
    refine tendsto_integral_filter_of_dominated_convergence (fun p => ‖F p‖)
      (Eventually.of_forall fun ε => (hGint ε).aestronglyMeasurable)
      (Eventually.of_forall fun ε => Eventually.of_forall fun p => ?_) hFint.norm ?_
    · simp only [hGdef]
      split_ifs
      · exact le_rfl
      · simp
    · refine Eventually.of_forall fun p => ?_
      by_cases hpt : ‖p.1 - p.2‖ = 0
      · have hz0 : p.1 - p.2 = 0 := norm_eq_zero.1 hpt
        have hF0 : F p = 0 := by simp only [hFdef, hz0, hκ0, zero_mul]
        rw [hF0]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with ε hε
        have hn : ¬ ε < ‖p.1 - p.2‖ := by
          rw [hpt]; exact not_lt.2 (Set.mem_Ioi.1 hε).le
        show (0 : ℝ) = G ε p
        simp only [hGdef, if_neg hn]
      · have hpos : 0 < ‖p.1 - p.2‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hpt)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [Ioo_mem_nhdsGT hpos] with ε hε
        show F p = G ε p
        simp only [hGdef, if_pos hε.2]
  -- conclusions
  have hTP : ∀ ε : ℝ, HRS.Whole.truncPairing ε κ a w (fun _ => 1) = ∫ p, T ε p := by
    intro ε
    simp only [HRS.Whole.truncPairing, mul_one, hTdef]
  have hSP : HRS.Whole.symPairing κ a w (fun _ => 1) = (1 / 2) * ∫ p, F p := by
    simp only [HRS.Whole.symPairing, mul_one, hFdef]
  refine ⟨hFint, fun ε hε => hTint ε hε, ?_, ?_⟩
  · simp only [hTP, hSP]
    refine (hlim.const_mul (1 / 2)).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (hsym ε (Set.mem_Ioi.1 hε)).symm
  · rw [hSP, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    have hW : 0 ≤ ∫ x, w x ^ 2 := integral_nonneg fun x => sq_nonneg _
    have hc1 : 0 ≤ ∫ z : Euc d, msf_I1 s z := integral_nonneg (msf_I1_nonneg s)
    have hc2 : 0 ≤ ∫ z : Euc d, msf_I2 s z := integral_nonneg (msf_I2_nonneg s)
    have hX : 0 ≤ K₀ * ∫ x, w x ^ 2 := mul_nonneg hK hW
    have hY : 0 ≤ ((∫ z : Euc d, msf_I1 s z) + ∫ z : Euc d, msf_I2 s z) * (La + Λ)
        - 1 / 2 * (La * (∫ z : Euc d, msf_I1 s z) + 2 * Λ * ∫ z : Euc d, msf_I2 s z) := by
      nlinarith [mul_nonneg hL hc1, mul_nonneg hΛ0 hc1, mul_nonneg hL hc2, mul_nonneg hΛ0 hc2]
    have hC := mul_le_mul_of_nonneg_left hFbound (by norm_num : (0:ℝ) ≤ 1 / 2)
    nlinarith [mul_nonneg hX hY]

example := (@same_function_rd_proof : type_of% @HRS.Whole.same_function_rd)

end HRS.MS.SameFunction
