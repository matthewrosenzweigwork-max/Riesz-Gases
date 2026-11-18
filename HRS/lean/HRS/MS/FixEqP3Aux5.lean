import HRS.MS.FixEqP3Aux4

/-!
# S5.7 `fixed_equation` (worker S57P), part 17: weighted `L²([0,T]×ℝ^d; ℝ^d)` kernels

`s57pμ d T = (Leb|[0,T]) ⊗ Leb`; a kernel `κ_t = 1_{r ≤ t} w • A_t` (`s57pkf`), its element `s57pel` of `L²(s57pμ; ℝ^d)`.
`s57p_el_holder`: `‖κ_t - κ_s‖² ≤ W_m (B_d² (t-s)² T + B_a² (t-s))` when `∫ w(r,x)² dx ≤ W_m`, `|A_t| ≤ B_a` (`r ≤ t`) and
`|A_t - A_s| ≤ B_d (t-s)` (`r ≤ s`); `s57p_el_norm`: `‖κ_t‖² ≤ W_m T B_a²`.
-/

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.FixEq

open HRS HRS.Whole

variable {d : ℕ}

/-- `Leb|[0,T] ⊗ Leb` on `ℝ × ℝ^d` -/
def s57pμ (d : ℕ) (T : ℝ) : Measure (ℝ × Euc d) :=
  (volume.restrict (Set.Icc (0 : ℝ) T)).prod (volume : Measure (Euc d))

instance (T : ℝ) : SigmaFinite (s57pμ d T) := by unfold s57pμ; infer_instance

/-- the kernel `1_{r ≤ t} w • A` -/
def s57pkf (w : ℝ × Euc d → ℝ) (A : ℝ × Euc d → Euc d) (t : ℝ) : ℝ × Euc d → Euc d :=
  fun p => if p.1 ≤ t then w p • A p else 0

theorem s57p_ae_fst (T : ℝ) : ∀ᵐ p ∂(s57pμ d T), p.1 ∈ Set.Icc (0 : ℝ) T :=
  Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)

theorem s57p_lint_prod_le {T : ℝ} {f : ℝ × Euc d → ℝ≥0∞} (hf : Measurable f) {g : ℝ → ℝ≥0∞}
    (hg : ∀ r ∈ Set.Icc (0 : ℝ) T, ∫⁻ x, f (r, x) ≤ g r) :
    ∫⁻ p, f p ∂(s57pμ d T) ≤ ∫⁻ r in Set.Icc (0 : ℝ) T, g r := by
  unfold s57pμ
  rw [lintegral_prod _ hf.aemeasurable]
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
  exact hg r hr

theorem s57p_W_total {T : ℝ} (hT : 0 ≤ T) {w : ℝ × Euc d → ℝ} (hw : Measurable w) {Wm : ℝ} (hWm : 0 ≤ Wm)
    (hW : ∀ r ∈ Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (w (r, x) ^ 2) ≤ ENNReal.ofReal Wm) :
    ∫⁻ p, ENNReal.ofReal (w p ^ 2) ∂(s57pμ d T) ≤ ENNReal.ofReal (T * Wm) := by
  have hm : Measurable fun p => ENNReal.ofReal (w p ^ 2) := ENNReal.measurable_ofReal.comp (hw.pow_const 2)
  refine (s57p_lint_prod_le hm (g := fun _ => ENNReal.ofReal Wm) hW).trans ?_
  rw [setLIntegral_const, Real.volume_Icc, sub_zero, ← ENNReal.ofReal_mul hWm, mul_comm]

theorem s57p_ker_pt {w : ℝ × Euc d → ℝ} {At As : ℝ × Euc d → Euc d} {s t Ba Bd : ℝ} (hst : s ≤ t)
    (hAt : ∀ p : ℝ × Euc d, p.1 ∈ Set.Icc (0 : ℝ) t → ‖At p‖ ≤ Ba)
    (hD : ∀ p : ℝ × Euc d, p.1 ∈ Set.Icc (0 : ℝ) s → ‖At p - As p‖ ≤ Bd * (t - s))
    (p : ℝ × Euc d) (hp : 0 ≤ p.1) :
    ‖s57pkf w At t p - s57pkf w As s p‖ ^ 2 ≤
      w p ^ 2 * (Bd ^ 2 * (t - s) ^ 2 + (Set.Ioc s t).indicator (fun _ => Ba ^ 2) p.1) := by
  have hw2 : 0 ≤ w p ^ 2 := sq_nonneg _
  have hi : 0 ≤ (Set.Ioc s t).indicator (fun _ => Ba ^ 2) p.1 := Set.indicator_nonneg (fun _ _ => sq_nonneg _) _
  have hb : 0 ≤ Bd ^ 2 * (t - s) ^ 2 := by positivity
  by_cases h1 : p.1 ≤ s
  · have h2 : p.1 ≤ t := h1.trans hst
    have hnot : p.1 ∉ Set.Ioc s t := fun h => absurd h.1 (not_lt.2 h1)
    simp only [s57pkf, h1, h2, if_true]
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    rw [Set.indicator_of_notMem hnot, add_zero]
    refine mul_le_mul_of_nonneg_left ?_ hw2
    have := hD p ⟨hp, h1⟩
    calc ‖At p - As p‖ ^ 2 ≤ (Bd * (t - s)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
      _ = Bd ^ 2 * (t - s) ^ 2 := by ring
  · by_cases h2 : p.1 ≤ t
    · have hmem : p.1 ∈ Set.Ioc s t := ⟨not_le.1 h1, h2⟩
      simp only [s57pkf, h1, h2, if_true, if_false, sub_zero]
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, Set.indicator_of_mem hmem]
      have := hAt p ⟨hp, h2⟩
      have h3 : ‖At p‖ ^ 2 ≤ Ba ^ 2 := pow_le_pow_left₀ (norm_nonneg _) this 2
      nlinarith [mul_le_mul_of_nonneg_left h3 hw2]
    · simp only [s57pkf, h1, h2, if_false, sub_zero, norm_zero]
      rw [show ((0 : ℝ) ^ 2) = 0 by norm_num]
      positivity

theorem s57p_ker_holder_lint {T : ℝ} (hT : 0 ≤ T) {w : ℝ × Euc d → ℝ} (hw : Measurable w) {Wm : ℝ} (hWm : 0 ≤ Wm)
    (hW : ∀ r ∈ Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (w (r, x) ^ 2) ≤ ENNReal.ofReal Wm)
    {At As : ℝ × Euc d → Euc d} {s t Ba Bd : ℝ} (hst : s ≤ t)
    (hAt : ∀ p : ℝ × Euc d, p.1 ∈ Set.Icc (0 : ℝ) t → ‖At p‖ ≤ Ba)
    (hD : ∀ p : ℝ × Euc d, p.1 ∈ Set.Icc (0 : ℝ) s → ‖At p - As p‖ ≤ Bd * (t - s)) :
    ∫⁻ p, ENNReal.ofReal (‖s57pkf w At t p - s57pkf w As s p‖ ^ 2) ∂(s57pμ d T) ≤
      ENNReal.ofReal (Wm * (Bd ^ 2 * (t - s) ^ 2 * T + Ba ^ 2 * (t - s))) := by
  set a : ℝ := Bd ^ 2 * (t - s) ^ 2 with ha
  set b : ℝ := Ba ^ 2 with hb
  have ha0 : 0 ≤ a := by positivity
  have hb0 : 0 ≤ b := by positivity
  set c : ℝ → ℝ≥0∞ := fun r => ENNReal.ofReal a + (Set.Ioc s t).indicator (fun _ => ENNReal.ofReal b) r with hc
  have hcm : Measurable c := by
    show Measurable fun r => ENNReal.ofReal a + (Set.Ioc s t).indicator (fun _ => ENNReal.ofReal b) r
    exact Measurable.add measurable_const ((measurable_const (a := ENNReal.ofReal b)).indicator (measurableSet_Ioc (a := s) (b := t)))
  have hpt : ∀ᵐ p ∂(s57pμ d T), ENNReal.ofReal (‖s57pkf w At t p - s57pkf w As s p‖ ^ 2) ≤
      ENNReal.ofReal (w p ^ 2) * c p.1 := by
    filter_upwards [s57p_ae_fst (d := d) T] with p hp
    have h1 := s57p_ker_pt (w := w) hst hAt hD p hp.1
    refine (ENNReal.ofReal_le_ofReal h1).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (sq_nonneg _), hc]
    simp only
    congr 1
    by_cases hm : p.1 ∈ Set.Ioc s t
    · simp only [Set.indicator_of_mem hm]
      rw [ENNReal.ofReal_add ha0 hb0]
    · simp only [Set.indicator_of_notMem hm, add_zero]
      rfl
  refine (lintegral_mono_ae hpt).trans ?_
  have hfm : Measurable fun p : ℝ × Euc d => ENNReal.ofReal (w p ^ 2) * c p.1 :=
    (ENNReal.measurable_ofReal.comp (hw.pow_const 2)).mul (hcm.comp measurable_fst)
  refine (s57p_lint_prod_le hfm (g := fun r => ENNReal.ofReal Wm * c r) (fun r hr => ?_)).trans ?_
  · have hmx : Measurable fun x : Euc d => ENNReal.ofReal (w (r, x) ^ 2) :=
      ENNReal.measurable_ofReal.comp ((hw.comp (measurable_const.prodMk measurable_id)).pow_const 2)
    simp only
    calc ∫⁻ x, ENNReal.ofReal (w (r, x) ^ 2) * c r = (∫⁻ x, ENNReal.ofReal (w (r, x) ^ 2)) * c r :=
          lintegral_mul_const _ hmx
      _ ≤ ENNReal.ofReal Wm * c r := mul_le_mul' (hW r hr) le_rfl
  · rw [lintegral_const_mul _ hcm, hc]
    rw [lintegral_add_left measurable_const, setLIntegral_const, lintegral_indicator measurableSet_Ioc,
      setLIntegral_const, Measure.restrict_apply measurableSet_Ioc, Real.volume_Icc, sub_zero]
    have hvol : volume (Set.Ioc s t ∩ Set.Icc (0 : ℝ) T) ≤ ENNReal.ofReal (t - s) := by
      refine (measure_mono Set.inter_subset_left).trans ?_
      rw [Real.volume_Ioc]
    calc ENNReal.ofReal Wm * (ENNReal.ofReal a * ENNReal.ofReal T +
          ENNReal.ofReal b * volume (Set.Ioc s t ∩ Set.Icc (0 : ℝ) T))
        ≤ ENNReal.ofReal Wm * (ENNReal.ofReal a * ENNReal.ofReal T + ENNReal.ofReal b * ENNReal.ofReal (t - s)) := by
          gcongr
      _ = ENNReal.ofReal (Wm * (a * T + b * (t - s))) := by
          rw [← ENNReal.ofReal_mul ha0, ← ENNReal.ofReal_mul hb0, ← ENNReal.ofReal_add (mul_nonneg ha0 hT)
            (mul_nonneg hb0 (by linarith)), ← ENNReal.ofReal_mul hWm]

theorem s57p_ker_norm_lint {T : ℝ} (hT : 0 ≤ T) {w : ℝ × Euc d → ℝ} (hw : Measurable w) {Wm : ℝ} (hWm : 0 ≤ Wm)
    (hW : ∀ r ∈ Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (w (r, x) ^ 2) ≤ ENNReal.ofReal Wm)
    {A : ℝ × Euc d → Euc d} {t Ba : ℝ} (hA : ∀ p : ℝ × Euc d, p.1 ∈ Set.Icc (0 : ℝ) t → ‖A p‖ ≤ Ba) :
    ∫⁻ p, ENNReal.ofReal (‖s57pkf w A t p‖ ^ 2) ∂(s57pμ d T) ≤ ENNReal.ofReal (T * Wm * Ba ^ 2) := by
  have hpt : ∀ᵐ p ∂(s57pμ d T), ENNReal.ofReal (‖s57pkf w A t p‖ ^ 2) ≤
      ENNReal.ofReal (w p ^ 2) * ENNReal.ofReal (Ba ^ 2) := by
    filter_upwards [s57p_ae_fst (d := d) T] with p hp
    rw [← ENNReal.ofReal_mul (sq_nonneg _)]
    refine ENNReal.ofReal_le_ofReal ?_
    by_cases h : p.1 ≤ t
    · simp only [s57pkf, h, if_true]
      rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hA p ⟨hp.1, h⟩) 2) (sq_nonneg _)
    · simp only [s57pkf, h, if_false, norm_zero]
      rw [show ((0 : ℝ) ^ 2) = 0 by norm_num]
      positivity
  refine (lintegral_mono_ae hpt).trans ?_
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top]
  calc (∫⁻ p, ENNReal.ofReal (w p ^ 2) ∂(s57pμ d T)) * ENNReal.ofReal (Ba ^ 2)
      ≤ ENNReal.ofReal (T * Wm) * ENNReal.ofReal (Ba ^ 2) := by
        gcongr
        exact s57p_W_total hT hw hWm hW
    _ = ENNReal.ofReal (T * Wm * Ba ^ 2) := (ENNReal.ofReal_mul (mul_nonneg hT hWm)).symm

/-- the data of a weight -/
structure S57pKd (T : ℝ) (w : ℝ × Euc d → ℝ) (Wm : ℝ) : Prop where
  hT : 0 ≤ T
  hw : Measurable w
  hWm : 0 ≤ Wm
  hW : ∀ r ∈ Set.Icc (0 : ℝ) T, ∫⁻ x, ENNReal.ofReal (w (r, x) ^ 2) ≤ ENNReal.ofReal Wm

theorem s57p_kf_memLp {T : ℝ} {w : ℝ × Euc d → ℝ} {Wm : ℝ} (K : S57pKd T w Wm) {A : ℝ × Euc d → Euc d}
    (hA : AEStronglyMeasurable A (s57pμ d T)) {t Ba : ℝ}
    (hAt : ∀ p : ℝ × Euc d, p.1 ∈ Set.Icc (0 : ℝ) t → ‖A p‖ ≤ Ba) : MemLp (s57pkf w A t) 2 (s57pμ d T) := by
  have hwm : AEStronglyMeasurable w (s57pμ d T) := K.hw.aestronglyMeasurable
  have hw2 : MemLp w 2 (s57pμ d T) := by
    rw [memLp_two_iff_integrable_sq_norm hwm]
    have hint : Integrable (fun p => w p ^ 2) (s57pμ d T) := by
      rw [← lintegral_ofReal_ne_top_iff_integrable (K.hw.pow_const 2).aestronglyMeasurable
        (Eventually.of_forall fun p => sq_nonneg (w p))]
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (s57p_W_total K.hT K.hw K.hWm K.hW)
    simpa [Real.norm_eq_abs, sq_abs] using hint
  have hmeas : AEStronglyMeasurable (s57pkf w A t) (s57pμ d T) := by
    have e : s57pkf w A t = {p : ℝ × Euc d | p.1 ≤ t}.indicator (fun p => w p • A p) := by
      funext p; simp only [s57pkf, Set.indicator_apply, Set.mem_setOf_eq]
    rw [e]
    exact (hwm.smul hA).indicator (measurableSet_le measurable_fst measurable_const)
  refine (hw2.of_le_mul (c := |Ba|) hmeas ?_)
  filter_upwards [s57p_ae_fst (d := d) T] with p hp
  by_cases h : p.1 ≤ t
  · simp only [s57pkf, h, if_true]
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right ((hAt p ⟨hp.1, h⟩).trans (le_abs_self _)) (norm_nonneg _)
  · simp only [s57pkf, h, if_false, norm_zero]
    positivity

open Classical in
/-- the element of `L²(s57pμ; ℝ^d)` -/
def s57pel (T : ℝ) (w : ℝ × Euc d → ℝ) (A : ℝ × Euc d → Euc d) (t : ℝ) : Lp (Euc d) 2 (s57pμ d T) :=
  if h : MemLp (s57pkf w A t) 2 (s57pμ d T) then h.toLp _ else 0

theorem s57p_el_eq {T : ℝ} {w : ℝ × Euc d → ℝ} {A : ℝ × Euc d → Euc d} {t : ℝ}
    (h : MemLp (s57pkf w A t) 2 (s57pμ d T)) : s57pel T w A t = h.toLp (s57pkf w A t) := by
  unfold s57pel; rw [dif_pos h]

theorem s57p_toLp_norm_sq {T : ℝ} {f : ℝ × Euc d → Euc d} (hf : MemLp f 2 (s57pμ d T)) :
    ‖hf.toLp f‖ ^ 2 = ∫ p, ‖f p‖ ^ 2 ∂(s57pμ d T) := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp] with a ha
  rw [ha, real_inner_self_eq_norm_sq]

theorem s57p_int_le_of_lint {T : ℝ} {f : ℝ × Euc d → Euc d} (hf : MemLp f 2 (s57pμ d T)) {B : ℝ} (hB : 0 ≤ B)
    (h : ∫⁻ p, ENNReal.ofReal (‖f p‖ ^ 2) ∂(s57pμ d T) ≤ ENNReal.ofReal B) :
    ∫ p, ‖f p‖ ^ 2 ∂(s57pμ d T) ≤ B := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun p => sq_nonneg _)
    ((continuous_pow 2).comp_aestronglyMeasurable hf.aestronglyMeasurable.norm)]
  exact ENNReal.toReal_le_of_le_ofReal hB h

theorem s57p_el_norm {T : ℝ} {w : ℝ × Euc d → ℝ} {Wm : ℝ} (K : S57pKd T w Wm) {A : ℝ × Euc d → Euc d}
    (hA : AEStronglyMeasurable A (s57pμ d T)) {t Ba : ℝ}
    (hAt : ∀ p : ℝ × Euc d, p.1 ∈ Set.Icc (0 : ℝ) t → ‖A p‖ ≤ Ba) :
    ‖s57pel T w A t‖ ^ 2 ≤ T * Wm * Ba ^ 2 := by
  have hm := s57p_kf_memLp K hA hAt
  rw [s57p_el_eq hm, s57p_toLp_norm_sq hm]
  exact s57p_int_le_of_lint hm (by have := K.hT; have := K.hWm; positivity)
    (s57p_ker_norm_lint K.hT K.hw K.hWm K.hW hAt)

theorem s57p_el_holder {T : ℝ} {w : ℝ × Euc d → ℝ} {Wm : ℝ} (K : S57pKd T w Wm) {At As : ℝ × Euc d → Euc d}
    (hAt' : AEStronglyMeasurable At (s57pμ d T)) (hAs' : AEStronglyMeasurable As (s57pμ d T)) {s t Ba Bd : ℝ}
    (hst : s ≤ t) (hAt : ∀ p : ℝ × Euc d, p.1 ∈ Set.Icc (0 : ℝ) t → ‖At p‖ ≤ Ba)
    (hAs : ∀ p : ℝ × Euc d, p.1 ∈ Set.Icc (0 : ℝ) s → ‖As p‖ ≤ Ba)
    (hD : ∀ p : ℝ × Euc d, p.1 ∈ Set.Icc (0 : ℝ) s → ‖At p - As p‖ ≤ Bd * (t - s)) :
    ‖s57pel T w At t - s57pel T w As s‖ ^ 2 ≤ Wm * (Bd ^ 2 * (t - s) ^ 2 * T + Ba ^ 2 * (t - s)) := by
  have h1 := s57p_kf_memLp K hAt' hAt
  have h2 := s57p_kf_memLp K hAs' hAs
  rw [s57p_el_eq h1, s57p_el_eq h2, ← MemLp.toLp_sub h1 h2, s57p_toLp_norm_sq (h1.sub h2)]
  have hb : 0 ≤ Wm * (Bd ^ 2 * (t - s) ^ 2 * T + Ba ^ 2 * (t - s)) := by
    have := K.hT; have := K.hWm; have : 0 ≤ t - s := by linarith
    positivity
  refine s57p_int_le_of_lint (h1.sub h2) hb ?_
  have := s57p_ker_holder_lint K.hT K.hw K.hWm K.hW hst hAt hD
  simpa [Pi.sub_apply] using this

end HRS.MS.FixEq
