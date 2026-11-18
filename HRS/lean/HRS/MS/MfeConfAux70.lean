import HRS.MS.MfeConfAux69

/-!
# S.B.1, packet F8 (part 2): convolution toolkit

For a kernel `f` of logarithmic growth (`Sb1Gr f A`: measurable, `|f z| ≤ A + log(1+|z|)`) and a weight `φ` with
`φ`, `|φ|·‖y‖` integrable, `sb1_lv_cv f φ x = ∫ φ(y) f(x-y) dy` (so `sb1G k ρ = sb1_lv_cv k ρ`):

* `sb1_lv_cv_int`: the integrand is integrable;
* `sb1_lv_cv_abs_le`: `|cv f φ x| ≤ (A + log(1+|x|)) ∫|φ| + ∫|φ||y|`;
* `sb1_lv_cv_cont`: joint continuity in `(s,x)` of `cv f (φ s) x` for a jointly continuous `φ` with `|φ s y| ≤ a w(y)`;
* `sb1_lv_cv_hasFDerivAt`: the `x`-derivative for a `C¹` kernel with bounded derivative;
* `sb1_lv_cv_lip`: Lipschitz continuity in `x` for a Lipschitz kernel;
* `sb1_lv_ibp_cv`: `∫ρ (∂_j∂_j k)(x-y) = ∫ ∂_jρ ∂_jk(x-y)` (used for the Lipschitz bound of `div ∇G`).
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.MfeConf

variable {d : ℕ}

/-- `∫ φ(y) f(x - y) dy` -/
def sb1_lv_cv (f φ : Euc d → ℝ) (x : Euc d) : ℝ := ∫ y, φ y * f (x - y)

/-- kernels of logarithmic growth -/
def Sb1Gr (f : Euc d → ℝ) (A : ℝ) : Prop := Measurable f ∧ ∀ z, |f z| ≤ A + Real.log (1 + ‖z‖)

theorem Sb1Gr.A_nonneg {f : Euc d → ℝ} {A : ℝ} (h : Sb1Gr f A) : 0 ≤ A := by
  have := h.2 0
  simp at this
  exact (abs_nonneg _).trans this

theorem sb1_lv_pt_bound {f : Euc d → ℝ} {A : ℝ} (h : Sb1Gr f A) (x y : Euc d) :
    |f (x - y)| ≤ (A + Real.log (1 + ‖x‖)) + ‖y‖ := by
  have h1 := h.2 (x - y)
  have h2 := sb1_log_sub x y
  have h3 := sb1_log_le_norm y
  linarith

theorem sb1_lv_cv_int {f φ : Euc d → ℝ} {A : ℝ} (hf : Sb1Gr f A) (hm : AEStronglyMeasurable φ volume)
    (h1 : Integrable φ) (h2 : Integrable (fun y => |φ y| * ‖y‖)) (x : Euc d) :
    Integrable (fun y => φ y * f (x - y)) := by
  have hb : Integrable (fun y => |φ y| * (A + Real.log (1 + ‖x‖)) + |φ y| * ‖y‖) :=
    (h1.abs.mul_const _).add h2
  refine hb.mono' (hm.mul (hf.1.comp (measurable_const.sub measurable_id)).aestronglyMeasurable)
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have := mul_le_mul_of_nonneg_left (sb1_lv_pt_bound hf x y) (abs_nonneg (φ y))
  linarith

theorem sb1_lv_cv_abs_le {f φ : Euc d → ℝ} {A : ℝ} (hf : Sb1Gr f A) (hm : AEStronglyMeasurable φ volume)
    (h1 : Integrable φ) (h2 : Integrable (fun y => |φ y| * ‖y‖)) (x : Euc d) :
    |sb1_lv_cv f φ x| ≤ (A + Real.log (1 + ‖x‖)) * (∫ y, |φ y|) + ∫ y, |φ y| * ‖y‖ := by
  unfold sb1_lv_cv
  have hb : Integrable (fun y => |φ y| * (A + Real.log (1 + ‖x‖)) + |φ y| * ‖y‖) :=
    (h1.abs.mul_const _).add h2
  have hpt : ∀ y, ‖φ y * f (x - y)‖ ≤ |φ y| * (A + Real.log (1 + ‖x‖)) + |φ y| * ‖y‖ := fun y => by
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have := mul_le_mul_of_nonneg_left (sb1_lv_pt_bound hf x y) (abs_nonneg (φ y))
    linarith
  have := norm_integral_le_of_norm_le hb (Eventually.of_forall hpt)
  rw [Real.norm_eq_abs, integral_add (h1.abs.mul_const _) h2, integral_mul_const] at this
  exact this.trans (le_of_eq (by ring))

/-- Joint continuity of the convolution in the parameter and the point. -/
theorem sb1_lv_cv_cont {f : Euc d → ℝ} {A : ℝ} (hf : Sb1Gr f A) (hfc : Continuous f) {φ : ℝ → Euc d → ℝ}
    (hφc : Continuous (Function.uncurry φ)) {a : ℝ} (hd : 1 ≤ d)
    (hφb : ∀ s y, |φ s y| ≤ a * sb1w ((d : ℝ) + 2) y) :
    Continuous (Function.uncurry fun s x => sb1_lv_cv f (φ s) x) := by
  rw [continuous_iff_continuousAt]
  rintro ⟨s₀, x₀⟩
  have hw := sb1w_int hd (p := (d : ℝ) + 2) (by linarith)
  have hwm := sb1w_mom hd
  have ha : 0 ≤ a := by
    have := (abs_nonneg (φ 0 0)).trans (hφb 0 0)
    have h2 : 0 < sb1w ((d : ℝ) + 2) (0 : Euc d) := sb1w_pos _ _
    by_contra hneg
    push Not at hneg
    nlinarith
  set R : ℝ := A + Real.log (2 + ‖x₀‖) with hR
  have hA := hf.A_nonneg
  have hlog : 0 ≤ Real.log (2 + ‖x₀‖) := Real.log_nonneg (by linarith [norm_nonneg x₀])
  refine continuousAt_of_dominated (bound := fun y => a * sb1w ((d : ℝ) + 2) y * (R + ‖y‖)) ?_ ?_ ?_ ?_
  · refine Eventually.of_forall fun p => ?_
    exact ((hφc.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable (μ := volume)).mul
      (hf.1.comp (measurable_const.sub measurable_id)).aestronglyMeasurable
  · have hn : {p : ℝ × Euc d | ‖p.2 - x₀‖ < 1} ∈ 𝓝 (s₀, x₀) :=
      (isOpen_lt (continuous_norm.comp (continuous_snd.sub continuous_const)) continuous_const).mem_nhds
        (by simp)
    filter_upwards [hn] with p hp
    refine Eventually.of_forall fun y => ?_
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    have hxp : ‖p.2‖ ≤ ‖x₀‖ + 1 := by
      have := norm_le_norm_add_norm_sub' p.2 x₀
      have h2 : ‖p.2 - x₀‖ < 1 := hp
      linarith
    have hlp : Real.log (1 + ‖p.2‖) ≤ Real.log (2 + ‖x₀‖) :=
      Real.log_le_log (by positivity) (by linarith)
    have h1 := sb1_lv_pt_bound hf p.2 y
    calc |φ p.1 y| * |f (p.2 - y)| ≤ (a * sb1w ((d : ℝ) + 2) y) * (R + ‖y‖) :=
          mul_le_mul (hφb p.1 y) (by linarith) (abs_nonneg _) (mul_nonneg ha (sb1w_pos _ _).le)
      _ = _ := rfl
  · have := (hw.const_mul (a * R)).add (hwm.const_mul a)
    refine this.congr (Eventually.of_forall fun y => ?_)
    simp only [Pi.add_apply]
    ring
  · refine Eventually.of_forall fun y => ?_
    exact (hφc.comp (continuous_fst.prodMk continuous_const)).continuousAt.mul
      (hfc.comp (continuous_snd.sub continuous_const)).continuousAt

end HRS.MS.MfeConf
