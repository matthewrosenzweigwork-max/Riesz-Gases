import Mathlib
import HRS.MS.S82WJ1

/-!
# S8.2 A04 (S82W), part 2: the cut-off profile and jets of squared coordinate maps
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ContDiff

namespace HRS.MS.S82W

/-- the cut-off profile: `1` on `s ≤ 1`, `0` on `s ≥ 2` -/
def wc (s : ℝ) : ℝ := Real.smoothTransition (2 - s)

lemma wc_contDiff : ContDiff ℝ ∞ wc := by
  have h : ContDiff ℝ ∞ (fun s : ℝ => 2 - s) := contDiff_const.sub contDiff_id
  exact Real.smoothTransition.contDiff.comp h

lemma wc_one {s : ℝ} (h : s ≤ 1) : wc s = 1 := Real.smoothTransition.one_of_one_le (by linarith)

lemma wc_zero {s : ℝ} (h : 2 ≤ s) : wc s = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)

lemma wc_nonneg (s : ℝ) : 0 ≤ wc s := Real.smoothTransition.nonneg _

lemma wc_le_one (s : ℝ) : wc s ≤ 1 := Real.smoothTransition.le_one _

/-- a cut-off profile with derivative bound `B`, supported (as to derivatives) in `[1,2]` -/
def IsCut (ch : ℝ → ℝ) (B : ℝ) : Prop :=
  ContDiff ℝ 2 ch ∧ 0 ≤ B ∧ (∀ s, 0 ≤ ch s ∧ ch s ≤ 1) ∧
  (∀ s, s ∉ Set.Icc (1 : ℝ) 2 → deriv ch s = 0 ∧ deriv (deriv ch) s = 0) ∧
  ∀ s, |deriv ch s| ≤ B ∧ |deriv (deriv ch) s| ≤ B

lemma wc_loc_const {s : ℝ} (hs : s ∉ Set.Icc (1 : ℝ) 2) : ∃ k : ℝ, wc =ᶠ[𝓝 s] fun _ => k := by
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hs
  rcases hs with h | h
  · refine ⟨1, ?_⟩
    filter_upwards [Iio_mem_nhds h] with y hy using wc_one (le_of_lt hy)
  · refine ⟨0, ?_⟩
    filter_upwards [Ioi_mem_nhds h] with y hy using wc_zero (le_of_lt hy)

lemma wc_deriv_zero {s : ℝ} (hs : s ∉ Set.Icc (1 : ℝ) 2) : deriv wc s = 0 ∧ deriv (deriv wc) s = 0 := by
  have h1 : ∀ y, y ∉ Set.Icc (1 : ℝ) 2 → deriv wc y = 0 := by
    intro y hy
    obtain ⟨k, hk⟩ := wc_loc_const hy
    rw [hk.deriv_eq]; simp
  refine ⟨h1 s hs, ?_⟩
  have : deriv wc =ᶠ[𝓝 s] fun _ => (0 : ℝ) := by
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hs] with y hy using h1 y hy
  rw [this.deriv_eq]; simp

lemma exists_isCut : ∃ B : ℝ, IsCut wc B ∧ IsCut (fun s => 1 - wc s) B := by
  have h1 : ContDiff ℝ ∞ (deriv wc) := (contDiff_infty_iff_deriv.1 wc_contDiff).2
  have c1 : Continuous (deriv wc) := h1.continuous
  have c2 : Continuous (deriv (deriv wc)) := (h1.continuous_deriv (by simp))
  obtain ⟨B1, hB1⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 2)).exists_bound_of_continuousOn c1.continuousOn
  obtain ⟨B2, hB2⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 2)).exists_bound_of_continuousOn c2.continuousOn
  set B := max 0 (max B1 B2) with hB
  have hB0 : 0 ≤ B := le_max_left _ _
  have hbd : ∀ s, |deriv wc s| ≤ B ∧ |deriv (deriv wc) s| ≤ B := by
    intro s
    by_cases hs : s ∈ Set.Icc (1 : ℝ) 2
    · refine ⟨?_, ?_⟩
      · have := hB1 s hs; rw [Real.norm_eq_abs] at this
        exact this.trans ((le_max_left _ _).trans (le_max_right _ _))
      · have := hB2 s hs; rw [Real.norm_eq_abs] at this
        exact this.trans ((le_max_right _ _).trans (le_max_right _ _))
    · obtain ⟨a, b⟩ := wc_deriv_zero hs
      rw [a, b]; simpa using hB0
  have hd2 : ContDiff ℝ 2 wc := wc_contDiff.of_le (by norm_num)
  refine ⟨B, ⟨hd2, hB0, fun s => ⟨wc_nonneg s, wc_le_one s⟩, fun s hs => wc_deriv_zero hs, hbd⟩, ?_⟩
  have hder : ∀ s, deriv (fun s => 1 - wc s) s = -deriv wc s := by
    intro s
    have : DifferentiableAt ℝ wc s := (wc_contDiff.differentiable (by simp)) s
    rw [deriv_const_sub]
  have hder' : deriv (fun s => 1 - wc s) = fun s => -deriv wc s := funext hder
  have hder2 : ∀ s, deriv (deriv fun s => 1 - wc s) s = -deriv (deriv wc) s := by
    intro s; rw [hder']; exact deriv.fun_neg
  refine ⟨contDiff_const.sub hd2, hB0, fun s => ⟨by linarith [wc_le_one s], by linarith [wc_nonneg s]⟩, ?_, ?_⟩
  · intro s hs
    obtain ⟨a, b⟩ := wc_deriv_zero hs
    rw [hder, hder2, a, b]; simp
  · intro s
    rw [hder, hder2, abs_neg, abs_neg]; exact hbd s

section sq
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma wk_clm_jets (L : E →L[ℝ] F) (x : E) :
    ‖iteratedFDeriv ℝ 0 (fun y => L y) x‖ = ‖L x‖ ∧ ‖iteratedFDeriv ℝ 1 (fun y => L y) x‖ = ‖L‖ ∧
      ‖iteratedFDeriv ℝ 2 (fun y => L y) x‖ = 0 := by
  have hfd : fderiv ℝ (fun y => L y) = fun _ => L := funext fun y => L.fderiv
  refine ⟨norm_iteratedFDeriv_zero, ?_, ?_⟩
  · rw [norm_iteratedFDeriv_one, L.fderiv]
  · have := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := fun y => L y) (x := x) (n := 1)
    rw [norm_iteratedFDeriv_one, hfd] at this
    rw [← this]
    simp

/-- jets of `x ↦ ‖L x‖²` -/
lemma wk_sq_jets (L : E →L[ℝ] F) :
    ContDiff ℝ 2 (fun x => ‖L x‖ ^ 2) ∧ ∀ x, ‖fderiv ℝ (fun y => ‖L y‖ ^ 2) x‖ ≤ 2 * ‖L‖ * ‖L x‖ ∧
      ‖fderiv ℝ (fderiv ℝ (fun y => ‖L y‖ ^ 2)) x‖ ≤ 2 * ‖L‖ ^ 2 := by
  have hg : (fun y => ‖L y‖ ^ 2) = fun y => (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ) (L y) (L y) := by
    funext y; simp [real_inner_self_eq_norm_sq]
  rw [hg]
  refine ⟨(innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ).isBoundedBilinearMap.contDiff.comp (L.contDiff.prodMk L.contDiff), fun x => ?_⟩
  have hB : ‖(innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ)‖ ≤ 1 := norm_innerSL_le ℝ
  have h1 := (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ).norm_iteratedFDeriv_le_of_bilinear (f := fun y => L y)
    (g := fun y => L y) (N := 2) L.contDiff L.contDiff x (n := 1) (by norm_num)
  have h2 := (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ).norm_iteratedFDeriv_le_of_bilinear (f := fun y => L y)
    (g := fun y => L y) (N := 2) L.contDiff L.contDiff x (n := 2) le_rfl
  obtain ⟨a0, a1, a2⟩ := wk_clm_jets L x
  simp only [Finset.sum_range_succ, Finset.range_zero, Finset.sum_empty, zero_add, Nat.choose, Nat.cast_one,
    Nat.cast_ofNat, Nat.reduceSub, a0, a1, a2] at h1 h2
  have e1 : ‖iteratedFDeriv ℝ 1 (fun y => (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ) (L y) (L y)) x‖ =
      ‖fderiv ℝ (fun y => (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ) (L y) (L y)) x‖ := norm_iteratedFDeriv_one _
  have e2 : ‖iteratedFDeriv ℝ 2 (fun y => (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ) (L y) (L y)) x‖ =
      ‖fderiv ℝ (fderiv ℝ (fun y => (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ) (L y) (L y))) x‖ := w_j2 _ x
  rw [e1] at h1
  rw [e2] at h2
  have n1 := norm_nonneg L
  have n2 := norm_nonneg (L x)
  have n3 := norm_nonneg (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ)
  norm_num at h1 h2 ⊢
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.2 hB) (mul_nonneg n1 n2)]
  · nlinarith [mul_nonneg (sub_nonneg.2 hB) (mul_nonneg n1 n1)]

end sq

end HRS.MS.S82W
