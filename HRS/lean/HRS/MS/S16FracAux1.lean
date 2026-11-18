import Mathlib

/-!
# S16-FRAC, part 1: Glaeser's inequality (S.A.16 input E5)

Packet S16-FRAC (CZ development).  Glaeser's inequality (supplement L10351, used to write
`∇μ = 2 √μ ∇√μ` with `∇√μ ∈ L^∞`):

* `s16frac_glaeser`: for a real normed space `E`, `μ : E → ℝ` of class `C²` with `μ ≥ 0` and
  `‖D²μ(y)‖ ≤ M` for all `y` (operator norm of `iteratedFDeriv ℝ 2 μ y`, the quantity entering `cbNorm 2`),
  one has `‖Dμ(x)‖² ≤ 2 M μ(x)` for every `x`.
  Proof: second-order Taylor bound `μ(x + t v) ≤ μ(x) + t Dμ(x) v + M t² ‖v‖²/2` (`t ≥ 0`, one-variable
  monotonicity argument), applied to `±v` and optimised in `t`, then `opNorm_le_bound`.
* `s16frac_glaeser_cb`: the same with the bound `M = ⨆ ‖D²μ‖`, hypothesis `BddAbove` (this is the
  `cbNorm`-type quantity `‖D²μ‖_∞`; the boundedness conjunct rules out the junk value `0` of the real `iSup`).

All hypotheses are real; nothing is a junk value.
-/

open MeasureTheory Filter Topology Set Metric

noncomputable section

namespace HRS.S16Frac

/-- one-variable Taylor bound with bounded second derivative -/
lemma s16frac_taylor1 {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) {M : ℝ}
    (hM : ∀ t, deriv (deriv φ) t ≤ M) {t : ℝ} (ht : 0 ≤ t) :
    φ t ≤ φ 0 + t * deriv φ 0 + M * t ^ 2 / 2 := by
  have hc : Continuous φ := hφ.continuous
  have hd1 : Differentiable ℝ φ := hφ.differentiable (by norm_num)
  have hφ' : ContDiff ℝ 1 (deriv φ) := hφ.iterate_deriv' 1 1
  have hd2 : Differentiable ℝ (deriv φ) := hφ'.differentiable (by norm_num)
  -- g t = φ' t - M t is antitone
  have hg : Antitone fun t => deriv φ t - M * t := by
    refine antitone_of_deriv_nonpos (f := fun t => deriv φ t - M * t) ?_ ?_
    · exact hd2.sub (by fun_prop)
    · intro t
      have : HasDerivAt (fun t => deriv φ t - M * t) (deriv (deriv φ) t - M) t := by
        have h1 := (hd2 t).hasDerivAt
        have h2 : HasDerivAt (fun t : ℝ => M * t) M t := by simpa using (hasDerivAt_id t).const_mul M
        exact h1.sub h2
      rw [this.deriv]
      linarith [hM t]
  -- h t = φ t - φ 0 - t φ'(0) - M t²/2 is antitone on [0, ∞)
  have hh : AntitoneOn (fun t => φ t - φ 0 - t * deriv φ 0 - M * t ^ 2 / 2) (Ici 0) := by
    refine antitoneOn_of_deriv_nonpos (convex_Ici 0) ?_ ?_ ?_
    · exact (Continuous.continuousOn (by fun_prop))
    · exact (Differentiable.differentiableOn (by fun_prop))
    · intro t ht'
      have : HasDerivAt (fun t => φ t - φ 0 - t * deriv φ 0 - M * t ^ 2 / 2)
          (deriv φ t - deriv φ 0 - M * t) t := by
        have h1 := (hd1 t).hasDerivAt
        have h2 : HasDerivAt (fun t : ℝ => t * deriv φ 0) (deriv φ 0) t := by
          simpa using (hasDerivAt_id t).mul_const (deriv φ 0)
        have h3 : HasDerivAt (fun t : ℝ => M * t ^ 2 / 2) (M * t) t := by
          have := ((hasDerivAt_pow 2 t).const_mul M).div_const 2
          convert this using 1
          simp; ring
        have := ((h1.sub_const (φ 0)).sub h2).sub h3
        convert this using 1
      rw [this.deriv]
      have ht'' : 0 < t := by simpa using ht'
      have := hg ht''.le
      simp at this
      linarith
  have := hh (show (0:ℝ) ∈ Ici 0 from by simp) (show t ∈ Ici 0 from ht) ht
  simp at this
  linarith

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Taylor bound along a line for `C²` functions with bounded second derivative -/
lemma s16frac_taylor_line {μ : E → ℝ} (hμ : ContDiff ℝ 2 μ) {M : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 2 μ y‖ ≤ M) (x v : E) {t : ℝ} (ht : 0 ≤ t) :
    μ (x + t • v) ≤ μ x + t * fderiv ℝ μ x v + M * ‖v‖ ^ 2 * t ^ 2 / 2 := by
  set φ : ℝ → ℝ := fun s => μ (x + s • v) with hφdef
  have hline : ∀ s : ℝ, HasDerivAt (fun s : ℝ => x + s • v) v s := by
    intro s
    simpa using ((hasDerivAt_id s).smul_const v).const_add x
  have hμ1 : ContDiff ℝ 1 (fderiv ℝ μ) := hμ.fderiv_right (by norm_num)
  have hline_c : ContDiff ℝ 2 (fun s : ℝ => x + s • v) := by fun_prop
  have hφ : ContDiff ℝ 2 φ := hμ.comp hline_c
  have hd1 : ∀ s, deriv φ s = fderiv ℝ μ (x + s • v) v := by
    intro s
    have h := (hμ.differentiable (by norm_num) (x + s • v)).hasFDerivAt.comp_hasDerivAt s (hline s)
    exact h.deriv
  have hd2 : ∀ s, deriv (deriv φ) s = fderiv ℝ (fderiv ℝ μ) (x + s • v) v v := by
    intro s
    have hfun : deriv φ = fun s => fderiv ℝ μ (x + s • v) v := funext hd1
    rw [hfun]
    have h1 : HasFDerivAt (fderiv ℝ μ) (fderiv ℝ (fderiv ℝ μ) (x + s • v)) (x + s • v) :=
      (hμ1.differentiable (by norm_num) _).hasFDerivAt
    have h2 := h1.comp_hasDerivAt s (hline s)
    have h3 := h2.clm_apply (hasDerivAt_const s v)
    simpa using h3.deriv
  have hbound : ∀ s, deriv (deriv φ) s ≤ M * ‖v‖ ^ 2 := by
    intro s
    rw [hd2]
    have h1 : fderiv ℝ (fderiv ℝ μ) (x + s • v) v v = iteratedFDeriv ℝ 2 μ (x + s • v) ![v, v] := by
      rw [iteratedFDeriv_two_apply]; simp
    rw [h1]
    calc _ ≤ ‖iteratedFDeriv ℝ 2 μ (x + s • v) ![v, v]‖ := le_abs_self _
      _ ≤ ‖iteratedFDeriv ℝ 2 μ (x + s • v)‖ * ∏ i, ‖(![v, v] : Fin 2 → E) i‖ :=
          (iteratedFDeriv ℝ 2 μ (x + s • v)).le_opNorm _
      _ ≤ M * ‖v‖ ^ 2 := by
          simp [Fin.prod_univ_two, sq]
          exact mul_le_mul_of_nonneg_right (hM _) (by positivity)
  have := s16frac_taylor1 hφ hbound ht
  simp only [hφdef, zero_smul, add_zero] at this
  rw [hd1 0] at this
  simpa [hφdef] using this

/-- **Glaeser's inequality**: `μ ≥ 0` of class `C²` with `‖D²μ‖ ≤ M` everywhere has `‖Dμ(x)‖² ≤ 2 M μ(x)`. -/
theorem s16frac_glaeser {μ : E → ℝ} (hμ : ContDiff ℝ 2 μ) (hpos : ∀ y, 0 ≤ μ y) {M : ℝ}
    (hM : ∀ y, ‖iteratedFDeriv ℝ 2 μ y‖ ≤ M) (x : E) :
    ‖fderiv ℝ μ x‖ ^ 2 ≤ 2 * M * μ x := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM x)
  -- for each unit vector: (Dμ v)² ≤ 2 M μ(x) ‖v‖²
  have key : ∀ v : E, (fderiv ℝ μ x v) ^ 2 ≤ 2 * M * μ x * ‖v‖ ^ 2 := by
    intro v
    -- for every `w` (take `w = ±v`) and `t ≥ 0`: `0 ≤ μ x + t Dμ(x) w + M ‖w‖² t²/2`
    have h1 : ∀ w : E, ∀ t : ℝ, 0 ≤ t → 0 ≤ μ x + t * fderiv ℝ μ x w + M * ‖w‖ ^ 2 * t ^ 2 / 2 := by
      intro w t ht
      exact le_trans (hpos _) (s16frac_taylor_line hμ hM x w ht)
    -- pick `w = -sign · v` so that `Dμ(x) w = -|Dμ(x) v|`
    obtain ⟨w, hw, hwn⟩ : ∃ w : E, fderiv ℝ μ x w = -|fderiv ℝ μ x v| ∧ ‖w‖ = ‖v‖ := by
      rcases le_total 0 (fderiv ℝ μ x v) with h | h
      · exact ⟨-v, by simp [abs_of_nonneg h], by simp⟩
      · exact ⟨v, by simp [abs_of_nonpos h], rfl⟩
    set a := |fderiv ℝ μ x v| with ha
    have ha0 : 0 ≤ a := abs_nonneg _
    have hsq : (fderiv ℝ μ x v) ^ 2 = a ^ 2 := (sq_abs _).symm
    rw [hsq]
    have h2 : ∀ t : ℝ, 0 ≤ t → 0 ≤ μ x - t * a + M * ‖v‖ ^ 2 * t ^ 2 / 2 := by
      intro t ht
      have := h1 w t ht
      rw [hw, hwn] at this
      linarith
    set N := M * ‖v‖ ^ 2 with hN
    have hN0 : 0 ≤ N := by positivity
    rcases hN0.eq_or_lt with hN' | hN'
    · -- `N = 0`: `a t ≤ μ x` for all `t ≥ 0`, so `a = 0`
      have : a = 0 := by
        by_contra hne
        have hapos : 0 < a := lt_of_le_of_ne ha0 (Ne.symm hne)
        have := h2 ((μ x + 1) / a) (by have := hpos x; positivity)
        rw [← hN'] at this
        have e : (μ x + 1) / a * a = μ x + 1 := by field_simp
        nlinarith [e]
      rw [this]
      have : 0 ≤ 2 * M * μ x * ‖v‖ ^ 2 := by have := hpos x; positivity
      simpa using this
    · have := h2 (a / N) (by positivity)
      have e1 : a / N * a = a ^ 2 / N := by ring
      have e2 : N * (a / N) ^ 2 / 2 = a ^ 2 / N / 2 := by field_simp
      have e3 : M * ‖v‖ ^ 2 * (a / N) ^ 2 / 2 = a ^ 2 / N / 2 := by rw [← hN]; exact e2
      rw [e3, e1] at this
      have h4 : a ^ 2 / N ≤ 2 * μ x := by linarith
      rw [div_le_iff₀ hN'] at h4
      calc a ^ 2 ≤ 2 * μ x * N := h4
        _ = 2 * M * μ x * ‖v‖ ^ 2 := by rw [hN]; ring
  have hnn : 0 ≤ Real.sqrt (2 * M * μ x) := Real.sqrt_nonneg _
  have hop : ‖fderiv ℝ μ x‖ ≤ Real.sqrt (2 * M * μ x) := by
    refine ContinuousLinearMap.opNorm_le_bound _ hnn fun v => ?_
    have hv := key v
    have h2 : |fderiv ℝ μ x v| ≤ Real.sqrt (2 * M * μ x) * ‖v‖ := by
      have : |fderiv ℝ μ x v| ≤ Real.sqrt (2 * M * μ x * ‖v‖ ^ 2) :=
        Real.abs_le_sqrt hv
      rwa [Real.sqrt_mul (by have := hpos x; positivity), Real.sqrt_sq (norm_nonneg _)] at this
    simpa using h2
  have := pow_le_pow_left₀ (norm_nonneg _) hop 2
  rwa [Real.sq_sqrt (by have := hpos x; positivity)] at this

/-- Glaeser with the supremum form `‖D²μ‖_∞ = ⨆ ‖D²μ‖` (`BddAbove` makes it the true supremum). -/
theorem s16frac_glaeser_cb {μ : E → ℝ} (hμ : ContDiff ℝ 2 μ) (hpos : ∀ y, 0 ≤ μ y)
    (hbdd : BddAbove (Set.range fun y => ‖iteratedFDeriv ℝ 2 μ y‖)) (x : E) :
    ‖fderiv ℝ μ x‖ ^ 2 ≤ 2 * (⨆ y, ‖iteratedFDeriv ℝ 2 μ y‖) * μ x :=
  s16frac_glaeser hμ hpos (fun y => le_ciSup hbdd y) x

end

end HRS.S16Frac
