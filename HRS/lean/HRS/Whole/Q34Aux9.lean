import HRS.Whole.Q34Aux8

/-!
# Packet Q34, helper file 9: the resolvent of a bounded nonnegative symmetric operator
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric InnerProductSpace
open scoped ENNReal NNReal

namespace HRS.Whole.Q34

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Cauchy-Schwarz for a nonnegative symmetric operator: `‖Kh‖² ≤ M ⟨Kh, h⟩`. -/
theorem sq_norm_le_of_pos (K : H →L[ℝ] H)
    (hsymm : ∀ x y, inner ℝ (K x) y = inner ℝ x (K y)) (hpos : ∀ x, 0 ≤ inner ℝ (K x) x)
    {Mg : ℝ} (hMg0 : 0 ≤ Mg) (hMg : ∀ x, ‖K x‖ ≤ Mg * ‖x‖) (h : H) :
    ‖K h‖ ^ 2 ≤ Mg * inner ℝ (K h) h := by
  set w : H := K h with hw
  set q : ℝ := inner ℝ (K h) h with hq
  set b : ℝ := ‖w‖ ^ 2 with hb
  set a : ℝ := inner ℝ (K w) w with ha
  have hq0 : 0 ≤ q := hpos h
  have ha0 : 0 ≤ a := hpos w
  have hquad : ∀ t : ℝ, 0 ≤ a * (t * t) + (2 * b) * t + q := by
    intro t
    have h1 := hpos (h + t • w)
    have e1 : inner ℝ (K (h + t • w)) (h + t • w) = a * (t * t) + (2 * b) * t + q := by
      rw [map_add, map_smul, inner_add_left, inner_add_right, inner_add_right, inner_smul_left,
        inner_smul_left, inner_smul_right, inner_smul_right]
      have e2 : inner ℝ (K w) h = b := by
        rw [hsymm w h, hb, ← real_inner_self_eq_norm_sq]
      have e3 : inner ℝ (K h) w = b := by
        rw [hb, ← real_inner_self_eq_norm_sq]
      simp only [conj_trivial]
      rw [e2, e3]
      ring
    linarith
  have hdisc := discrim_le_zero hquad
  unfold discrim at hdisc
  have hab : a ≤ Mg * b := by
    calc a = inner ℝ (K w) w := rfl
      _ ≤ ‖K w‖ * ‖w‖ := real_inner_le_norm _ _
      _ ≤ (Mg * ‖w‖) * ‖w‖ := by gcongr; exact hMg w
      _ = Mg * b := by rw [hb]; ring
  have hb0 : 0 ≤ b := by positivity
  have hbb : b * b ≤ Mg * b * q := by
    have : b * b ≤ a * q := by nlinarith
    calc b * b ≤ a * q := this
      _ ≤ (Mg * b) * q := by gcongr
  show b ≤ Mg * q
  rcases hb0.eq_or_lt with h0 | hpos'
  · rw [← h0]; positivity
  · have : b * b ≤ (Mg * q) * b := by nlinarith
    exact le_of_mul_le_mul_right this hpos'

/-- Existence, uniqueness and bounds for `h + βKh = f`. -/
theorem resolvent_exists (K : H →L[ℝ] H)
    (hsymm : ∀ x y, inner ℝ (K x) y = inner ℝ x (K y)) (hpos : ∀ x, 0 ≤ inner ℝ (K x) x)
    {Mg : ℝ} (hMg0 : 0 ≤ Mg) (hMg : ∀ x, ‖K x‖ ≤ Mg * ‖x‖) {β : ℝ} (hβ : 0 < β) (f : H) :
    ∃ h : H, h + β • K h = f ∧ (∀ h', h' + β • K h' = f → h' = h) ∧
      ‖f‖ ^ 2 / (1 + β * Mg) ≤ inner ℝ f h ∧ inner ℝ f h ≤ ‖f‖ ^ 2 ∧ ‖h‖ ≤ ‖f‖ := by
  set A : H →L[ℝ] H := ContinuousLinearMap.id ℝ H + β • K with hA
  have hAapp : ∀ x, A x = x + β • K x := fun x => by simp [hA]
  let B : H →L[ℝ] H →L[ℝ] ℝ := (innerSL ℝ : H →L[ℝ] H →L[ℝ] ℝ).comp A
  have hB : ∀ v w, B v w = inner ℝ (A v) w := fun v w => rfl
  have hcoer : IsCoercive B := by
    refine ⟨1, one_pos, fun u => ?_⟩
    rw [hB, hAapp, inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq]
    have := hpos u
    simp only [conj_trivial]
    nlinarith [mul_nonneg hβ.le this]
  set e := hcoer.continuousLinearEquivOfBilin with he
  have heA : ∀ v, e v = A v := by
    intro v
    refine ext_inner_right ℝ fun w => ?_
    rw [he, IsCoercive.continuousLinearEquivOfBilin_apply, hB]
  set h := e.symm f with hh
  have hAh : h + β • K h = f := by
    rw [← hAapp, ← heA, hh, ContinuousLinearEquiv.apply_symm_apply]
  refine ⟨h, hAh, ?_, ?_⟩
  · intro h' hh'
    have : e h' = e h := by
      rw [heA, heA, hAapp, hAapp, hh', hAh]
    exact e.injective this
  · set q : ℝ := inner ℝ (K h) h with hq
    set b : ℝ := ‖K h‖ ^ 2 with hb
    have hq0 : 0 ≤ q := hpos h
    have hb0 : 0 ≤ b := by positivity
    have hfh : inner ℝ f h = ‖h‖ ^ 2 + β * q := by
      conv_lhs => rw [← hAh]
      rw [inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq]
      simp only [conj_trivial]
      rfl
    have hff : ‖f‖ ^ 2 = ‖h‖ ^ 2 + 2 * β * q + β ^ 2 * b := by
      rw [← real_inner_self_eq_norm_sq]
      conv_lhs => rw [← hAh]
      rw [inner_add_left, inner_add_right, inner_add_right, inner_smul_left, inner_smul_left,
        inner_smul_right, inner_smul_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
      have : inner ℝ h (K h) = q := by rw [hq, real_inner_comm]
      rw [this]
      simp only [conj_trivial]
      rw [hb]
      ring
    have hup : inner ℝ f h ≤ ‖f‖ ^ 2 := by
      rw [hfh, hff]
      nlinarith [mul_nonneg hβ.le hq0, mul_nonneg (sq_nonneg β) hb0]
    have hlow : ‖f‖ ^ 2 / (1 + β * Mg) ≤ inner ℝ f h := by
      have hpos1 : 0 < 1 + β * Mg := by positivity
      rw [div_le_iff₀ hpos1]
      have h1 : b ≤ Mg * q := sq_norm_le_of_pos K hsymm hpos hMg0 hMg h
      have h2 : q ≤ Mg * ‖h‖ ^ 2 := by
        calc q = inner ℝ (K h) h := rfl
          _ ≤ ‖K h‖ * ‖h‖ := real_inner_le_norm _ _
          _ ≤ (Mg * ‖h‖) * ‖h‖ := by gcongr; exact hMg h
          _ = Mg * ‖h‖ ^ 2 := by ring
      rw [hfh, hff]
      nlinarith [mul_nonneg hβ.le hq0, mul_nonneg (sq_nonneg β) hb0,
        mul_le_mul_of_nonneg_left h1 (sq_nonneg β), mul_le_mul_of_nonneg_left h2 hβ.le]
    refine ⟨hlow, hup, ?_⟩
    have hhh : ‖h‖ ^ 2 ≤ ‖f‖ ^ 2 := by
      have : ‖h‖ ^ 2 ≤ inner ℝ f h := by rw [hfh]; nlinarith [mul_nonneg hβ.le hq0]
      linarith
    exact (sq_le_sq₀ (norm_nonneg h) (norm_nonneg f)).1 hhh

end Hilbert

end HRS.Whole.Q34
