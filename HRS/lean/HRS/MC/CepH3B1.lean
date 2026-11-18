import HRS.MC.CepH3A2

/-!
# Packet CEPH3, part B1: resolvent facts from the Yosida structure

For `cep_Yosida 1 N J`: `G n z := n • (z - J n z) = ∇Φ (J n z)`, `J n` is nonexpansive on the alcove side,
`‖G n z‖ ≤ ‖∇Φ z‖` for `z ∈ A`, the Moreau representation of the envelope and local uniform convergence.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepH3

open HRS HRS.MC.Cepa

variable {N : ℕ} {J : ℝ → Ch N → Ch N}

lemma h3b_force (hJ : cep_Yosida 1 N J) {n : ℝ} (hn : 0 < n) (z : Ch N) :
    h3a_gam (J n z) = n • (z - J n z) := by
  rw [← h3a_gradient_eq (hJ.mem n z hn), ← hJ.force n z hn]

/-- The resolvent is nonexpansive. -/
lemma h3b_J_nonexp (hJ : cep_Yosida 1 N J) {n : ℝ} (hn : 0 < n) (z z' : Ch N) :
    ‖J n z - J n z'‖ ≤ ‖z - z'‖ := by
  have hmono := h3a_gam_mono (hJ.mem n z' hn) (hJ.mem n z hn)
  rw [h3b_force hJ hn z, h3b_force hJ hn z'] at hmono
  -- ⟪n(z - Jz) - n(z' - Jz'), Jz - Jz'⟫ ≥ 0
  set a := J n z with ha
  set b := J n z' with hb
  have h1 : ⟪n • (z - a) - n • (z' - b), a - b⟫ = n * ⟪(z - z') - (a - b), a - b⟫ := by
    rw [← smul_sub, real_inner_smul_left]; congr 2; abel
  rw [h1] at hmono
  have h2 : 0 ≤ ⟪(z - z') - (a - b), a - b⟫ := by
    by_contra h
    push_neg at h
    nlinarith
  rw [inner_sub_left] at h2
  have h3 : ‖a - b‖ ^ 2 ≤ ⟪z - z', a - b⟫ := by
    rw [real_inner_self_eq_norm_sq] at h2; linarith
  have h4 : ⟪z - z', a - b⟫ ≤ ‖z - z'‖ * ‖a - b‖ := real_inner_le_norm _ _
  by_contra hcon
  push_neg at hcon
  have : ‖z - z'‖ * ‖a - b‖ < ‖a - b‖ ^ 2 := by
    have hpos : 0 < ‖a - b‖ := lt_of_le_of_lt (norm_nonneg _) hcon
    nlinarith
  linarith

/-- `‖G n z‖ ≤ ‖∇Φ z‖` for `z` in the alcove. -/
lemma h3b_G_le (hJ : cep_Yosida 1 N J) {n : ℝ} (hn : 0 < n) {z : Ch N} (hz : z ∈ cep_Alcove N) :
    ‖n • (z - J n z)‖ ≤ ‖h3a_gam z‖ := by
  have hmono := h3a_gam_mono hz (hJ.mem n z hn)
  rw [h3b_force hJ hn z] at hmono
  set a := J n z with ha
  set g := n • (z - a) with hg
  have hz' : a - z = -(n⁻¹ • g) := by
    rw [hg, smul_smul, inv_mul_cancel₀ hn.ne', one_smul]; abel
  rw [hz', inner_neg_right, inner_sub_left] at hmono
  simp only [real_inner_smul_right] at hmono
  have h1 : ‖g‖ ^ 2 ≤ ⟪h3a_gam z, g⟫ := by
    have : 0 ≤ n⁻¹ * (⟪h3a_gam z, g⟫ - ‖g‖ ^ 2) := by
      rw [← real_inner_self_eq_norm_sq]
      nlinarith [hmono]
    have h' : 0 ≤ ⟪h3a_gam z, g⟫ - ‖g‖ ^ 2 := by
      by_contra hneg; push_neg at hneg
      have := mul_neg_of_pos_of_neg (inv_pos.mpr hn) hneg
      linarith
    linarith
  have h2 : ⟪h3a_gam z, g⟫ ≤ ‖h3a_gam z‖ * ‖g‖ := real_inner_le_norm _ _
  by_contra hcon
  push_neg at hcon
  have hpos : 0 < ‖g‖ := lt_of_le_of_lt (norm_nonneg _) hcon
  nlinarith

/-- A quadratic remainder bound gives a gradient. -/
lemma h3b_hasGradientAt_of_quad {f : Ch N → ℝ} {g z : Ch N} {C : ℝ}
    (hq : ∀ z', |f z' - f z - ⟪g, z' - z⟫| ≤ C * ‖z' - z‖ ^ 2) : HasGradientAt f g z := by
  show HasFDerivAt f (InnerProductSpace.toDual ℝ (Ch N) g) z
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  refine Asymptotics.isLittleO_iff.mpr fun c hc => ?_
  have hev : ∀ᶠ h in 𝓝 (0 : Ch N), ‖h‖ < c / (|C| + 1) :=
    Metric.eventually_nhds_iff.mpr ⟨c / (|C| + 1), by positivity, fun h hh => by simpa using hh⟩
  filter_upwards [hev] with h hh
  have h1 := hq (z + h)
  simp only [add_sub_cancel_left] at h1
  have e : f (z + h) - f z - (InnerProductSpace.toDual ℝ (Ch N) g) h = f (z + h) - f z - ⟪g, h⟫ := by
    simp [InnerProductSpace.toDual_apply_apply]
  simp only [Real.norm_eq_abs, e]
  have hnn := norm_nonneg h
  calc |f (z + h) - f z - ⟪g, h⟫| ≤ C * ‖h‖ ^ 2 := h1
    _ ≤ |C| * ‖h‖ * ‖h‖ := by nlinarith [le_abs_self C]
    _ ≤ c * ‖h‖ := by
        have : |C| * ‖h‖ ≤ c := by
          have h2 : (|C| + 1) * ‖h‖ ≤ c := by
            have := mul_lt_mul_of_pos_left hh (show (0:ℝ) < |C| + 1 by positivity)
            rw [mul_div_cancel₀ _ (by positivity)] at this
            exact this.le
          nlinarith
        exact mul_le_mul_of_nonneg_right this hnn

end HRS.MC.CepH3
