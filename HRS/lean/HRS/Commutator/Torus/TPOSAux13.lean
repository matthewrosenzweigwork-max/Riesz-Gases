import HRS.Commutator.Torus.TPOSAux12
import HRS.PDE.MeanFieldAux

/-!
# T-POS helpers, part 13: the local structure of `g_η^𝕋` near the origin

`g_η^𝕋(y) = r(y) + A_η(y) - tScale ∑_{m≠0} f_η(y+m) + tScale ∫ perio f_η` for `0 < |y| < δ`
(local singularity of `periodicRiesz`, `g_1` smooth), hence the continuous extension `tposGloc`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s η : ℝ}

lemma tpos_mk_eq_zero {y : Euc d} (h : Torus.mk y = 0) : ∃ m : Lattice d, y = Lattice.toEuc m := by
  have : ∀ i, ∃ n : ℤ, (n : ℝ) = y i := by
    intro i
    have hi := congrFun h i
    simp only [Torus.mk] at hi
    obtain ⟨n, hn⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp hi
    exact ⟨n, by simpa using hn⟩
  choose m hm using this
  exact ⟨m, by ext i; simp [Lattice.toEuc, hm]⟩

lemma tpos_mk_ne_zero_small {y : Euc d} (hy0 : y ≠ 0) (hy1 : ‖y‖ < 1) : Torus.mk y ≠ 0 := by
  intro h
  obtain ⟨m, hm⟩ := tpos_mk_eq_zero h
  by_cases hm0 : m = 0
  · apply hy0; rw [hm, hm0]; ext i; simp [Lattice.toEuc]
  · have := one_le_enorm m hm0
    have h2 : ‖y‖ = ‖Lattice.toEuc m‖ := by rw [hm]
    have h3 : Lattice.enorm m = ‖Lattice.toEuc m‖ := rfl
    linarith

lemma tpos_isOpen_mk_ne : IsOpen {y : Euc d | Torus.mk y ≠ 0} :=
  (isOpen_compl_singleton (x := (0 : Torus d))).preimage Torus.continuous_mk

lemma tpos_mk_add_toEuc (y : Euc d) (m : Lattice d) : Torus.mk (y + Lattice.toEuc m) = Torus.mk y := by
  rw [Torus.mk_add, Torus.mk_toEuc, add_zero]

lemma tpos_lift_gTorus (y : Euc d) (hy : Torus.mk y ≠ 0) :
    gTorus s η (Torus.mk y) = periodicRiesz d s (Torus.mk y) -
      tScale s * (∑' m : Lattice d, Whole.fTrunc s η (y + Lattice.toEuc m) -
        ∫ x : Torus d, perio (Whole.fTrunc s η : Euc d → ℝ) x) := by
  unfold gTorus fTorus
  rw [if_neg hy, tpos_perio_mk]

/-- `tScale · f_η` near the origin in terms of the smooth function `g_1`. -/
lemma tpos_sing_formula (hη : 0 < η) {y : Euc d} (hy : y ≠ 0) :
    tScale s * Whole.fTrunc s η y =
      (if s = 0 then -Real.log ‖y‖ else ‖y‖ ^ (-s)) -
        (tScale s * η ^ (-s) * Whole.g1 s (η⁻¹ • y) - (if s = 0 then Real.log η else 0)) := by
  have hz : η⁻¹ • y ≠ 0 := smul_ne_zero (inv_ne_zero hη.ne') hy
  have hyn : 0 < ‖y‖ := norm_pos_iff.2 hy
  have hzn : ‖η⁻¹ • y‖ = ‖y‖ / η := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hη, inv_mul_eq_div]
  have hg : Whole.fTrunc s 1 (η⁻¹ • y) = Whole.kern s (η⁻¹ • y) - Whole.g1 s (η⁻¹ • y) := by
    simp only [Whole.g1, if_neg hz]; ring
  rw [tpos_fTrunc_scale hη y, hg]
  unfold Whole.kern
  rw [hzn]
  by_cases hs : s = 0
  · subst hs
    simp only [tScale, if_true, neg_zero, Real.rpow_zero, one_mul]
    rw [Real.log_div hyn.ne' hη.ne']
    ring
  · simp only [tScale, hs, if_false]
    have h1 : η ^ (-s) * (s⁻¹ * (‖y‖ / η) ^ (-s)) = s⁻¹ * ‖y‖ ^ (-s) := by
      rw [Real.div_rpow hyn.le hη.le, Real.rpow_neg hη.le]
      field_simp
    have : s * (η ^ (-s) * (s⁻¹ * (‖y‖ / η) ^ (-s) - Whole.g1 s (η⁻¹ • y))) =
        ‖y‖ ^ (-s) - s * η ^ (-s) * Whole.g1 s (η⁻¹ • y) := by
      have hs' : s ≠ 0 := hs
      calc s * (η ^ (-s) * (s⁻¹ * (‖y‖ / η) ^ (-s) - Whole.g1 s (η⁻¹ • y)))
          = s * (η ^ (-s) * (s⁻¹ * (‖y‖ / η) ^ (-s))) - s * η ^ (-s) * Whole.g1 s (η⁻¹ • y) := by ring
        _ = _ := by rw [h1]; field_simp
    rw [this]; simp

open Classical in
/-- The local expression of `g_η^𝕋` near `0` (continuous). -/
def tposGloc (s η : ℝ) (r : Torus d → ℝ) (y : Euc d) : ℝ :=
  r (Torus.mk y) + (tScale s * η ^ (-s) * Whole.g1 s (η⁻¹ • y) - (if s = 0 then Real.log η else 0)) -
    tScale s * ∑' m : Lattice d, (if m = 0 then 0 else Whole.fTrunc s η (y + Lattice.toEuc m)) +
    tScale s * ∫ x : Torus d, perio (Whole.fTrunc s η : Euc d → ℝ) x

lemma tpos_local_eq (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (hη : 0 < η)
    (r : Torus d → ℝ) (δ : ℝ)
    (hsing : ∀ x : Euc d, ‖x‖ < δ → x ≠ 0 → periodicRiesz d s (Torus.mk x) =
      (if s = 0 then -Real.log ‖x‖ else ‖x‖ ^ (-s)) + r (Torus.mk x))
    {y : Euc d} (hy0 : y ≠ 0) (hyδ : ‖y‖ < δ) (hy1 : ‖y‖ < 1) :
    gTorus s η (Torus.mk y) = tposGloc s η r y := by
  classical
  rw [tpos_lift_gTorus y (tpos_mk_ne_zero_small hy0 hy1), hsing y hyδ hy0]
  have hsum := tpos_fTrunc_summable hs0 hsd hη y
  have h1 := hsum.tsum_eq_add_tsum_ite 0
  have h0 : Lattice.toEuc (0 : Lattice d) = 0 := by ext i; simp [Lattice.toEuc]
  rw [h0, add_zero] at h1
  have h2 := tpos_sing_formula (s := s) hη hy0
  unfold tposGloc
  rw [h1]
  try simp only [h0]
  linarith

end HRS.Commutator.TorusNote
