import HRS.MD.EQLZSgSemigroup
import HRS.PDE.TorusFPEntropyClassicalAux1
import HRS.PDE.TorusFPCompareAux2

/-!
# EQ-LZ packet SG-4: invariance of the Gibbs measure under `P_t` (`eqlz_sg_invariant`), proof

`∫ g dπ = c ∫ g G dx` with a constant `c` independent of `g` (`d3a_exists_c`), and `∫ f_0 G = ∫ φ G` for a classical
backward solution (`d1c_stationary`); `P_t φ = f 0` for the solution on `[0, t]` (`d1_P_eq`).
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS

namespace HRS.MD.EQLZSgInvariant

variable {n : ℕ}

/-- (SG-4, `eqlz_sg_invariant`.)  Statement copied verbatim from `HRS.MD.EQLZ.eqlz_sg_invariant`. -/
theorem eqlz_sg_invariant_proof (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U) {t : ℝ}
    (ht : 0 ≤ t) {φ : Torus n → ℝ} (hφ : Torus.IsSmooth φ) :
    ∫ x, d1_P hn hκ hU t φ x ∂(d1_gibbsMeasure κ U) = ∫ x, φ x ∂(d1_gibbsMeasure κ U) := by
  rcases ht.eq_or_lt with h0 | hpos
  · subst h0
    rw [HRS.MD.EQLZSgSemigroup.eqlzsg_P_zero hn hκ hU]
  · obtain ⟨c, hc⟩ := d3a_exists_c (κ := κ) (U := U) hU
    obtain ⟨f, hf⟩ := d1_backward_classical hn hκ hU hpos hφ
    have hP : ∀ x, d1_P hn hκ hU t φ x = f 0 x := by
      intro x
      rw [d1_P_eq hn hκ hU hpos hφ hf ⟨ht, le_rfl⟩ x]
      simp
    rw [hc, hc]
    congr 1
    simp_rw [hP]
    exact d1c_stationary hκ hU hpos hf

end HRS.MD.EQLZSgInvariant

end
