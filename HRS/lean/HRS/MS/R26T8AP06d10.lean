import HRS.MS.R26T8AP06b

/-!
# S8.2 local Newton layer, packet T8A.P06d (part 10): joint-jet differences bounded by nested-jet differences
`r26t8a_joint_diff_le`: for `Phi` of class `C^j`, `|D^j Phi (X,z) - D^j Phi (X,z')| <= sum_q C(j,q) |nest (j-q) q Phi X z - nest (j-q) q Phi X z'|`.
Proof: apply `r26t8a_joint_le_nest` (P06b) to the difference of the two `z`-translates of `Phi` at `(X,0)`.
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ContDiff

namespace HRS.MS.R26T8A

section D

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem r26t8a_nest_shift (p q : ℕ) (Φ : E × E → V) (X z : E) :
    r26t8a_nest p q (fun Yw : E × E => Φ (Yw.1, Yw.2 + z)) X 0 = r26t8a_nest p q Φ X z := by
  unfold r26t8a_nest
  congr 1
  funext Y
  rw [iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := fun w => Φ (Y, w)) q z 0, zero_add]

theorem r26t8a_joint_shift (j : ℕ) (Φ : E × E → V) (X z : E) :
    iteratedFDeriv ℝ j (fun w : E × E => Φ (w.1, w.2 + z)) (X, 0) = iteratedFDeriv ℝ j Φ (X, z) := by
  have : (fun w : E × E => Φ (w.1, w.2 + z)) = fun w => Φ (w + (0, z)) := by
    funext w; congr 1; exact Prod.ext (by simp) (by simp)
  rw [this, iteratedFDeriv_comp_add_right]
  congr 1; exact Prod.ext (by simp) (by simp)

theorem r26t8a_nest_sub (p q : ℕ) (z X : E) {Φ Ψ : E × E → V}
    (hΦ : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) Φ) (hΨ : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) Ψ) :
    r26t8a_nest p q (fun Yw => Φ Yw - Ψ Yw) X z = r26t8a_nest p q Φ X z - r26t8a_nest p q Ψ X z := by
  unfold r26t8a_nest
  have hq : (q : WithTop ℕ∞) ≤ ((p + q : ℕ) : WithTop ℕ∞) := by exact_mod_cast Nat.le_add_left q p
  have h : (fun Y => iteratedFDeriv ℝ q (fun w => Φ (Y, w) - Ψ (Y, w)) z) =
      (fun Y => iteratedFDeriv ℝ q (fun w => Φ (Y, w)) z) - (fun Y => iteratedFDeriv ℝ q (fun w => Ψ (Y, w)) z) := by
    funext Y
    exact fun_iteratedFDeriv_sub_apply
      (((hΦ.of_le hq).comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ (q : WithTop ℕ∞) fun w : E => (Y, w))).contDiffAt)
      (((hΨ.of_le hq).comp (contDiff_const.prodMk contDiff_id : ContDiff ℝ (q : WithTop ℕ∞) fun w : E => (Y, w))).contDiffAt)
  rw [h]
  exact iteratedFDeriv_sub_apply
    ((r26t8a_nest_contDiff q p Φ z hΦ).of_le (le_refl _) |>.contDiffAt)
    ((r26t8a_nest_contDiff q p Ψ z hΨ).of_le (le_refl _) |>.contDiffAt)

theorem r26t8a_joint_diff_le (j : ℕ) {Φ : E × E → V} (hΦ : ContDiff ℝ (j : WithTop ℕ∞) Φ) (X z z' : E) :
    ‖iteratedFDeriv ℝ j Φ (X, z) - iteratedFDeriv ℝ j Φ (X, z')‖ ≤
      ∑ q ∈ Finset.range (j + 1), (j.choose q : ℝ) *
        ‖r26t8a_nest (j - q) q Φ X z - r26t8a_nest (j - q) q Φ X z'‖ := by
  have hs : ∀ c : E, ContDiff ℝ (j : WithTop ℕ∞) (fun w : E × E => Φ (w.1, w.2 + c)) := fun c =>
    hΦ.comp (contDiff_fst.prodMk (contDiff_snd.add contDiff_const))
  have hD : ContDiff ℝ (j : WithTop ℕ∞) (fun w : E × E => Φ (w.1, w.2 + z) - Φ (w.1, w.2 + z')) :=
    (hs z).sub (hs z')
  have key := r26t8a_joint_le_nest j (fun w : E × E => Φ (w.1, w.2 + z) - Φ (w.1, w.2 + z')) X 0 hD
  have e1 : iteratedFDeriv ℝ j (fun w : E × E => Φ (w.1, w.2 + z) - Φ (w.1, w.2 + z')) (X, 0) =
      iteratedFDeriv ℝ j Φ (X, z) - iteratedFDeriv ℝ j Φ (X, z') := by
    rw [fun_iteratedFDeriv_sub_apply (hs z).contDiffAt (hs z').contDiffAt, r26t8a_joint_shift, r26t8a_joint_shift]
  rw [e1] at key
  refine key.trans (le_of_eq (Finset.sum_congr rfl fun q hq => ?_))
  have hq' : q ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hq)
  have hc : ∀ c : E, ContDiff ℝ (((j - q) + q : ℕ) : WithTop ℕ∞) (fun w : E × E => Φ (w.1, w.2 + c)) := fun c => by
    rw [Nat.sub_add_cancel hq']; exact hs c
  rw [r26t8a_nest_sub (j - q) q 0 X (hc z) (hc z'), r26t8a_nest_shift, r26t8a_nest_shift]

end D

end HRS.MS.R26T8A
