import HRS.MS.SA16SEn1

/-!
# S.A.16 (SA16S) En2: the commutator `[∂^idx, b·∇]` (packet P7, step 3)

`sa16sy_transport_split`: for smooth `φ` and coefficients `b_l` smooth with `‖D^i b_l‖ ≤ B` for `i ≤ j`,
`|∂^idx (∑ b_l ∂_l φ)(x) - ∑ b_l(x) ∂_l (∂^idx φ)(x)| ≤ d 2^j B (d+1)^j ‖wJet j φ (x)‖`  (`|idx| = j`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section En2
variable {d : ℕ}

lemma sa16sy_pd_add {f g : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) {j : ℕ}
    (idx : Fin j → Fin d) (x : Euc d) :
    partialDeriv idx (fun y => f y + g y) x = partialDeriv idx f x + partialDeriv idx g x := by
  unfold partialDeriv
  have := iteratedFDeriv_add_apply (𝕜 := ℝ) (i := j) (x := x) (f := f) (g := g)
    (hf.contDiffAt.of_le (by exact_mod_cast le_top)) (hg.contDiffAt.of_le (by exact_mod_cast le_top))
  rw [show (fun y => f y + g y) = f + g from rfl, this]
  rfl

lemma sa16sy_pd_cmul {g : Euc d → ℝ} (hg : ContDiff ℝ ∞ g) (c : ℝ) {j : ℕ}
    (idx : Fin j → Fin d) (x : Euc d) :
    partialDeriv idx (fun y => c * g y) x = c * partialDeriv idx g x := by
  unfold partialDeriv
  have := iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (i := j) (x := x) (a := c) (f := g)
    (hg.contDiffAt.of_le (by exact_mod_cast le_top))
  rw [show (fun y => c * g y) = c • g from rfl, this]
  rfl

lemma sa16sy_comm_term {k : ℕ} {B : ℝ} {b : Euc d → ℝ} (hbs : ContDiff ℝ ∞ b)
    (hbb : ∀ i ≤ k, ∀ y, ‖iteratedFDeriv ℝ i b y‖ ≤ B) {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ) (l : Fin d)
    {j : ℕ} (hj : j ≤ k) (idx : Fin j → Fin d) (x : Euc d) :
    |partialDeriv idx (fun y => (b y - b x) * fderiv ℝ φ y (EuclideanSpace.single l 1)) x| ≤
      2 ^ j * (B * ((d : ℝ) + 1) ^ j) * ‖wJet j φ x‖ := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hbb 0 (Nat.zero_le _) x)
  have hJ0 := norm_nonneg (wJet j φ x)
  have hcs : ContDiff ℝ ∞ (fun y => b y - b x) := hbs.sub contDiff_const
  have hgs := sa16so_dir_smooth hφ (EuclideanSpace.single l 1)
  refine (sa16y_pd_le_iter _ x idx).trans ?_
  have hL := norm_iteratedFDeriv_mul_le (𝕜 := ℝ) (hcs.of_le (by exact_mod_cast le_top))
    (hgs.of_le (by exact_mod_cast le_top)) x (n := j) (N := (j : ℕ∞ω)) le_rfl
  refine hL.trans ?_
  have hterm : ∀ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y => b y - b x) x‖ *
      ‖iteratedFDeriv ℝ (j - i) (fun y => fderiv ℝ φ y (EuclideanSpace.single l 1)) x‖ ≤
      (j.choose i : ℝ) * (B * (((d : ℝ) + 1) ^ j * ‖wJet j φ x‖)) := by
    intro i hi
    have hi' : i ≤ j := by have := Finset.mem_range.1 hi; omega
    have hc : (0 : ℝ) ≤ j.choose i := Nat.cast_nonneg _
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      simp only [norm_iteratedFDeriv_zero, sub_self, norm_zero, mul_zero, zero_mul]
      positivity
    · have h1 : ‖iteratedFDeriv ℝ i (fun y => b y - b x) x‖ ≤ B := by
        have := iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := i) (x := x) (f := b) (g := fun _ => b x)
          (hbs.contDiffAt.of_le (by exact_mod_cast le_top)) (contDiff_const.contDiffAt.of_le (by exact_mod_cast le_top))
        rw [show (fun y => b y - b x) = b - fun _ => b x from rfl, this,
          iteratedFDeriv_const_of_ne (by omega : i ≠ 0)]
        simpa using hbb i (hi'.trans hj) x
      have h2 := sa16so_norm_iter_dir hφ (EuclideanSpace.single l 1) (j - i) x
      rw [PiLp.norm_single, norm_one, one_mul] at h2
      have h3 := sa16y_iter_le_jet φ x (n := j) (l := j - i + 1) (by omega)
      have h4 : ((d : ℝ)) ^ (j - i + 1) ≤ ((d : ℝ) + 1) ^ j := by
        calc ((d : ℝ)) ^ (j - i + 1) ≤ ((d : ℝ) + 1) ^ (j - i + 1) :=
              pow_le_pow_left₀ (Nat.cast_nonneg d) (by linarith) _
          _ ≤ ((d : ℝ) + 1) ^ j :=
              pow_le_pow_right₀ (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith) (by omega)
      have h5 : ‖iteratedFDeriv ℝ (j - i) (fun y => fderiv ℝ φ y (EuclideanSpace.single l 1)) x‖ ≤
          ((d : ℝ) + 1) ^ j * ‖wJet j φ x‖ :=
        h2.trans (h3.trans (mul_le_mul_of_nonneg_right h4 hJ0))
      calc (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun y => b y - b x) x‖ *
            ‖iteratedFDeriv ℝ (j - i) (fun y => fderiv ℝ φ y (EuclideanSpace.single l 1)) x‖
          ≤ (j.choose i : ℝ) * B * (((d : ℝ) + 1) ^ j * ‖wJet j φ x‖) :=
            mul_le_mul (mul_le_mul_of_nonneg_left h1 hc) h5 (norm_nonneg _) (mul_nonneg hc hB0)
        _ = _ := by ring
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_mul]
  have hsum : ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) = 2 ^ j := by
    exact_mod_cast Nat.sum_range_choose j
  rw [hsum]
  exact le_of_eq (by ring)

lemma sa16sy_transport_split {k : ℕ} {B : ℝ} {bc : Fin d → Euc d → ℝ} (hb : SA16BddCoef k B bc)
    {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ) {j : ℕ} (hj : j ≤ k) (idx : Fin j → Fin d) (x : Euc d) :
    |partialDeriv idx (sa16so_transportFun bc φ) x -
        ∑ l, bc l x * fderiv ℝ (partialDeriv idx φ) x (EuclideanSpace.single l 1)| ≤
      (d : ℝ) * (2 ^ j * (B * ((d : ℝ) + 1) ^ j) * ‖wJet j φ x‖) := by
  have hg : ∀ l : Fin d, ContDiff ℝ ∞ (fun y => fderiv ℝ φ y (EuclideanSpace.single l 1)) :=
    fun l => sa16so_dir_smooth hφ _
  have hsplit : ∀ l : Fin d, partialDeriv idx (fun y => bc l y * fderiv ℝ φ y (EuclideanSpace.single l 1)) x =
      partialDeriv idx (fun y => (bc l y - bc l x) * fderiv ℝ φ y (EuclideanSpace.single l 1)) x +
        bc l x * fderiv ℝ (partialDeriv idx φ) x (EuclideanSpace.single l 1) := by
    intro l
    have e1 : (fun y => bc l y * fderiv ℝ φ y (EuclideanSpace.single l 1)) =
        fun y => (bc l y - bc l x) * fderiv ℝ φ y (EuclideanSpace.single l 1) +
          bc l x * fderiv ℝ φ y (EuclideanSpace.single l 1) := by
      funext y; ring
    rw [e1, sa16sy_pd_add ((hb.smooth l).sub contDiff_const |>.mul (hg l)) (contDiff_const.mul (hg l)),
      sa16sy_pd_cmul (hg l)]
    have := congrFun (sa16sy_pd_comm hφ l idx) x
    rw [this]
  have hT : sa16so_transportFun bc φ = fun y => ∑ l : Fin d, bc l y * fderiv ℝ φ y (EuclideanSpace.single l 1) := rfl
  rw [hT, sa16sy_pd_sum Finset.univ (fun l _ => (hb.smooth l).mul (hg l))]
  simp_rw [hsplit]
  rw [Finset.sum_add_distrib, add_sub_cancel_right]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ l : Fin d, |partialDeriv idx (fun y => (bc l y - bc l x) * fderiv ℝ φ y (EuclideanSpace.single l 1)) x|
      ≤ ∑ l : Fin d, 2 ^ j * (B * ((d : ℝ) + 1) ^ j) * ‖wJet j φ x‖ :=
        Finset.sum_le_sum fun l _ => sa16sy_comm_term (hb.smooth l) (fun i hi y => hb.bound l i hi y) hφ l hj idx x
    _ = _ := by simp

end En2

end HRS.Whole.AppendixA.Phase2SA16R
