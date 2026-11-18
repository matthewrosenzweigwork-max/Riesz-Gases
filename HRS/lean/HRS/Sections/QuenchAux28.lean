import HRS.Sections.QuenchAux27

/-!
# Packet QUENCH (Q27), part 28: asymptotics of the window tensors (parts (iii), (iv) of Prop. 7.13)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Qch

open HRS.Sec7

variable {d : ℕ} {m T : ℝ} {s β β₀ : ℝ}

/-- the `k`-th mode path -/
abbrev mpk (d : ℕ) (s β m T : ℝ) (k : PosHalf d) (b : Bool) : PathSpace d m T :=
  modePath m T (lamMode d s β k.1) (modeFn k.1 b)

/-- the `k`-th coefficient tensor applied to `M` -/
def ckM (d : ℕ) (s β β₀ m T : ℝ) (M : PathSpace d m T [×2]→L[ℝ] ℝ) (k : PosHalf d) : ℝ :=
  deltaVar d s β β₀ k.1 * (M ![mpk d s β m T k true, mpk d s β m T k true] +
    M ![mpk d s β m T k false, mpk d s β m T k false])

/-- the weight `|δv_k|(‖f_{kψ}‖² + ‖f_{kχ}‖²)` -/
def wk (d : ℕ) (s β β₀ m T : ℝ) (k : PosHalf d) : ℝ :=
  |deltaVar d s β β₀ k.1| * (‖mpk d s β m T k true‖ ^ 2 + ‖mpk d s β m T k false‖ ^ 2)

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)

lemma summable_jp_posHalf (hm : (d : ℝ) / 2 + 1 < m) :
    Summable fun k : PosHalf d => Lattice.jp k.1 ^ (-(2 * m)) := by
  have h := summable_jp_rpow (d := d) m (by linarith)
  have hinj : Function.Injective fun k : PosHalf d => idx k true := fun k k' h =>
    congrArg Prod.fst (idx_injective (p := (k, true)) (q := (k', true)) h)
  exact (h.comp_injective hinj).congr fun k => by simp [idx]

include hd hs0 hsd hβ in
lemma wk_le (hβ₀ : 0 < β₀) (hT : 0 < T) (k : PosHalf d) :
    wk d s β β₀ m T k ≤ 2 * Lattice.jp k.1 ^ (-(2 * m)) := by
  have h1 := abs_deltaVar_le hd hs0 hsd hβ hβ₀ ⟨k.1, ne_zero_of_posHalf k.2⟩
  have hl := (lamMode_pos' hd hs0 hsd hβ k).le
  have h2 := norm_modePath_le (m := m) (T := T) (s := s) (β := β) k true hl rfl
  have h3 := norm_modePath_le (m := m) (T := T) (s := s) (β := β) k false hl rfl
  have hj : 0 ≤ Lattice.jp k.1 ^ (-m) := Real.rpow_nonneg (Torus.jp_pos _).le _
  have e : (Lattice.jp k.1 ^ (-m)) ^ 2 = Lattice.jp k.1 ^ (-(2 * m)) := by
    rw [Torus.jp_rpow_sq]; congr 1; ring
  unfold wk
  have h4 : ‖mpk d s β m T k true‖ ^ 2 ≤ (Lattice.jp k.1 ^ (-m)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
  have h5 : ‖mpk d s β m T k false‖ ^ 2 ≤ (Lattice.jp k.1 ^ (-m)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
  have h6 : |deltaVar d s β β₀ k.1| ≤ 1 := h1
  calc |deltaVar d s β β₀ k.1| * (‖mpk d s β m T k true‖ ^ 2 + ‖mpk d s β m T k false‖ ^ 2)
      ≤ 1 * ((Lattice.jp k.1 ^ (-m)) ^ 2 + (Lattice.jp k.1 ^ (-m)) ^ 2) :=
        mul_le_mul h6 (add_le_add h4 h5) (by positivity) zero_le_one
    _ = _ := by rw [e]; ring

include hd hs0 hsd hβ in
lemma summable_wk (hβ₀ : 0 < β₀) (hm : (d : ℝ) / 2 + 1 < m) (hT : 0 < T) :
    Summable (wk d s β β₀ m T) :=
  Summable.of_nonneg_of_le (fun k => by unfold wk; positivity) (wk_le hd hs0 hsd hβ hβ₀ hT)
    ((summable_jp_posHalf hm).mul_left 2)

include hd hs0 hsd hβ in
lemma summable_stmt (hβ₀ : 0 < β₀) (hm : (d : ℝ) / 2 + 1 < m) (hT : 0 < T) {a : ℝ} (ha : 0 ≤ a) :
    Summable (fun k : PosHalf d => |deltaVar d s β β₀ k.1| * Real.exp (-2 * lamMode d s β k.1 * a) *
        (‖modePath m T (lamMode d s β k.1) (modeFn k.1 true)‖ ^ 2 +
          ‖modePath m T (lamMode d s β k.1) (modeFn k.1 false)‖ ^ 2)) := by
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (summable_wk (β₀ := β₀) hd hs0 hsd hβ hβ₀ hm hT)
  have hl := (lamMode_pos' hd hs0 hsd hβ k).le
  have h : Real.exp (-2 * lamMode d s β k.1 * a) ≤ 1 :=
    Real.exp_le_one_iff.2 (by nlinarith)
  unfold wk
  have hq : 0 ≤ ‖mpk d s β m T k true‖ ^ 2 + ‖mpk d s β m T k false‖ ^ 2 := by positivity
  calc |deltaVar d s β β₀ k.1| * Real.exp (-2 * lamMode d s β k.1 * a) *
        (‖mpk d s β m T k true‖ ^ 2 + ‖mpk d s β m T k false‖ ^ 2)
      ≤ |deltaVar d s β β₀ k.1| * 1 * (‖mpk d s β m T k true‖ ^ 2 + ‖mpk d s β m T k false‖ ^ 2) := by
        gcongr
    _ = _ := by ring

lemma abs_ckM_le (M : PathSpace d m T [×2]→L[ℝ] ℝ) (hl : ∀ k : PosHalf d, 0 ≤ lamMode d s β k.1) (k : PosHalf d) :
    |ckM d s β β₀ m T M k| ≤ ‖M‖ * wk d s β β₀ m T k := by
  unfold ckM wk
  have h1 := abs_multi_le M (mpk d s β m T k true) (mpk d s β m T k true)
  have h2 := abs_multi_le M (mpk d s β m T k false) (mpk d s β m T k false)
  rw [abs_mul]
  calc |deltaVar d s β β₀ k.1| * |M ![mpk d s β m T k true, mpk d s β m T k true] +
        M ![mpk d s β m T k false, mpk d s β m T k false]|
      ≤ |deltaVar d s β β₀ k.1| * (‖M‖ * ‖mpk d s β m T k true‖ * ‖mpk d s β m T k true‖ +
          ‖M‖ * ‖mpk d s β m T k false‖ * ‖mpk d s β m T k false‖) := by
        gcongr
        exact (abs_add_le _ _).trans (add_le_add h1 h2)
    _ = _ := by ring

end Qch

end HRS
