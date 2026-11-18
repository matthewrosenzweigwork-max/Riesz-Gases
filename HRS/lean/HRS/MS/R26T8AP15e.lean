import HRS.MS.R26T8AP15f

/-!
# S8.2 T8A P15e: coefficients `alpha(x)`, `alpha(x) + alpha(y)`, `alpha(x) - alpha(y)` for the product lemma
For `alpha ∈ C^(k+1)` with `‖D^j alpha(x)‖ ≤ B jb(x)` for `j ≤ k+1` (e.g. a coordinate of the drift `-forceMean - a x`):
* `r26t8a_conormal_mul_xw`: `alpha(x) G(x,y)` is `Conormal k b (M+1) σ`;
* `r26t8a_conormal_mul_sum`: `(alpha(x) + alpha(y)) G(x,y)` is `Conormal k b (M+1) σ`;
* `r26t8a_conormal_mul_diff`: `(alpha(x) - alpha(y)) G(x,y)` is `Conormal k b (M+1) (σ-1)` (the separation factor).
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_nest_shift_bound_w {l : ℝ} (hl : |l| ≤ 1) {k : ℕ} {α : Euc d → ℝ}
    (hα : ContDiff ℝ (k : WithTop ℕ∞) α) (Bw : Euc d → ℝ)
    (hab : ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j α x‖ ≤ Bw x) {i j : ℕ} (hij : i + j ≤ k) (X z : Euc d) :
    ‖r26t8a_nest i j (fun Yw : Euc d × Euc d => α (Yw.1 + l • Yw.2)) X z‖ ≤ Bw (X + l • z) := by
  set Ψa : Euc d × Euc d → ℝ := fun Yw => α Yw.1 with hΨa
  have hΨ : ContDiff ℝ ((i + j : ℕ) : WithTop ℕ∞) Ψa :=
    (hα.comp contDiff_fst).of_le (by exact_mod_cast hij)
  have h := r26t8a_shear l i j Ψa hΨ X z
  refine h.trans ?_
  rw [Finset.sum_eq_single j]
  · rw [Nat.sub_self, Nat.choose_self, Nat.cast_one, one_mul, r26t8a_nest_zero]
    have : ‖iteratedFDeriv ℝ (i + j) (fun Y => Ψa (Y, z)) (X + l • z)‖ ≤ Bw (X + l • z) := hab _ hij _
    have hl' : |l| ^ j ≤ 1 := pow_le_one₀ (abs_nonneg _) hl
    calc _ ≤ 1 * ‖iteratedFDeriv ℝ (i + j) (fun Y => Ψa (Y, z)) (X + l • z)‖ :=
          mul_le_mul_of_nonneg_right hl' (norm_nonneg _)
      _ ≤ Bw (X + l • z) := by rw [one_mul]; exact this
  · intro t ht htj
    have : j - t ≠ 0 := by have := Finset.mem_range.1 ht; omega
    rw [r26t8a_nest_const_w this, norm_zero, mul_zero]
  · intro hj; exact absurd (Finset.mem_range.2 (Nat.lt_succ_self j)) hj

theorem r26t8a_jb_mul_ge (x y : Euc d) : jbracket x ≤ jbracket x * jbracket y := by
  have := r26t8a_one_le_jb y
  have h0 := r26t8a_one_le_jb x
  nlinarith

theorem r26t8a_jb_add_le (x y : Euc d) : jbracket x + jbracket y ≤ 2 * (jbracket x * jbracket y) := by
  have h1 := r26t8a_one_le_jb y
  have h0 := r26t8a_one_le_jb x
  nlinarith

theorem r26t8a_jb_mono {u x : Euc d} (h : ‖u‖ ≤ ‖x‖) : jbracket u ≤ jbracket x := by
  unfold jbracket
  exact Real.sqrt_le_sqrt (by nlinarith [norm_nonneg u])

/-- Coefficient `alpha(x)` as a function of centre/relative variables. -/
def r26t8a_cX (α : Euc d → ℝ) (Yw : Euc d × Euc d) : ℝ := α (Yw.1 + (1 / 2 : ℝ) • Yw.2)
def r26t8a_cY (α : Euc d → ℝ) (Yw : Euc d × Euc d) : ℝ := α (Yw.1 + (-(1 / 2 : ℝ)) • Yw.2)

theorem r26t8a_cpair_cX (α : Euc d → ℝ) (x y : Euc d) : r26t8a_cpair (r26t8a_cX α) x y = α x := by
  unfold r26t8a_cpair r26t8a_cX
  congr 1; module

theorem r26t8a_cpair_cY (α : Euc d → ℝ) (x y : Euc d) : r26t8a_cpair (r26t8a_cY α) x y = α y := by
  unfold r26t8a_cpair r26t8a_cY
  congr 1; module

theorem r26t8a_cX_contDiff {k : ℕ} {α : Euc d → ℝ} (hα : ContDiff ℝ (k : WithTop ℕ∞) α) :
    ContDiff ℝ (k : WithTop ℕ∞) (r26t8a_cX α) :=
  hα.comp (contDiff_fst.add (contDiff_snd.const_smul (1 / 2 : ℝ)))

theorem r26t8a_cY_contDiff {k : ℕ} {α : Euc d → ℝ} (hα : ContDiff ℝ (k : WithTop ℕ∞) α) :
    ContDiff ℝ (k : WithTop ℕ∞) (r26t8a_cY α) :=
  hα.comp (contDiff_fst.add (contDiff_snd.const_smul (-(1 / 2 : ℝ))))

theorem r26t8a_nest_cX {k : ℕ} {α : Euc d → ℝ} (hα : ContDiff ℝ (k : WithTop ℕ∞) α) {B : ℝ}
    (hab : ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j α x‖ ≤ B * jbracket x) {i j : ℕ} (hij : i + j ≤ k) (X z : Euc d) :
    ‖r26t8a_nest i j (r26t8a_cX α) X z‖ ≤ B * jbracket (X + (1 / 2 : ℝ) • z) :=
  r26t8a_nest_shift_bound_w (l := 1 / 2) (by norm_num [abs_of_pos]) hα (fun x => B * jbracket x) hab hij X z

theorem r26t8a_nest_cY {k : ℕ} {α : Euc d → ℝ} (hα : ContDiff ℝ (k : WithTop ℕ∞) α) {B : ℝ}
    (hab : ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j α x‖ ≤ B * jbracket x) {i j : ℕ} (hij : i + j ≤ k) (X z : Euc d) :
    ‖r26t8a_nest i j (r26t8a_cY α) X z‖ ≤ B * jbracket (X + (-(1 / 2 : ℝ)) • z) :=
  r26t8a_nest_shift_bound_w (l := -(1 / 2)) (by norm_num [abs_neg, abs_of_pos]) hα (fun x => B * jbracket x) hab hij X z

theorem r26t8a_jb_pair (X z : Euc d) :
    jbracket (X + (1 / 2 : ℝ) • z) + jbracket (X + (-(1 / 2 : ℝ)) • z) ≤
      2 * HRS.MS.Phase2S82.pairWeight 1 (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) := by
  have e : X + (-(1 / 2 : ℝ)) • z = X - (1 / 2 : ℝ) • z := by module
  rw [e]
  simp only [HRS.MS.Phase2S82.pairWeight, Real.rpow_one]
  exact r26t8a_jb_add_le _ _

theorem r26t8a_jb_x_pair (X z : Euc d) :
    jbracket (X + (1 / 2 : ℝ) • z) ≤ HRS.MS.Phase2S82.pairWeight 1 (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) := by
  simp only [HRS.MS.Phase2S82.pairWeight, Real.rpow_one]
  exact r26t8a_jb_mul_ge _ _

/-- sum coefficient -/
def r26t8a_cP (α : Euc d → ℝ) (Yw : Euc d × Euc d) : ℝ := r26t8a_cX α Yw + r26t8a_cY α Yw
def r26t8a_cM (α : Euc d → ℝ) (Yw : Euc d × Euc d) : ℝ := r26t8a_cX α Yw - r26t8a_cY α Yw

theorem r26t8a_cpair_cP (α : Euc d → ℝ) (x y : Euc d) : r26t8a_cpair (r26t8a_cP α) x y = α x + α y := by
  unfold r26t8a_cP
  show r26t8a_cpair (r26t8a_cX α) x y + r26t8a_cpair (r26t8a_cY α) x y = _
  rw [r26t8a_cpair_cX, r26t8a_cpair_cY]

theorem r26t8a_cpair_cM (α : Euc d → ℝ) (x y : Euc d) : r26t8a_cpair (r26t8a_cM α) x y = α x - α y := by
  unfold r26t8a_cM
  show r26t8a_cpair (r26t8a_cX α) x y - r26t8a_cpair (r26t8a_cY α) x y = _
  rw [r26t8a_cpair_cX, r26t8a_cpair_cY]

theorem r26t8a_nest_cP {k : ℕ} {α : Euc d → ℝ} (hα : ContDiff ℝ (k : WithTop ℕ∞) α) {B : ℝ}
    (hab : ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j α x‖ ≤ B * jbracket x) (hB : 0 ≤ B) {i j : ℕ} (hij : i + j ≤ k)
    (X z : Euc d) :
    ‖r26t8a_nest i j (r26t8a_cP α) X z‖ ≤ 2 * B * HRS.MS.Phase2S82.pairWeight 1 (X + (1 / 2 : ℝ) • z)
      (X - (1 / 2 : ℝ) • z) := by
  have hcx : ContDiff ℝ ((i + j : ℕ) : WithTop ℕ∞) (r26t8a_cX α) :=
    (r26t8a_cX_contDiff hα).of_le (by exact_mod_cast hij)
  have hcy : ContDiff ℝ ((i + j : ℕ) : WithTop ℕ∞) (r26t8a_cY α) :=
    (r26t8a_cY_contDiff hα).of_le (by exact_mod_cast hij)
  have e : r26t8a_cP α = fun Yw => r26t8a_cX α Yw + r26t8a_cY α Yw := rfl
  rw [e, r26t8a_nest_add i j z X hcx hcy]
  refine (norm_add_le _ _).trans ?_
  have h1 := r26t8a_nest_cX hα hab hij X z
  have h2 := r26t8a_nest_cY hα hab hij X z
  have h3 := r26t8a_jb_pair X z
  nlinarith

theorem r26t8a_nest_cM_pos {k : ℕ} {α : Euc d → ℝ} (hα : ContDiff ℝ (k : WithTop ℕ∞) α) {B : ℝ}
    (hab : ∀ j ≤ k, ∀ x, ‖iteratedFDeriv ℝ j α x‖ ≤ B * jbracket x) (hB : 0 ≤ B) {i j : ℕ} (hij : i + j ≤ k)
    (X z : Euc d) :
    ‖r26t8a_nest i j (r26t8a_cM α) X z‖ ≤ 2 * B * HRS.MS.Phase2S82.pairWeight 1 (X + (1 / 2 : ℝ) • z)
      (X - (1 / 2 : ℝ) • z) := by
  have hcx : ContDiff ℝ ((i + j : ℕ) : WithTop ℕ∞) (r26t8a_cX α) :=
    (r26t8a_cX_contDiff hα).of_le (by exact_mod_cast hij)
  have hcy : ContDiff ℝ ((i + j : ℕ) : WithTop ℕ∞) (r26t8a_cY α) :=
    (r26t8a_cY_contDiff hα).of_le (by exact_mod_cast hij)
  set L : ℝ →L[ℝ] ℝ := -(ContinuousLinearMap.id ℝ ℝ) with hLdef
  have hLn : ∀ v : ℝ, ‖L v‖ ≤ ‖v‖ := fun v => by simp [hLdef]
  have e : r26t8a_cM α = fun Yw => r26t8a_cX α Yw + L (r26t8a_cY α Yw) := by
    funext Yw; simp [r26t8a_cM, hLdef, sub_eq_add_neg]
  have hLc : ContDiff ℝ ((i + j : ℕ) : WithTop ℕ∞) (fun Yw => L (r26t8a_cY α Yw)) := L.contDiff.comp hcy
  rw [e, r26t8a_nest_add i j z X hcx hLc]
  refine (norm_add_le _ _).trans ?_
  have h1 := r26t8a_nest_cX hα hab hij X z
  have h2 := (r26t8a_nest_clm' L hLn i j (r26t8a_cY α) X z hcy).trans (r26t8a_nest_cY hα hab hij X z)
  have h3 := r26t8a_jb_pair X z
  nlinarith

end HRS.MS.R26T8A
