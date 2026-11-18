import HRS.MS.R26T8AP21c

/-!
# S8.2 local Newton layer, packet T8A.P21 (part d): contraction chain and nested jets of `u_n`
`contr G (Y,w) = (G (Y,w)).curryLeft w` lowers the multilinear arity; `u_n(tau)(Y,w) = D^n f(Y + tau w)(w,...,w)` is the `n`-fold
contraction of `D^n f (Y + tau w)`.  Nested Leibniz (`r26t8a_nest_bilinear`) gives, for `|z| <= 1`, `|nest p q u_4| <= A (q+1)^4 |z|^(4-q)`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

section Chain

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

abbrev r26t8a_Mult (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) : Type :=
  ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ

def r26t8a_contrCLM (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (n : ℕ) :
    E →L[ℝ] r26t8a_Mult E (n + 1) →L[ℝ] r26t8a_Mult E n :=
  ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ).toContinuousLinearEquiv :
    r26t8a_Mult E (n + 1) →L[ℝ] (E →L[ℝ] r26t8a_Mult E n)).flip

theorem r26t8a_contrCLM_apply (n : ℕ) (v : E) (m : r26t8a_Mult E (n + 1)) :
    r26t8a_contrCLM E n v m = m.curryLeft v := rfl

theorem r26t8a_clm_norm_le_one {F1 F2 F3 : Type} [NormedAddCommGroup F1] [NormedSpace ℝ F1]
    [NormedAddCommGroup F2] [NormedSpace ℝ F2] [NormedAddCommGroup F3] [NormedSpace ℝ F3]
    (B : F1 →L[ℝ] F2 →L[ℝ] F3) (hB : ∀ v m, ‖B v m‖ ≤ ‖v‖ * ‖m‖) : ‖B‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => ?_)
  rw [one_mul]
  exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun m => hB v m)

theorem r26t8a_contrCLM_bound (n : ℕ) (v : E) (m : r26t8a_Mult E (n + 1)) :
    ‖r26t8a_contrCLM E n v m‖ ≤ ‖v‖ * ‖m‖ := by
  rw [r26t8a_contrCLM_apply]
  have h := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℝ).norm_map m
  calc ‖m.curryLeft v‖ ≤ ‖m.curryLeft‖ * ‖v‖ := (m.curryLeft).le_opNorm v
    _ = ‖m‖ * ‖v‖ := by
        have : ‖m.curryLeft‖ = ‖m‖ := h
        rw [this]
    _ = ‖v‖ * ‖m‖ := mul_comm _ _

def r26t8a_contr {n : ℕ} (G : E × E → r26t8a_Mult E (n + 1)) : E × E → r26t8a_Mult E n :=
  fun Yw => r26t8a_contrCLM E n Yw.2 (G Yw)

def r26t8a_contrIter : (j : ℕ) → {n : ℕ} → (E × E → r26t8a_Mult E (n + j)) → (E × E → r26t8a_Mult E n)
  | 0, _, G => G
  | j + 1, _, G => r26t8a_contrIter j (r26t8a_contr G)

theorem r26t8a_contr_contDiff {n : ℕ} {N : ℕ} {G : E × E → r26t8a_Mult E (n + 1)}
    (hG : ContDiff ℝ (N : WithTop ℕ∞) G) : ContDiff ℝ (N : WithTop ℕ∞) (r26t8a_contr G) :=
  (r26t8a_contrCLM E n).isBoundedBilinearMap.contDiff.comp (contDiff_snd.prodMk hG)

theorem r26t8a_contrIter_contDiff : ∀ (j : ℕ) {n : ℕ} {N : ℕ} (G : E × E → r26t8a_Mult E (n + j)),
    ContDiff ℝ (N : WithTop ℕ∞) G → ContDiff ℝ (N : WithTop ℕ∞) (r26t8a_contrIter j G)
  | 0, _, _, _, hG => hG
  | j + 1, _, _, G, hG => r26t8a_contrIter_contDiff j _ (r26t8a_contr_contDiff hG)

theorem r26t8a_iteratedFDeriv_id_two (z : E) (i : ℕ) : ‖iteratedFDeriv ℝ (i + 2) (id : E → E) z‖ = 0 := by
  rw [← norm_iteratedFDeriv_fderiv]
  have : fderiv ℝ (id : E → E) = fun _ => ContinuousLinearMap.id ℝ E := by
    funext y; exact fderiv_id
  rw [this]
  have : iteratedFDeriv ℝ (i + 1) (fun _ : E => ContinuousLinearMap.id ℝ E) z = 0 :=
    congrFun (iteratedFDeriv_const_of_ne (𝕜 := ℝ) (Nat.succ_ne_zero i) _) z
  rw [this, norm_zero]

theorem r26t8a_contr_step {n : ℕ} (p q : ℕ) (G : E × E → r26t8a_Mult E (n + 1)) (X z : E)
    (hG : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) G) :
    ‖r26t8a_nest p q (r26t8a_contr G) X z‖ ≤
      ‖z‖ * ‖r26t8a_nest p q G X z‖ + (q : ℝ) * ‖r26t8a_nest p (q - 1) G X z‖ := by
  have hid : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (fun w : E => w) := contDiff_id
  have h := r26t8a_nest_bilinear q p (r26t8a_contrCLM E n) (fun w => w) G X z hid hG
  have hB := r26t8a_clm_norm_le_one (r26t8a_contrCLM E n) (fun v m => r26t8a_contrCLM_bound n v m)
  have hs : 0 ≤ ∑ i ∈ Finset.range (q + 1), (q.choose i : ℝ) * ‖iteratedFDeriv ℝ i (fun w : E => w) z‖ *
      ‖r26t8a_nest p (q - i) G X z‖ := Finset.sum_nonneg fun i _ => by positivity
  refine (le_trans (le_of_eq rfl) h).trans ((mul_le_of_le_one_left hs hB).trans ?_)
  rcases q with _ | q
  · simp [norm_iteratedFDeriv_zero]
  · rw [Finset.sum_range_succ', Finset.sum_range_succ']
    have h0 : ∀ i ∈ Finset.range q, ((q + 1).choose (i + 1 + 1) : ℝ) * ‖iteratedFDeriv ℝ (i + 1 + 1) (fun w : E => w) z‖ *
        ‖r26t8a_nest p (q + 1 - (i + 1 + 1)) G X z‖ = 0 := fun i _ => by
      have : ‖iteratedFDeriv ℝ (i + 1 + 1) (fun w : E => w) z‖ = 0 := r26t8a_iteratedFDeriv_id_two z i
      rw [this]; ring
    rw [Finset.sum_eq_zero h0, zero_add]
    have h1 : ‖iteratedFDeriv ℝ (0 + 1) (fun w : E => w) z‖ ≤ 1 := by
      rw [zero_add, norm_iteratedFDeriv_one]
      have : fderiv ℝ (fun w : E => w) z = ContinuousLinearMap.id ℝ E := fderiv_id
      rw [this]; exact ContinuousLinearMap.norm_id_le
    simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, norm_iteratedFDeriv_zero, Nat.choose_one_right,
      Nat.cast_add, Nat.cast_one, Nat.sub_zero, Nat.add_sub_cancel, zero_add]
    have hn : 0 ≤ ‖r26t8a_nest p q G X z‖ := norm_nonneg _
    have e1 : q + 1 - (0 + 1) = q := by omega
    have e2 : q + 1 - 1 = q := by omega
    rw [e1]
    have hq1 : (0 : ℝ) ≤ (q : ℝ) + 1 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right h1 (mul_nonneg hq1 hn)]

end Chain

end HRS.MS.R26T8A
