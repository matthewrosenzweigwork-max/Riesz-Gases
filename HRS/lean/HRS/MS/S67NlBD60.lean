import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.S67NlBD55
import HRS.MS.S67NlBD56
import HRS.MS.S67NlBD57A
import HRS.MS.S67NlBD57C

/-!
# S6.7 nonlinear breakdown, packet 60: uniform mixed-difference bounds give gradient-jet bounds

Namespace `HRS.MS.BreakdownS67`, helper prefix `s67bd_`. TeX S:4844-4851 (finiteness
prerequisite), nonlinear part of `S:W:lem:r2mov-global-adjoint`. No owned definitions.
Route: (i) the gradient of a mixed difference of `u` is the mixed difference of `∇u` (57C);
(ii) for `f ∈ C^k` with all unit-direction `k`-fold mixed differences bounded by `B`, induction on
`k` peels the innermost difference: the derivative of `Δ_{t,e} f` of order `k` is the difference
quotient of `D^k f`, the induction hypothesis bounds it for every `t ≠ 0`, and letting `t → 0`
(the closed ball is closed, `D^k f` is differentiable) bounds `D^{k+1} f` on unit tuples;
(iii) multilinearity passes from unit tuples to the operator norm; (iv) the finite `cb` sum.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

section Aux60

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- the `k`-th derivative of a difference quotient is the difference quotient of the `k`-th derivative -/
lemma s67bd60_diff_iter {f : Euc d → F} {k : ℕ} (hk' : ContDiff ℝ (k : WithTop ℕ∞) f)
    (h : ℝ) (e : Euc d) (x : Euc d) :
    iteratedFDeriv ℝ k (s67bd_diff h e f) x =
      h⁻¹ • (iteratedFDeriv ℝ k f (x + h • e) - iteratedFDeriv ℝ k f x) := by
  have hs : ContDiff ℝ (k : WithTop ℕ∞) (fun y : Euc d => f (y + h • e)) :=
    hk'.comp (contDiff_id.add contDiff_const)
  unfold s67bd_diff
  rw [iteratedFDeriv_const_smul_apply' ((hs.sub hk').contDiffAt)]
  have hsub := iteratedFDeriv_sub_apply (𝕜 := ℝ) (x := x) hs.contDiffAt hk'.contDiffAt
  rw [show (fun y : Euc d => f (y + h • e) - f y) = (fun y : Euc d => f (y + h • e)) - f from rfl,
    hsub, iteratedFDeriv_comp_add_right]

/-- peeling the innermost difference of a mixed difference -/
lemma s67bd60_mixed_snoc (k : ℕ) (h : Fin (k + 1) → ℝ) (e : Fin (k + 1) → Euc d) (f : Euc d → F) :
    s67bd_mixedDiff (k + 1) h e f =
      s67bd_mixedDiff k (fun i => h i.castSucc) (fun i => e i.castSucc)
        (s67bd_diff (h (Fin.last k)) (e (Fin.last k)) f) := by
  unfold s67bd_mixedDiff
  rw [List.ofFn_succ', List.concat_eq_append, List.foldr_append]
  simp

/-- unit-tuple bound on `D^k f` from uniform bounds on the `k`-fold mixed differences -/
lemma s67bd60_unit_bound (B : ℝ) : ∀ (k : ℕ) (f : Euc d → F),
    ContDiff ℝ (k : WithTop ℕ∞) f →
    (∀ (h : Fin k → ℝ) (e : Fin k → Euc d), (∀ i, h i ≠ 0) → (∀ i, ‖e i‖ = 1) → ∀ x,
      ‖s67bd_mixedDiff k h e f x‖ ≤ B) →
    ∀ (m : Fin k → Euc d), (∀ i, ‖m i‖ = 1) → ∀ x, ‖iteratedFDeriv ℝ k f x m‖ ≤ B := by
  intro k
  induction k with
  | zero =>
    intro f _ hbd m _ x
    have h0 := hbd (fun i => i.elim0) (fun i => i.elim0) (fun i => i.elim0)
      (fun i => i.elim0) x
    rw [s67bd_mixedDiff_zero] at h0
    simpa [iteratedFDeriv_zero_apply] using h0
  | succ k ih =>
    intro f hf hbd m hm x
    have hf' : ContDiff ℝ (k : WithTop ℕ∞) f := hf.of_le (by exact_mod_cast Nat.le_succ k)
    have hDk : DifferentiableAt ℝ (iteratedFDeriv ℝ k f) x :=
      (hf.differentiable_iteratedFDeriv (m := k)
        (by exact_mod_cast Nat.lt_succ_self k)) x
    have hbt : ∀ t : ℝ, t ≠ 0 →
        ‖t⁻¹ • (iteratedFDeriv ℝ k f (x + t • m 0) (Fin.tail m) -
          iteratedFDeriv ℝ k f x (Fin.tail m))‖ ≤ B := by
      intro t ht
      have hg : ContDiff ℝ (k : WithTop ℕ∞) (s67bd_diff t (m 0) f) :=
        s67bd_diff_contDiff hf' t (m 0)
      have key := ih (s67bd_diff t (m 0) f) hg ?_ (Fin.tail m) (fun i => hm _) x
      · rw [s67bd60_diff_iter hf' t (m 0) x] at key
        simpa using key
      · intro h' e' hh' he' y
        have hb := hbd (Fin.snoc (α := fun _ => ℝ) h' t) (Fin.snoc (α := fun _ => Euc d) e' (m 0))
          (by
            intro i
            refine Fin.lastCases ?_ (fun i => ?_) i
            · simpa using ht
            · simpa using hh' i)
          (by
            intro i
            refine Fin.lastCases ?_ (fun i => ?_) i
            · simpa using hm 0
            · simpa using he' i) y
        rw [s67bd60_mixed_snoc] at hb
        simpa using hb
    have hψ : HasDerivAt (fun t : ℝ => iteratedFDeriv ℝ k f (x + t • m 0) (Fin.tail m))
        ((fderiv ℝ (iteratedFDeriv ℝ k f) x (m 0)) (Fin.tail m)) 0 := by
      have h1 : HasFDerivAt (iteratedFDeriv ℝ k f) (fderiv ℝ (iteratedFDeriv ℝ k f) x) x :=
        hDk.hasFDerivAt
      have h2 : HasDerivAt (fun t : ℝ => x + t • m 0) (m 0) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (m 0)).const_add x
      have h3 : HasFDerivAt (iteratedFDeriv ℝ k f) (fderiv ℝ (iteratedFDeriv ℝ k f) x)
          (x + (0 : ℝ) • m 0) := by simpa using h1
      have h4 := h3.comp_hasDerivAt (0 : ℝ) h2
      have ev := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Euc d) F
        (Fin.tail m)).hasFDerivAt (x := iteratedFDeriv ℝ k f (x + (0 : ℝ) • m 0))
      exact ev.comp_hasDerivAt (0 : ℝ) h4
    have hlim := hψ.tendsto_slope_zero
    rw [iteratedFDeriv_succ_apply_left]
    refine le_of_tendsto hlim.norm ?_
    refine eventually_nhdsWithin_of_forall (fun t ht => ?_)
    simpa using hbt t ht

/-- from unit tuples to the multilinear operator norm -/
lemma s67bd60_opnorm {k : ℕ} {B : ℝ} (hB : 0 ≤ B)
    (f : ContinuousMultilinearMap ℝ (fun _ : Fin k => Euc d) F)
    (hf : ∀ m : Fin k → Euc d, (∀ i, ‖m i‖ = 1) → ‖f m‖ ≤ B) : ‖f‖ ≤ B := by
  refine f.opNorm_le_bound hB (fun m => ?_)
  by_cases hz : ∃ i, m i = 0
  · obtain ⟨i, hi⟩ := hz
    rw [f.map_coord_zero i hi, norm_zero]
    exact mul_nonneg hB (Finset.prod_nonneg fun j _ => norm_nonneg _)
  · simp only [not_exists] at hz
    have hn : ∀ i, ‖m i‖ ≠ 0 := fun i => norm_ne_zero_iff.2 (hz i)
    set m' : Fin k → Euc d := fun i => (‖m i‖)⁻¹ • m i with hm'def
    have hm' : ∀ i, ‖m' i‖ = 1 := by
      intro i
      simp only [hm'def, norm_smul, norm_inv, norm_norm]
      exact inv_mul_cancel₀ (hn i)
    have hmm : m = fun i => ‖m i‖ • m' i := by
      funext i
      simp only [hm'def, smul_smul]
      rw [mul_inv_cancel₀ (hn i), one_smul]
    have hfm : f m = (∏ i, ‖m i‖) • f m' := by
      conv_lhs => rw [hmm]
      exact f.toMultilinearMap.map_smul_univ _ _
    rw [hfm, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun i _ => norm_nonneg _)]
    calc (∏ i, ‖m i‖) * ‖f m'‖ ≤ (∏ i, ‖m i‖) * B :=
          mul_le_mul_of_nonneg_left (hf m' hm')
            (Finset.prod_nonneg fun i _ => norm_nonneg _)
      _ = B * ∏ i, ‖m i‖ := mul_comm _ _

end Aux60

theorem s67bd_difference_to_jet (d j : ℕ) (u : Euc d → ℝ)
    (hu : ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) u) (B : ℝ) (hB : 0 ≤ B)
    (hbd : ∀ n ≤ j, ∀ (h : Fin n → ℝ) (e : Fin n → Euc d),
      (∀ i, h i ≠ 0) → (∀ i, ‖e i‖ = 1) → ∀ x,
      ‖gradient (s67bd_mixedDiff n h e u) x‖ ≤ B) :
    (∀ k ≤ j, ∀ x, ‖iteratedFDeriv ℝ k (fun y => gradient u y) x‖ ≤ B) ∧
    cbNormVecE j (fun x => gradient u x) ≤ ENNReal.ofReal (((j : ℝ) + 1) * B) := by
  have hG : ContDiff ℝ (j : WithTop ℕ∞) (fun x => gradient u x) := s67_grad_contDiff hu
  have hjet : ∀ k ≤ j, ∀ x, ‖iteratedFDeriv ℝ k (fun y => gradient u y) x‖ ≤ B := by
    intro k hk x
    have hGk : ContDiff ℝ (k : WithTop ℕ∞) (fun y => gradient u y) :=
      hG.of_le (by exact_mod_cast hk)
    have hu' : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) u :=
      hu.of_le (by exact_mod_cast Nat.succ_le_succ hk)
    have hunit := s67bd60_unit_bound B k (fun y => gradient u y) hGk
      (fun h e hh he y => by
        rw [← (s67bd_mixed_gradient d k h e hh u hu').1 y]
        exact hbd k hk h e hh he y)
    exact s67bd60_opnorm hB _ (fun m hm => hunit m hm x)
  refine ⟨hjet, ?_⟩
  unfold cbNormVecE
  calc ∑ i ∈ Finset.range (j + 1), ⨆ x : Euc d,
        ENNReal.ofReal ‖iteratedFDeriv ℝ i (fun x => gradient u x) x‖
      ≤ ∑ _i ∈ Finset.range (j + 1), ENNReal.ofReal B := by
        refine Finset.sum_le_sum fun i hi => iSup_le fun x => ?_
        exact ENNReal.ofReal_le_ofReal (hjet i (by simpa [Nat.lt_succ_iff] using hi) x)
    _ = ENNReal.ofReal (((j : ℝ) + 1) * B) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [← Nat.cast_succ, ENNReal.ofReal_natCast]

end HRS.MS.BreakdownS67
