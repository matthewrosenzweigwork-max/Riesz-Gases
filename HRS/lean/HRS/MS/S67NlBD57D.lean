import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.S67NlBD55
import HRS.MS.S67NlBD56
import HRS.MS.S67NlBD57A
import HRS.MS.S67NlBD57B
import HRS.MS.S67NlBD57C

/-!
# S6.7 nonlinear breakdown, packet 57D: exact shifted affine OU residual and its lower-jet bound

Namespace `HRS.MS.BreakdownS67`, helper prefix `s67bd_`. TeX S:4842-4851 (finiteness
prerequisite), nonlinear part of `S:W:lem:r2mov-global-adjoint`. No owned definitions.
Route: additivity of the mixed difference, the Leibniz expansion (57A) at the affine field
`x ↦ -q x`, vanishing of every affine subset difference except the singletons, the singleton
reindexing, and the subset mean value bound (57B) on the order `n - 1` gradient jets.
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

/-- additivity of the mixed difference -/
lemma s67bd57d_mixedDiff_add (n : ℕ) (h : Fin n → ℝ) (e : Fin n → Euc d)
    (f g : Euc d → ℝ) :
    s67bd_mixedDiff n h e (fun y => f y + g y) =
      fun y => s67bd_mixedDiff n h e f y + s67bd_mixedDiff n h e g y := by
  unfold s67bd_mixedDiff
  generalize List.ofFn (fun i => (h i, e i)) = L
  induction L with
  | nil => rfl
  | cons a L ih =>
    rw [List.foldr_cons, List.foldr_cons, List.foldr_cons, ih]
    funext x
    simp only [s67bd_diff]
    rw [← smul_add]
    congr 1
    abel

/-- the difference of a linear map is the constant `c • e` -/
lemma s67bd57d_diff_lin (c h : ℝ) (hh : h ≠ 0) (e : Euc d) :
    s67bd_diff h e (fun y : Euc d => c • y) = fun _ => c • e := by
  funext x
  simp only [s67bd_diff]
  have : c • (x + h • e) - c • x = h • (c • e) := by module
  rw [this, smul_smul, inv_mul_cancel₀ hh, one_smul]

lemma s67bd57d_diff_const (c : Euc d) (h : ℝ) (e : Euc d) :
    s67bd_diff h e (fun _ : Euc d => c) = fun _ => 0 := by
  funext x
  simp [s67bd_diff]

lemma s67bd57d_fold_lin (n : ℕ) (h : Fin n → ℝ) (e : Fin n → Euc d) (hh : ∀ i, h i ≠ 0)
    (c : ℝ) (L : List (Fin n)) (hL : 2 ≤ L.length) :
    L.foldr (fun i v => s67bd_diff (h i) (e i) v) (fun y : Euc d => c • y) = fun _ => 0 := by
  induction L with
  | nil => simp at hL
  | cons a L ih =>
    rw [List.foldr_cons]
    by_cases h2 : 2 ≤ L.length
    · rw [ih h2]; exact s67bd57d_diff_const 0 _ _
    · have h1 : L.length = 1 := by simp at hL; omega
      obtain ⟨b, rfl⟩ := List.length_eq_one_iff.1 h1
      simp only [List.foldr_cons, List.foldr_nil]
      rw [s67bd57d_diff_lin c _ (hh b)]
      exact s67bd57d_diff_const _ _ _

lemma s67bd57d_filter_nodup (n : ℕ) (S : Finset (Fin n)) :
    ((List.ofFn (fun i : Fin n => i)).filter (fun i => decide (i ∈ S))).Nodup :=
  (List.nodup_ofFn.2 Function.injective_id).filter _

lemma s67bd57d_filter_toFinset (n : ℕ) (S : Finset (Fin n)) :
    ((List.ofFn (fun i : Fin n => i)).filter (fun i => decide (i ∈ S))).toFinset = S := by
  ext a
  simp

lemma s67bd57d_filter_length (n : ℕ) (S : Finset (Fin n)) :
    ((List.ofFn (fun i : Fin n => i)).filter (fun i => decide (i ∈ S))).length = S.card := by
  rw [← List.toFinset_card_of_nodup (s67bd57d_filter_nodup n S), s67bd57d_filter_toFinset]

lemma s67bd57d_filter_single (n : ℕ) (k : Fin n) :
    (List.ofFn (fun i : Fin n => i)).filter (fun i => decide (i ∈ ({k} : Finset (Fin n)))) =
      [k] := by
  have hlen := s67bd57d_filter_length n {k}
  rw [Finset.card_singleton] at hlen
  obtain ⟨a, ha⟩ := List.length_eq_one_iff.1 hlen
  have hk : k ∈ (List.ofFn (fun i : Fin n => i)).filter
      (fun i => decide (i ∈ ({k} : Finset (Fin n)))) := by simp
  rw [ha] at hk ⊢
  simp at hk
  rw [hk]

lemma s67bd57d_subsetDiff_lin_ge (n : ℕ) (h : Fin n → ℝ) (e : Fin n → Euc d)
    (hh : ∀ i, h i ≠ 0) (c : ℝ) (S : Finset (Fin n)) (hS : 2 ≤ S.card) :
    s67bd_subsetDiff n h e S (fun y : Euc d => c • y) = fun _ => 0 := by
  unfold s67bd_subsetDiff
  exact s67bd57d_fold_lin n h e hh c _ (by rw [s67bd57d_filter_length]; exact hS)

lemma s67bd57d_subsetDiff_lin_single (n : ℕ) (h : Fin n → ℝ) (e : Fin n → Euc d)
    (hh : ∀ i, h i ≠ 0) (c : ℝ) (k : Fin n) :
    s67bd_subsetDiff n h e {k} (fun y : Euc d => c • y) = fun _ => c • e k := by
  unfold s67bd_subsetDiff
  rw [s67bd57d_filter_single]
  simp only [List.foldr_cons, List.foldr_nil]
  exact s67bd57d_diff_lin c _ (hh k) _

/-- the Leibniz remainder of the affine field -/
lemma s67bd57d_remainder (d n : ℕ) (q : ℝ) (h : Fin n → ℝ) (e : Fin n → Euc d)
    (hh : ∀ i, h i ≠ 0) (V : Euc d → Euc d) (x : Euc d) :
    ∑ S ∈ ((Finset.univ : Finset (Fin n)).powerset.erase ∅),
        inner ℝ (s67bd_subsetDiff n h e S (fun y : Euc d => (-q) • y) x)
          (s67bd_subsetDiff n h e (Finset.univ \ S) V (s67bd_subsetShift n h e S x)) =
      -q * ∑ k : Fin n, inner ℝ (e k)
        (s67bd_subsetDiff n h e (Finset.univ.erase k) V (x + h k • e k)) := by
  set T : Finset (Fin n) → ℝ := fun S =>
    inner ℝ (s67bd_subsetDiff n h e S (fun y : Euc d => (-q) • y) x)
          (s67bd_subsetDiff n h e (Finset.univ \ S) V (s67bd_subsetShift n h e S x)) with hT
  have hsub : Finset.powersetCard 1 (Finset.univ : Finset (Fin n)) ⊆
      ((Finset.univ : Finset (Fin n)).powerset.erase ∅) := by
    intro S hS
    rw [Finset.mem_powersetCard] at hS
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_powerset.2 hS.1⟩
    rintro rfl
    simp at hS
  have hzero : ∀ S ∈ ((Finset.univ : Finset (Fin n)).powerset.erase ∅),
      S ∉ Finset.powersetCard 1 (Finset.univ : Finset (Fin n)) → T S = 0 := by
    intro S hS hS1
    rw [Finset.mem_erase] at hS
    have hne : S.card ≠ 0 := fun h0 => hS.1 (Finset.card_eq_zero.1 h0)
    have hne1 : S.card ≠ 1 := fun h1 =>
      hS1 (Finset.mem_powersetCard.2 ⟨Finset.subset_univ _, h1⟩)
    simp only [hT]
    rw [s67bd57d_subsetDiff_lin_ge n h e hh (-q) S (by omega)]
    simp
  show ∑ S ∈ ((Finset.univ : Finset (Fin n)).powerset.erase ∅), T S = _
  rw [← Finset.sum_subset hsub hzero, Finset.powersetCard_one, Finset.sum_map, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  simp only [hT, Function.Embedding.coeFn_mk]
  rw [s67bd57d_subsetDiff_lin_single n h e hh, Finset.sdiff_singleton_eq_erase]
  simp only [s67bd_subsetShift, Finset.sum_singleton]
  rw [real_inner_smul_left]

lemma s67bd57d_residual (d n : ℕ) (q : ℝ) (h : Fin n → ℝ) (e : Fin n → Euc d)
    (hh : ∀ i, h i ≠ 0) (B : Euc d → Euc d) (J u : Euc d → ℝ)
    (hu : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) u) (x : Euc d) :
    s67bd_commutator q n h e B J u x = s67bd_commutator 0 n h e B J u x +
      (-q) * ∑ k : Fin n, inner ℝ (e k)
        (s67bd_subsetDiff n h e (Finset.univ.erase k) (fun y => gradient u y) (x + h k • e k)) := by
  rw [← s67bd57d_remainder d n q h e hh (fun y => gradient u y) x]
  have hG := (s67bd_mixed_gradient d n h e hh u hu).1 x
  have hL := s67bd_mixed_leibniz d n h e hh (fun y : Euc d => (-q) • y)
    (fun y => gradient u y) x
  beta_reduce at hL
  have e1 : (fun y => inner ℝ ((-q) • y + B y) (gradient u y) + J y) =
      fun y => (inner ℝ (B y) (gradient u y) + J y) + inner ℝ ((-q) • y) (gradient u y) := by
    funext y; rw [inner_add_left]; ring
  have e0 : (fun y => inner ℝ ((-(0 : ℝ)) • y + B y) (gradient u y) + J y) =
      fun y => inner ℝ (B y) (gradient u y) + J y := by
    funext y; simp
  unfold s67bd_commutator
  rw [e1, e0, s67bd57d_mixedDiff_add, hG]
  beta_reduce
  rw [hL]
  simp only [inner_add_left, neg_zero, zero_smul, zero_add]
  ring

theorem s67bd_affine_commutator (d n : ℕ) (hn : 1 ≤ n) (q A : ℝ) (hA : 0 ≤ A)
    (h : Fin n → ℝ) (e : Fin n → Euc d) (hh : ∀ i, h i ≠ 0) (he : ∀ i, ‖e i‖ = 1)
    (B : Euc d → Euc d) (J u : Euc d → ℝ)
    (hu : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) u)
    (hlower : ∀ i < n, ∀ x, ‖iteratedFDeriv ℝ i (fun y => gradient u y) x‖ ≤ A) :
    (∀ x, s67bd_commutator q n h e B J u x = s67bd_commutator 0 n h e B J u x -
      q * ∑ k : Fin n, inner ℝ (e k)
        (s67bd_subsetDiff n h e (Finset.univ.erase k) (fun y => gradient u y) (x + h k • e k))) ∧
    ∀ x, |q * ∑ k : Fin n, inner ℝ (e k)
      (s67bd_subsetDiff n h e (Finset.univ.erase k) (fun y => gradient u y) (x + h k • e k))| ≤
        |q| * (n : ℝ) * A := by
  refine ⟨fun x => ?_, fun x => ?_⟩
  · rw [s67bd57d_residual d n q h e hh B J u hu x]; ring
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    have hG : ContDiff ℝ (j : WithTop ℕ∞) (fun x => gradient u x) := s67_grad_contDiff (hu.of_le (by exact_mod_cast Nat.le_succ _))
    have hbound : ∀ (k : Fin (j + 1)) (y : Euc d),
        ‖s67bd_subsetDiff (j + 1) h e (Finset.univ.erase k) (fun y => gradient u y) y‖ ≤ A := by
      intro k y
      have hc : (Finset.univ.erase k).card = j := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ k)]; simp
      refine s67bd_subset_mean_value d (j + 1) h e hh he _ (fun y => gradient u y) ?_ A hA ?_ y
      · rw [hc]; exact hG
      · intro z; rw [hc]; exact hlower j (Nat.lt_succ_self j) z
    rw [abs_mul]
    have hsum : |∑ k : Fin (j + 1), inner ℝ (e k)
        (s67bd_subsetDiff (j + 1) h e (Finset.univ.erase k) (fun y => gradient u y)
          (x + h k • e k))| ≤ ((j + 1 : ℕ) : ℝ) * A := by
      calc _ ≤ ∑ k : Fin (j + 1), |inner ℝ (e k)
            (s67bd_subsetDiff (j + 1) h e (Finset.univ.erase k) (fun y => gradient u y)
              (x + h k • e k))| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _k : Fin (j + 1), A := by
            refine Finset.sum_le_sum fun k _ => ?_
            refine (abs_real_inner_le_norm _ _).trans ?_
            rw [he k, one_mul]
            exact hbound k _
        _ = _ := by simp
    calc |q| * _ ≤ |q| * (((j + 1 : ℕ) : ℝ) * A) := mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
      _ = _ := by ring

end HRS.MS.BreakdownS67
