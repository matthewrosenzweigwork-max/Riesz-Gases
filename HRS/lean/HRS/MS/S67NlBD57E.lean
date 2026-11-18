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
# S6.7 nonlinear breakdown, packet 57E: bounded drift/source residual

Namespace `HRS.MS.BreakdownS67`, helper prefix `s67bd_`. TeX S:4842-4851 (finiteness
prerequisite), nonlinear part of `S:W:lem:r2mov-global-adjoint`. No owned definitions.
Route: Leibniz expansion (57A) at `B` and `∇u`, the empty-subset principal term cancels against the
commutator's gradient term (57C), every nonempty subset puts a difference on `B` (bounded by `Mb`
via 57B) and leaves a strictly lower gradient jet (bounded by `A` via 57B and `hlower`), the
full difference of `J` is bounded by `MJ` (57B with `S = univ`); the constant is `2^n * Mb + 1`.
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
lemma s67bd57e_mixedDiff_add (n : ℕ) (h : Fin n → ℝ) (e : Fin n → Euc d)
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

theorem s67bd_bounded_commutator (d n : ℕ) (hn : 1 ≤ n) (Mb : ℝ) (hMb : 0 ≤ Mb) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A MJ : ℝ, 0 ≤ A → 0 ≤ MJ →
      ∀ (B : Euc d → Euc d) (J u : Euc d → ℝ),
      ContDiff ℝ (n : WithTop ℕ∞) B →
      (∀ i ≤ n, ∀ x, ‖iteratedFDeriv ℝ i B x‖ ≤ Mb) →
      ContDiff ℝ (n : WithTop ℕ∞) J →
      (∀ i ≤ n, ∀ x, ‖iteratedFDeriv ℝ i J x‖ ≤ MJ) →
      ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) u →
      (∀ i < n, ∀ x, ‖iteratedFDeriv ℝ i (fun y => gradient u y) x‖ ≤ A) →
      ∀ (h : Fin n → ℝ) (e : Fin n → Euc d),
      (∀ i, h i ≠ 0) → (∀ i, ‖e i‖ = 1) → ∀ x,
        |s67bd_commutator 0 n h e B J u x| ≤ C * (A + MJ) := by
  refine ⟨2 ^ n * Mb + 1, by positivity, fun A MJ hA hMJ B J u hB hBj hJ hJj hu hlow h e hh he x => ?_⟩
  have hG : ContDiff ℝ (n : WithTop ℕ∞) (fun y => gradient u y) := s67_grad_contDiff hu
  -- expansion of the commutator
  have hGr := (s67bd_mixed_gradient d n h e hh u hu).1 x
  have hL := s67bd_mixed_leibniz d n h e hh B (fun y => gradient u y) x
  have e0 : (fun y => inner ℝ ((-(0 : ℝ)) • y + B y) (gradient u y) + J y) =
      fun y => inner ℝ (B y) (gradient u y) + J y := by
    funext y; simp
  have hcomm : s67bd_commutator 0 n h e B J u x =
      (∑ S ∈ ((Finset.univ : Finset (Fin n)).powerset.erase ∅),
        inner ℝ (s67bd_subsetDiff n h e S B x)
          (s67bd_subsetDiff n h e (Finset.univ \ S) (fun y => gradient u y)
            (s67bd_subsetShift n h e S x))) + s67bd_mixedDiff n h e J x := by
    unfold s67bd_commutator
    rw [e0, s67bd57e_mixedDiff_add, hGr]
    beta_reduce
    rw [hL]
    simp only [neg_zero, zero_smul, zero_add]
    ring
  -- the J term
  have hJb : |s67bd_mixedDiff n h e J x| ≤ MJ := by
    have hc : (Finset.univ : Finset (Fin n)).card = n := by simp
    have := s67bd_subset_mean_value d n h e hh he Finset.univ J (by rw [hc]; exact hJ) MJ hMJ
      (by intro y; rw [hc]; exact hJj n le_rfl y) x
    have e2 : s67bd_subsetDiff n h e Finset.univ J = s67bd_mixedDiff n h e J := by
      have : List.ofFn (fun i : Fin n => (h i, e i)) =
          (List.ofFn (fun i : Fin n => i)).map (fun i => (h i, e i)) := by
        rw [List.map_ofFn]; rfl
      unfold s67bd_subsetDiff s67bd_mixedDiff
      rw [this, List.foldr_map]
      simp
    rw [e2] at this
    simpa using this
  -- each nonempty subset term
  have hterm : ∀ S ∈ ((Finset.univ : Finset (Fin n)).powerset.erase ∅),
      |inner ℝ (s67bd_subsetDiff n h e S B x)
          (s67bd_subsetDiff n h e (Finset.univ \ S) (fun y => gradient u y)
            (s67bd_subsetShift n h e S x))| ≤ Mb * A := by
    intro S hS
    rw [Finset.mem_erase] at hS
    have hcpos : 0 < S.card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 hS.1)
    have hcle : S.card ≤ n := by simpa using Finset.card_le_univ S
    have h1 := s67bd_subset_mean_value d n h e hh he S B
      (hB.of_le (by exact_mod_cast hcle)) Mb hMb (fun y => hBj _ hcle y)
    have hcs : (Finset.univ \ S).card < n := by
      rw [Finset.card_univ_sdiff, Fintype.card_fin]; omega
    have h2 := s67bd_subset_mean_value d n h e hh he (Finset.univ \ S)
      (fun y => gradient u y) (hG.of_le (by exact_mod_cast hcs.le)) A hA
      (fun y => hlow _ hcs y)
    refine (abs_real_inner_le_norm _ _).trans ?_
    exact mul_le_mul (h1 x) (h2 _) (norm_nonneg _) hMb
  have hsum : |∑ S ∈ ((Finset.univ : Finset (Fin n)).powerset.erase ∅),
        inner ℝ (s67bd_subsetDiff n h e S B x)
          (s67bd_subsetDiff n h e (Finset.univ \ S) (fun y => gradient u y)
            (s67bd_subsetShift n h e S x))| ≤ 2 ^ n * (Mb * A) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hMb hA)
    have : (((Finset.univ : Finset (Fin n)).powerset.erase ∅).card : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) := by
      exact_mod_cast (Finset.card_erase_le).trans (by simp)
    simpa using this
  rw [hcomm]
  refine (abs_add_le _ _).trans ?_
  have hA2 : 0 ≤ (2 : ℝ) ^ n * (Mb * A) := by positivity
  have h3 : 0 ≤ (2 : ℝ) ^ n * Mb * MJ := by positivity
  have h4 : (2 ^ n * Mb + 1) * (A + MJ) =
      2 ^ n * (Mb * A) + 2 ^ n * Mb * MJ + A + MJ := by ring
  linarith

end HRS.MS.BreakdownS67
