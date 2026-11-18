import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.S67NlBD56

/-!
# S6.7 nonlinear, packet S6.7nl.57A: exact finite-subset discrete Leibniz formula with translations

Namespace `HRS.MS.BreakdownS67`, helper prefix `s67bd_`. TeX S:4842-4851 (finiteness
prerequisite), row `S:W:lem:r2mov-global-adjoint` (nonlinear part). Owned definitions:
`s67bd_subsetDiff`, `s67bd_subsetShift`.
The formula is proved in the equivalent form "sum over the full powerset" (the empty subset is the
principal term). Induction on `n` peels the first step: powerset sums are split along
`0 in S` / `0 notin S` (`Finset.sum_powerset_insert`, reindexing by `Fin.succEmb`), the filtered
folds are identified with `s67bd_subsetDiff` of the tail data, and the one-step identity
`delta <B,V> = <B, delta V> + <delta B, V(.+h e)>` is applied to each term; translations commute
with the finite differences.
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

def s67bd_subsetDiff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) (h : Fin n → ℝ) (e : Fin n → Euc d) (S : Finset (Fin n))
    (u : Euc d → F) : Euc d → F :=
  ((List.ofFn (fun i : Fin n => i)).filter (fun i => decide (i ∈ S))).foldr
    (fun i v => s67bd_diff (h i) (e i) v) u

def s67bd_subsetShift (n : ℕ) (h : Fin n → ℝ) (e : Fin n → Euc d)
    (S : Finset (Fin n)) (x : Euc d) : Euc d := x + ∑ i ∈ S, h i • e i

section Aux
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma s67bd57_ofFn_succ (n : ℕ) :
    List.ofFn (fun i : Fin (n + 1) => i) =
      0 :: (List.ofFn (fun i : Fin n => i)).map Fin.succ := by
  rw [List.ofFn_succ, List.map_ofFn]; rfl

lemma s67bd57_sd_map (n : ℕ) (h : Fin (n + 1) → ℝ) (e : Fin (n + 1) → Euc d)
    (S' : Finset (Fin n)) (u : Euc d → F) :
    s67bd_subsetDiff (n + 1) h e (S'.map (Fin.succEmb n)) u =
      s67bd_subsetDiff n (fun i => h i.succ) (fun i => e i.succ) S' u := by
  unfold s67bd_subsetDiff
  rw [s67bd57_ofFn_succ, List.filter_cons]
  have h0 : decide ((0 : Fin (n + 1)) ∈ S'.map (Fin.succEmb n)) = false := by
    simp [Fin.succ_ne_zero]
  have hp : ∀ j : Fin n, decide (j.succ ∈ S'.map (Fin.succEmb n)) = decide (j ∈ S') := by
    intro j; simp
  rw [h0, List.filter_map]
  simp [List.foldr_map, Function.comp_def, hp]

lemma s67bd57_sd_insert (n : ℕ) (h : Fin (n + 1) → ℝ) (e : Fin (n + 1) → Euc d)
    (S' : Finset (Fin n)) (u : Euc d → F) :
    s67bd_subsetDiff (n + 1) h e (insert 0 (S'.map (Fin.succEmb n))) u =
      s67bd_diff (h 0) (e 0) (s67bd_subsetDiff n (fun i => h i.succ) (fun i => e i.succ) S' u) := by
  unfold s67bd_subsetDiff
  rw [s67bd57_ofFn_succ, List.filter_cons]
  have h0 : decide ((0 : Fin (n + 1)) ∈ insert 0 (S'.map (Fin.succEmb n))) = true := by simp
  have hp : ∀ j : Fin n, decide (j.succ ∈ insert 0 (S'.map (Fin.succEmb n))) = decide (j ∈ S') := by
    intro j; simp [Fin.succ_ne_zero]
  rw [h0, List.filter_map]
  simp [List.foldr_map, Function.comp_def, hp]

lemma s67bd57_diff_shift (h : ℝ) (e : Euc d) (G : Euc d → F) (c x : Euc d) :
    s67bd_diff h e (fun y => G (y + c)) x = s67bd_diff h e G (x + c) := by
  unfold s67bd_diff
  rw [add_right_comm]

lemma s67bd57_diff_sum {ι : Type*} (s : Finset ι) (g : ι → Euc d → ℝ) (h : ℝ) (e x : Euc d) :
    s67bd_diff h e (fun y => ∑ i ∈ s, g i y) x = ∑ i ∈ s, s67bd_diff h e (g i) x := by
  unfold s67bd_diff
  simp only [smul_eq_mul]
  rw [← Finset.sum_sub_distrib, Finset.mul_sum]

end Aux

lemma s67bd57_diff_inner (h : ℝ) (e : Euc d) (B V : Euc d → Euc d) (x : Euc d) :
    s67bd_diff h e (fun y => inner ℝ (B y) (V y)) x =
      inner ℝ (B x) (s67bd_diff h e V x) + inner ℝ (s67bd_diff h e B x) (V (x + h • e)) := by
  unfold s67bd_diff
  simp only [inner_smul_right, inner_smul_left, inner_sub_right, inner_sub_left,
    RCLike.conj_to_real, smul_eq_mul]
  ring

lemma s67bd57_sum_powerset_succ {M : Type*} [AddCommMonoid M] (n : ℕ)
    (F : Finset (Fin (n + 1)) → M) :
    ∑ S ∈ (Finset.univ : Finset (Fin (n + 1))).powerset, F S =
      ∑ S' ∈ (Finset.univ : Finset (Fin n)).powerset, F (S'.map (Fin.succEmb n)) +
      ∑ S' ∈ (Finset.univ : Finset (Fin n)).powerset, F (insert 0 (S'.map (Fin.succEmb n))) := by
  have hu : (Finset.univ : Finset (Fin (n + 1))) =
      insert 0 ((Finset.univ : Finset (Fin n)).map (Fin.succEmb n)) := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have h0 : (0 : Fin (n + 1)) ∉ (Finset.univ : Finset (Fin n)).map (Fin.succEmb n) := by
    simp [Fin.succ_ne_zero]
  have hmap : ∀ G : Finset (Fin (n + 1)) → M,
      ∑ t ∈ ((Finset.univ : Finset (Fin n)).map (Fin.succEmb n)).powerset, G t =
        ∑ S' ∈ (Finset.univ : Finset (Fin n)).powerset, G (S'.map (Fin.succEmb n)) := by
    intro G
    symm
    refine Finset.sum_nbij (fun S' => S'.map (Fin.succEmb n)) (fun S' hS' => ?_)
      (fun S₁ _ S₂ _ hS => Finset.map_injective _ hS) (fun t ht => ?_) (fun S' _ => rfl)
    · simpa using Finset.map_subset_map.2 (Finset.mem_powerset.1 hS')
    · obtain ⟨u, hu', rfl⟩ := Finset.subset_map_iff.1 (Finset.mem_powerset.1 ht)
      exact ⟨u, by simp, rfl⟩
  rw [hu, Finset.sum_powerset_insert h0, hmap, hmap (fun t => F (insert 0 t))]

lemma s67bd57_comp_map (n : ℕ) (S' : Finset (Fin n)) :
    (Finset.univ : Finset (Fin (n + 1))) \ S'.map (Fin.succEmb n) =
      insert 0 (((Finset.univ : Finset (Fin n)) \ S').map (Fin.succEmb n)) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

lemma s67bd57_comp_insert (n : ℕ) (S' : Finset (Fin n)) :
    (Finset.univ : Finset (Fin (n + 1))) \ insert 0 (S'.map (Fin.succEmb n)) =
      ((Finset.univ : Finset (Fin n)) \ S').map (Fin.succEmb n) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

lemma s67bd57_shift_map (n : ℕ) (h : Fin (n + 1) → ℝ) (e : Fin (n + 1) → Euc d)
    (S' : Finset (Fin n)) (x : Euc d) :
    s67bd_subsetShift (n + 1) h e (S'.map (Fin.succEmb n)) x =
      s67bd_subsetShift n (fun i => h i.succ) (fun i => e i.succ) S' x := by
  unfold s67bd_subsetShift
  simp [Finset.sum_map]

lemma s67bd57_shift_insert (n : ℕ) (h : Fin (n + 1) → ℝ) (e : Fin (n + 1) → Euc d)
    (S' : Finset (Fin n)) (x : Euc d) :
    s67bd_subsetShift (n + 1) h e (insert 0 (S'.map (Fin.succEmb n))) x =
      s67bd_subsetShift n (fun i => h i.succ) (fun i => e i.succ) S' (x + h 0 • e 0) := by
  unfold s67bd_subsetShift
  rw [Finset.sum_insert (by simp [Fin.succ_ne_zero]), Finset.sum_map]
  simp only [Fin.coe_succEmb]
  abel

lemma s67bd57_sd_empty {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (n : ℕ)
    (h : Fin n → ℝ) (e : Fin n → Euc d) (u : Euc d → F) :
    s67bd_subsetDiff n h e ∅ u = u := by
  simp [s67bd_subsetDiff]

lemma s67bd57_sd_univ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (n : ℕ)
    (h : Fin n → ℝ) (e : Fin n → Euc d) (u : Euc d → F) :
    s67bd_subsetDiff n h e Finset.univ u = s67bd_mixedDiff n h e u := by
  have : List.ofFn (fun i : Fin n => (h i, e i)) =
      (List.ofFn (fun i : Fin n => i)).map (fun i => (h i, e i)) := by
    rw [List.map_ofFn]; rfl
  unfold s67bd_subsetDiff s67bd_mixedDiff
  rw [this, List.foldr_map]
  simp

lemma s67bd57_full (n : ℕ) : ∀ (h : Fin n → ℝ) (e : Fin n → Euc d) (B V : Euc d → Euc d)
    (x : Euc d),
    s67bd_mixedDiff n h e (fun y => inner ℝ (B y) (V y)) x =
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
        inner ℝ (s67bd_subsetDiff n h e S B x)
          (s67bd_subsetDiff n h e (Finset.univ \ S) V (s67bd_subsetShift n h e S x)) := by
  induction n with
  | zero =>
    intro h e B V x
    simp [s67bd_mixedDiff, s67bd_subsetDiff, s67bd_subsetShift]
  | succ n ih =>
    intro h e B V x
    rw [s67bd_mixedDiff_succ]
    have hfun : s67bd_mixedDiff n (fun i => h i.succ) (fun i => e i.succ)
        (fun y => inner ℝ (B y) (V y)) = fun y => ∑ S ∈ (Finset.univ : Finset (Fin n)).powerset,
          inner ℝ (s67bd_subsetDiff n (fun i => h i.succ) (fun i => e i.succ) S B y)
            (s67bd_subsetDiff n (fun i => h i.succ) (fun i => e i.succ) (Finset.univ \ S) V
              (s67bd_subsetShift n (fun i => h i.succ) (fun i => e i.succ) S y)) :=
      funext fun y => ih _ _ B V y
    rw [hfun, s67bd57_diff_sum, s67bd57_sum_powerset_succ, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun S' _ => ?_)
    rw [s67bd57_diff_inner]
    set h' : Fin n → ℝ := fun i => h i.succ with hh'
    set e' : Fin n → Euc d := fun i => e i.succ with he'
    set σ : Euc d := ∑ i ∈ S', h' i • e' i with hσ
    set G : Euc d → Euc d := s67bd_subsetDiff n h' e' (Finset.univ \ S') V with hG
    have hV : (fun y => G (s67bd_subsetShift n h' e' S' y)) = fun y => G (y + σ) := rfl
    rw [hV, s67bd57_diff_shift]
    rw [s67bd57_sd_map, s67bd57_comp_map, s67bd57_sd_insert, s67bd57_shift_map,
      s67bd57_sd_insert, s67bd57_comp_insert, s67bd57_sd_map, s67bd57_shift_insert]
    rfl

theorem s67bd_mixed_leibniz (d n : ℕ) (h : Fin n → ℝ) (e : Fin n → Euc d)
    (hh : ∀ i, h i ≠ 0) (B V : Euc d → Euc d) (x : Euc d) :
    s67bd_mixedDiff n h e (fun y => inner ℝ (B y) (V y)) x =
      inner ℝ (B x) (s67bd_mixedDiff n h e V x) +
      ∑ S ∈ ((Finset.univ : Finset (Fin n)).powerset.erase ∅),
        inner ℝ (s67bd_subsetDiff n h e S B x)
          (s67bd_subsetDiff n h e (Finset.univ \ S) V (s67bd_subsetShift n h e S x)) := by
  rw [s67bd57_full, ← Finset.add_sum_erase _ _ (Finset.empty_mem_powerset _)]
  congr 1
  rw [s67bd57_sd_empty, Finset.sdiff_empty, s67bd57_sd_univ]
  simp [s67bd_subsetShift]

end HRS.MS.BreakdownS67
