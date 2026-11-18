import HRS.MS.R26T8AP11b3

/-!
# S8.2 Taylor split (T), step B2a: Taylor formula for polynomials given by diagonal multilinear forms
`r26t8a_poly_taylor`: for `Q(v) = Σ_{j<N} coeff_j (v,…,v)` with `coeff_j = 0` for `j > m` (`m < N`),
`Q(w) = Σ_{ℓ ≤ m} (1/ℓ!) D^ℓ Q(0) (w,…,w)`.  Also `r26t8a_cmm_diag_contDiff` (smoothness of `x ↦ f x (g x,…,g x)`).
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ContDiff

namespace HRS.MS.R26T8A

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem r26t8a_diag_jet_ne {n ℓ : ℕ} (B : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ) (h : ℓ ≠ n) :
    iteratedFDeriv ℝ ℓ (fun v : E => B (fun _ => v)) 0 = 0 := by
  set g : E →L[ℝ] (Fin n → E) := ContinuousLinearMap.pi (fun _ => ContinuousLinearMap.id ℝ E) with hg
  have hfun : (fun v : E => B (fun _ => v)) = B ∘ g := by funext v; rfl
  have hz : g 0 = 0 := map_zero g
  have h0 : iteratedFDeriv ℝ ℓ B (g 0) = 0 := by
    have hb := B.norm_iteratedFDeriv_le ℓ (g 0)
    rw [hz, Fintype.card_fin] at hb
    have hle : ‖iteratedFDeriv ℝ ℓ B 0‖ ≤ 0 := by
      rcases lt_or_gt_of_ne h with hlt | hgt
      · refine hb.trans (le_of_eq ?_)
        rw [norm_zero, zero_pow (by omega : n - ℓ ≠ 0), mul_zero]
      · refine hb.trans (le_of_eq ?_)
        rw [Nat.descFactorial_eq_zero_iff_lt.2 hgt]; simp
    rw [hz]
    exact norm_le_zero_iff.1 hle
  rw [hfun, g.iteratedFDeriv_comp_right (B.contDiff (n := (ℓ : WithTop ℕ∞))) 0 le_rfl, h0]
  ext v
  rfl

theorem r26t8a_diag_jet_self {n : ℕ} (B : ContinuousMultilinearMap ℝ (fun _ : Fin n => E) ℝ) (w : E) :
    iteratedFDeriv ℝ n (fun v : E => B (fun _ => v)) 0 (fun _ => w) = (n.factorial : ℝ) * B (fun _ => w) := by
  rw [B.iteratedFDeriv_comp_diagonal 0 (fun _ => w)]
  simp [Finset.sum_const, Fintype.card_perm]

theorem r26t8a_poly_taylor (N m : ℕ) (hN : m < N) (coeff : (j : ℕ) → ContinuousMultilinearMap ℝ (fun _ : Fin j => E) ℝ)
    (hvan : ∀ j, m < j → coeff j = 0) (w : E) :
    ∑ j ∈ Finset.range N, coeff j (fun _ => w) =
      ∑ ℓ ∈ Finset.range (m + 1), (1 / (ℓ.factorial : ℝ)) *
        iteratedFDeriv ℝ ℓ (fun v : E => ∑ j ∈ Finset.range N, coeff j (fun _ => v)) 0 (fun _ => w) := by
  have hcd : ∀ (j ℓ : ℕ), ContDiff ℝ (ℓ : WithTop ℕ∞) (fun v : E => coeff j (fun _ => v)) := fun j ℓ =>
    (coeff j).contDiff.comp (ContinuousLinearMap.pi (fun _ : Fin j => ContinuousLinearMap.id ℝ E)).contDiff
  have key : ∀ ℓ : ℕ, iteratedFDeriv ℝ ℓ (fun v : E => ∑ j ∈ Finset.range N, coeff j (fun _ => v)) 0 (fun _ => w) =
      ∑ j ∈ Finset.range N, (if ℓ = j then (ℓ.factorial : ℝ) * coeff ℓ (fun _ => w) else 0) := by
    intro ℓ
    rw [iteratedFDeriv_fun_sum_apply (fun j _ => (hcd j ℓ).contDiffAt)]
    rw [ContinuousMultilinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : ℓ = j
    · subst hj
      rw [if_pos rfl]
      exact r26t8a_diag_jet_self (coeff ℓ) w
    · rw [if_neg hj, r26t8a_diag_jet_ne (coeff j) hj]; rfl
  rw [← Finset.sum_subset (Finset.range_subset_range.2 (by omega : m + 1 ≤ N)) (fun j hj hj' => by
    rw [Finset.mem_range] at hj hj'
    rw [hvan j (by omega)]; rfl)]
  refine Finset.sum_congr rfl fun ℓ hℓ => ?_
  rw [key ℓ, Finset.sum_ite_eq, if_pos (by rw [Finset.mem_range] at hℓ ⊢; omega)]
  have : (ℓ.factorial : ℝ) ≠ 0 := by positivity
  field_simp

theorem r26t8a_cmm_diag_contDiff {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {n : WithTop ℕ∞} :
    ∀ (ℓ : ℕ) (f : X → ContinuousMultilinearMap ℝ (fun _ : Fin ℓ => E) ℝ) (g : X → E),
      ContDiff ℝ n f → ContDiff ℝ n g → ContDiff ℝ n (fun x => f x (fun _ => g x))
  | 0, f, g, hf, _ => by
    have : (fun x => f x (fun _ => g x)) = fun x => continuousMultilinearCurryFin0 ℝ E ℝ (f x) := by
      funext x; simp
      exact congrArg (f x) (Subsingleton.elim _ _)
    rw [this]
    exact (continuousMultilinearCurryFin0 ℝ E ℝ).contDiff.comp hf
  | ℓ + 1, f, g, hf, hg => by
    have hL : ContDiff ℝ n (fun x => continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (ℓ + 1) => E) ℝ (f x)) :=
      (LinearIsometryEquiv.contDiff _).comp hf
    have hf' : ContDiff ℝ n (fun x => (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (ℓ + 1) => E) ℝ (f x)) (g x)) :=
      hL.clm_apply hg
    have ih := r26t8a_cmm_diag_contDiff ℓ _ g hf' hg
    have heq : (fun x => f x (fun _ => g x)) = fun x =>
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (ℓ + 1) => E) ℝ (f x)) (g x) (fun _ => g x) := by
      funext x
      show f x (fun _ => g x) = (f x).curryLeft (g x) (fun _ => g x)
      rw [ContinuousMultilinearMap.curryLeft_apply]
      congr 1
      funext i
      refine Fin.cases rfl (fun j => by simp) i
    rw [heq]
    exact ih

end HRS.MS.R26T8A
