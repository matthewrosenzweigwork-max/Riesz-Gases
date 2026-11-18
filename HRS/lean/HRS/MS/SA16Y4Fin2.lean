import HRS.MS.SA16Y4Ap2
import HRS.MS.SA16Y3L4

/-!
# S.A.16 (SA16Y4) Fin2: uniform bound of `div(bcInt ψ)` on the support ball (the `hdiv` hypothesis of `sa16y4_weak_limit`)

`sa16y4_bcInt_abs_le`: `|bcInt N σ j x| ≤ A + L(‖x‖ + 1)` for `σ ∈ [0,t]` when the components of `b_r` grow at most like `A + L‖y‖`.
`sa16y4_bcInt_div_bound`: with `SA16DerCoef (m+1) B` (so `‖∇ bcInt‖ ≤ B`) there is `cN` with `|div(bcInt N σ ψ)| ≤ cN 1_{B_{R0}}`
for all `N ≥ 1`, `σ ∈ [0,t]`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16

section Fin2
variable {d : ℕ}

lemma sa16y4_tm_abs_le (N : ℕ) {f : EuclideanSpace ℝ (Fin d) → ℝ} {A L : ℝ} (hL : 0 ≤ L)
    (hf : ∀ y, |f y| ≤ A + L * ‖y‖) (x : EuclideanSpace ℝ (Fin d)) :
    |sa16y4_tm d N f x| ≤ A + L * (‖x‖ + 1) := by
  have hρ0 : ∀ z, 0 ≤ sa16y_rho d N z := sa16y_rho_nonneg N
  have hρ1 := sa16y_rho_int (d := d) N
  have hρs : ∀ z : EuclideanSpace ℝ (Fin d), 1 < ‖z‖ → sa16y_rho d N z = 0 := by
    intro z hz
    refine sa16y_rho_supp N z (lt_of_le_of_lt ?_ hz)
    rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  have h1 := sa16y4_mol_growth (sa16y4_rho_cc (d := d) N) hρ0 hρ1 hρs hf hL x
  have hχ : |sa16j_chi d ((N : ℝ) + 1) x| ≤ 1 := by
    unfold sa16j_chi
    rw [abs_of_nonneg (sa16j_bump d).nonneg]
    exact (sa16j_bump d).le_one
  unfold sa16y4_tm
  rw [abs_mul]
  have h0 : 0 ≤ |∫ y, f y * sa16y_rho d N (x - y)| := abs_nonneg _
  calc |sa16j_chi d ((N : ℝ) + 1) x| * |∫ y, f y * sa16y_rho d N (x - y)| ≤ 1 * (A + L * (‖x‖ + 1)) :=
        mul_le_mul hχ h1 h0 zero_le_one
    _ = _ := one_mul _

lemma sa16y4_bcInt_abs_le {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (ht : 0 < t) {A L : ℝ} (hL : 0 ≤ L)
    (b : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hb : ∀ r ∈ Icc (0 : ℝ) t, ∀ j y, |b r y j| ≤ A + L * ‖y‖) {σ : ℝ} (hσ : σ ∈ Icc (0 : ℝ) t) (j : Fin d)
    (x : EuclideanSpace ℝ (Fin d)) :
    |sa16y4_bcInt d N t b σ j x| ≤ A + L * (‖x‖ + 1) := by
  have hw0 : ∀ i ∈ Finset.range (N + 1), 0 ≤ sa16y4_hat N t i σ := fun i _ => sa16y4_hat_nonneg N t i σ
  have hw1 := sa16y4_hat_sum hN ht hσ
  unfold sa16y4_bcInt
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i ∈ Finset.range (N + 1), |sa16y4_hat N t i σ * sa16y4_tm d N (fun y => b (t - (i : ℝ) * t / N) y j) x|
      ≤ ∑ i ∈ Finset.range (N + 1), sa16y4_hat N t i σ * (A + L * (‖x‖ + 1)) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [abs_mul, abs_of_nonneg (hw0 i hi)]
        exact mul_le_mul_of_nonneg_left (sa16y4_tm_abs_le N hL (fun y => hb _ (sa16y4_node_mem hN ht hi) j y) x) (hw0 i hi)
    _ = A + L * (‖x‖ + 1) := by rw [← Finset.sum_mul, hw1, one_mul]

theorem sa16y4_bcInt_div_bound {t B A L : ℝ} (ht : 0 < t) (hL : 0 ≤ L) (hA : 0 ≤ A) {m : ℕ}
    (b : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hb : ∀ r ∈ Icc (0 : ℝ) t, ∀ j y, |b r y j| ≤ A + L * ‖y‖)
    (hD : ∀ N : ℕ, 1 ≤ N → ∀ σ ∈ Icc (0 : ℝ) t, SA16DerCoef (m + 1) B (sa16y4_bcInt d N t b σ))
    {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ) :
    ∃ cN R0 : ℝ, 0 ≤ cN ∧ ∀ N : ℕ, 1 ≤ N → ∀ σ ∈ Icc (0 : ℝ) t, ∀ x, |sa16so_divFun (sa16y4_bcInt d N t b σ) ψ x| ≤
      cN * (closedBall (0 : EuclideanSpace ℝ (Fin d)) R0).indicator (fun _ => (1 : ℝ)) x := by
  obtain ⟨R1, hR1⟩ := hψ.2.isCompact.isBounded.subset_closedBall (0 : EuclideanSpace ℝ (Fin d))
  set R0 : ℝ := max R1 0 with hR0
  have hψ0 : ∀ x, R0 < ‖x‖ → ψ x = 0 := by
    intro x hx
    by_contra hne
    have : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) R1 := hR1 (subset_tsupport ψ hne)
    rw [mem_closedBall_zero_iff] at this
    exact absurd (lt_of_le_of_lt this (lt_of_le_of_lt (le_max_left _ _) hx)) (lt_irrefl _)
  obtain ⟨S, hS⟩ := hψ.1.continuous.bounded_above_of_compact_support hψ.2
  have hψ' : ∀ i : Fin d, IsCcInfty (fun y => fderiv ℝ ψ y (EuclideanSpace.single i 1)) := fun i =>
    sa16s_cc_fderiv hψ _
  have hS' : ∀ i : Fin d, ∃ S', ∀ y, |fderiv ℝ ψ y (EuclideanSpace.single i 1)| ≤ S' := fun i => by
    obtain ⟨S', h⟩ := (hψ' i).1.continuous.bounded_above_of_compact_support (hψ' i).2
    exact ⟨S', fun y => by simpa [Real.norm_eq_abs] using h y⟩
  choose S' hS'b using hS'
  set Sm : ℝ := max S 0 + ∑ i, max (S' i) 0 with hSm
  have hSm0 : 0 ≤ Sm := by positivity
  have hψS : ∀ y, |ψ y| ≤ Sm := fun y => by
    have := hS y
    rw [Real.norm_eq_abs] at this
    have : 0 ≤ ∑ i, max (S' i) 0 := Finset.sum_nonneg fun i _ => le_max_right _ _
    linarith [le_max_left S 0]
  have hψS' : ∀ i y, |fderiv ℝ ψ y (EuclideanSpace.single i 1)| ≤ Sm := fun i y => by
    have h2 : max (S' i) 0 ≤ ∑ j, max (S' j) 0 :=
      Finset.single_le_sum (f := fun j => max (S' j) 0) (fun j _ => le_max_right _ _) (Finset.mem_univ i)
    have : 0 ≤ max S 0 := le_max_right _ _
    linarith [le_max_left (S' i) 0, hS'b i y]
  have hB0 : 0 ≤ B := by
    by_cases hN : (Finset.range 1).Nonempty
    · exact (hD 1 le_rfl 0 ⟨le_rfl, ht.le⟩).nonneg
    · exact absurd (by simp) hN
  refine ⟨(d : ℝ) * (B * Sm + (A + L * (R0 + 1)) * Sm), R0, by positivity, fun N hN σ hσ x => ?_⟩
  have hD' := hD N hN σ hσ
  refine sa16y3_divFun_bound (Ab := A + L * (R0 + 1)) (Sψ := Sm) (Sψ' := Sm) (R0 := R0) hD'.smooth
    (fun i y => ?_) (fun i y hy => ?_) hψ.1 hψ0 hψS (fun i y => hψS' i y) x |>.trans (le_of_eq rfl)
  · have := hD'.bound i 1 le_rfl (by omega) y
    rwa [norm_iteratedFDeriv_one] at this
  · refine (sa16y4_bcInt_abs_le hN ht hL b hb hσ i y).trans ?_
    nlinarith

end Fin2

end HRS.Whole.AppendixA.Phase2SA16R
