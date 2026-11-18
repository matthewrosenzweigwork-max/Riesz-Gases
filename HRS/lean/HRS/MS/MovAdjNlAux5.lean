import HRS.MS.MovAdjNlAux4

/-!
# S6.7 nonlinear row, package A, packet N4 (part 1): the converse ladder

Namespace `HRS.MS.MovAdjNl`, helpers `s67a_`.  Infrastructure for the supplement row `S:W:lem:r2mov-global-adjoint`; not a manuscript row.

`s67a_converse_ladder`: if `ψ ∈ Σ^s` (`s ≥ 0`) is `C¹` with `ψ, x_jψ, ∂_jψ ∈ L²` and `g_j = x_jψ + ∂_jψ ∈ Σ^s` for all `j`, then `ψ ∈ Σ^{s+1}` with
`‖ψ‖²_{Σ^{s+1}} ≤ 3^s ∑_j ‖g_j‖²_{Σ^s} + (d+1) ‖ψ‖²_{Σ^s}`.
Proof: `c_α(g_j) = 2 √((α_j+1)/2) c_{α+e_j}(ψ)` (`s67_coeff_xmul_gen`, `s67_coeff_partial_gen`), hence `2β_j c_β(ψ)² = c_{β-e_j}(g_j)²`
for `β_j ≥ 1`, and `λ_β = 2∑_j β_j + d + 1`; reindex over the injective map `α ↦ α + e_j`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovAdjNl

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovC1 HRS.MS.MovOsc HRS.MS.MovAdj

variable {d : ℕ}

/-- The ladder combination `g_j = x_jψ + ∂_jψ`. -/
def s67aG (j : Fin d) (ψ : Euc d → ℝ) (x : Euc d) : ℝ :=
  x j * ψ x + fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ))

theorem s67a_coeff_g (j : Fin d) {ψ : Euc d → ℝ} (hψC : ContDiff ℝ 1 ψ)
    (hψL : MemLp ψ 2 (volume : Measure (Euc d)))
    (hx : MemLp (fun x => x j * ψ x) 2 (volume : Measure (Euc d)))
    (hd : MemLp (fun x => fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ))) 2 (volume : Measure (Euc d)))
    (α : MultiIndex d) :
    hermiteCoeff (s67aG j ψ) α = 2 * Real.sqrt (((α j : ℝ) + 1) / 2) * hermiteCoeff ψ (mova1_up j α) := by
  have h1 := s67_coeff_xmul_gen hψL j α
  have h2 := s67_coeff_partial_gen hψC hψL j hd α
  have e : s67aG j ψ = fun x => x j * ψ x + fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ)) := rfl
  rw [e, movc1_coeff_add hx hd α, h1, h2]
  ring

theorem s67a_coeff_g_sq (j : Fin d) {ψ : Euc d → ℝ} (hψC : ContDiff ℝ 1 ψ)
    (hψL : MemLp ψ 2 (volume : Measure (Euc d)))
    (hx : MemLp (fun x => x j * ψ x) 2 (volume : Measure (Euc d)))
    (hd : MemLp (fun x => fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ))) 2 (volume : Measure (Euc d)))
    (α : MultiIndex d) :
    hermiteCoeff (s67aG j ψ) α ^ 2 = 2 * ((α j : ℝ) + 1) * hermiteCoeff ψ (mova1_up j α) ^ 2 := by
  rw [s67a_coeff_g j hψC hψL hx hd α, mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  ring

theorem s67a_eigen_eq (β : MultiIndex d) :
    oscEigenvalue d β = (∑ i, 2 * (β i : ℝ)) + ((d : ℝ) + 1) := by
  unfold oscEigenvalue MultiIndex.degree
  rw [Nat.cast_sum, Finset.mul_sum]
  ring

theorem s67a_converse_ladder {s : ℝ} (hs : 0 ≤ s) {ψ : Euc d → ℝ} (hψ : MemOsc s ψ) (hψC : ContDiff ℝ 1 ψ)
    (hx : ∀ j, MemLp (fun x => x j * ψ x) 2 (volume : Measure (Euc d)))
    (hd : ∀ j, MemLp (fun x => fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ))) 2 (volume : Measure (Euc d)))
    (hg : ∀ j, MemOsc s (s67aG j ψ)) :
    MemOsc (s + 1) ψ ∧
      oscNorm (s + 1) ψ ^ 2 ≤ 3 ^ s * ∑ j, oscNorm s (s67aG j ψ) ^ 2 + ((d : ℝ) + 1) * oscNorm s ψ ^ 2 := by
  set a : MultiIndex d → ℝ := fun β => oscEigenvalue d β ^ s * hermiteCoeff ψ β ^ 2 with ha
  have haS : Summable a := hψ.2
  set F : Fin d → MultiIndex d → ℝ := fun i β =>
    oscEigenvalue d β ^ s * (2 * (β i : ℝ)) * hermiteCoeff ψ β ^ 2 with hF
  have hev : ∀ β : MultiIndex d, 0 < oscEigenvalue d β := oscEigenvalue_pos
  have hdec : ∀ β : MultiIndex d, oscEigenvalue d β ^ (s + 1) * hermiteCoeff ψ β ^ 2 =
      ∑ i, F i β + ((d : ℝ) + 1) * a β := by
    intro β
    have hL := s67a_eigen_eq (d := d) β
    have e1 : ∑ i, F i β = oscEigenvalue d β ^ s * hermiteCoeff ψ β ^ 2 * ∑ i, 2 * (β i : ℝ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by simp only [hF]; ring
    have e2 : oscEigenvalue d β ^ (s + 1) = oscEigenvalue d β ^ s * ((∑ i, 2 * (β i : ℝ)) + ((d : ℝ) + 1)) := by
      rw [Real.rpow_add_one (hev β).ne', ← hL]
    rw [e1, e2, ha]
    simp only
    ring
  -- the pieces `F i`
  have hFnn : ∀ i β, 0 ≤ F i β := fun i β => by
    simp only [hF]
    exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (hev β).le _) (by positivity)) (sq_nonneg _)
  have hFup : ∀ i α, F i (mova1_up i α) = oscEigenvalue d (mova1_up i α) ^ s * hermiteCoeff (s67aG i ψ) α ^ 2 := by
    intro i α
    rw [s67a_coeff_g_sq i hψC hψ.1 (hx i) (hd i) α]
    simp only [hF, mova1_up_apply]
    push_cast
    ring
  have hle : ∀ α : MultiIndex d, ∀ i, oscEigenvalue d (mova1_up i α) ^ s ≤ 3 ^ s * oscEigenvalue d α ^ s := by
    intro α i
    rw [← Real.mul_rpow (by norm_num) (hev α).le, mova1_eigen_up]
    refine Real.rpow_le_rpow (by have := hev α; linarith) ?_ hs
    have := one_le_oscEigenvalue (d := d) α
    linarith
  have hFsum : ∀ i, Summable (F i) ∧ ∑' β, F i β ≤ 3 ^ s * oscNorm s (s67aG i ψ) ^ 2 := by
    intro i
    have hgi := hg i
    have hcomp : Summable (fun α => F i (mova1_up i α)) := by
      refine Summable.of_nonneg_of_le (fun α => hFnn i _) (fun α => ?_) (hgi.2.mul_left (3 ^ s))
      rw [hFup]
      calc oscEigenvalue d (mova1_up i α) ^ s * hermiteCoeff (s67aG i ψ) α ^ 2
          ≤ (3 ^ s * oscEigenvalue d α ^ s) * hermiteCoeff (s67aG i ψ) α ^ 2 :=
            mul_le_mul_of_nonneg_right (hle α i) (sq_nonneg _)
        _ = 3 ^ s * (oscEigenvalue d α ^ s * hermiteCoeff (s67aG i ψ) α ^ 2) := by ring
    have hoff : ∀ β ∉ Set.range (mova1_up (d := d) i), F i β = 0 := by
      intro β hβ
      have h0 : β i = 0 := by
        by_contra hne
        exact hβ (mova1_up_ne_dn_range i β (Nat.one_le_iff_ne_zero.2 hne))
      simp only [hF, h0]
      simp
    have hS : Summable (F i) := ((mova1_up_injective i).summable_iff hoff).1 hcomp
    refine ⟨hS, ?_⟩
    have hsupp : Function.support (F i) ⊆ Set.range (mova1_up (d := d) i) := by
      intro β hβ
      by_contra hn
      exact hβ (hoff β hn)
    rw [← (mova1_up_injective i).tsum_eq hsupp]
    calc ∑' α, F i (mova1_up i α) ≤ ∑' α, 3 ^ s * (oscEigenvalue d α ^ s * hermiteCoeff (s67aG i ψ) α ^ 2) := by
          refine Summable.tsum_le_tsum (fun α => ?_) hcomp (hgi.2.mul_left (3 ^ s))
          rw [hFup]
          calc oscEigenvalue d (mova1_up i α) ^ s * hermiteCoeff (s67aG i ψ) α ^ 2
              ≤ (3 ^ s * oscEigenvalue d α ^ s) * hermiteCoeff (s67aG i ψ) α ^ 2 :=
                mul_le_mul_of_nonneg_right (hle α i) (sq_nonneg _)
            _ = 3 ^ s * (oscEigenvalue d α ^ s * hermiteCoeff (s67aG i ψ) α ^ 2) := by ring
      _ = 3 ^ s * oscNorm s (s67aG i ψ) ^ 2 := by
          rw [tsum_mul_left, oscNorm, Real.sq_sqrt (tsum_nonneg fun α =>
            mul_nonneg (Real.rpow_nonneg (hev α).le _) (sq_nonneg _))]
  have hsumAll : Summable (fun β : MultiIndex d => oscEigenvalue d β ^ (s + 1) * hermiteCoeff ψ β ^ 2) := by
    have : (fun β : MultiIndex d => oscEigenvalue d β ^ (s + 1) * hermiteCoeff ψ β ^ 2) =
        fun β => ∑ i, F i β + ((d : ℝ) + 1) * a β := funext hdec
    rw [this]
    exact (summable_sum fun i _ => (hFsum i).1).add (haS.mul_left _)
  refine ⟨⟨hψ.1, hsumAll⟩, ?_⟩
  rw [oscNorm, Real.sq_sqrt (tsum_nonneg fun α =>
    mul_nonneg (Real.rpow_nonneg (hev α).le _) (sq_nonneg _))]
  have h1 : ∑' β : MultiIndex d, oscEigenvalue d β ^ (s + 1) * hermiteCoeff ψ β ^ 2 =
      ∑ i, ∑' β, F i β + ((d : ℝ) + 1) * ∑' β, a β := by
    have : (fun β : MultiIndex d => oscEigenvalue d β ^ (s + 1) * hermiteCoeff ψ β ^ 2) =
        fun β => ∑ i, F i β + ((d : ℝ) + 1) * a β := funext hdec
    rw [this, Summable.tsum_add (summable_sum fun i _ => (hFsum i).1) (haS.mul_left _),
      Summable.tsum_finsetSum fun i _ => (hFsum i).1, tsum_mul_left]
  rw [h1]
  have h2 : oscNorm s ψ ^ 2 = ∑' β, a β := by
    rw [oscNorm, Real.sq_sqrt (tsum_nonneg fun α => mul_nonneg (Real.rpow_nonneg (hev α).le _) (sq_nonneg _))]
  rw [h2, Finset.mul_sum]
  exact add_le_add (Finset.sum_le_sum fun i _ => (hFsum i).2) le_rfl

end HRS.MS.MovAdjNl
