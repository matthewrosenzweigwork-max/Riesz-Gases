import HRS.MS.SA16Y11Dr3
import HRS.MS.SA16Y11Nl2

/-!
# S.A.16 (SA16Y11) Kd: the difference of the iso/hilbert Duhamel families is small in `W^{m+2} → W^m`

`sa16y11_Kint_diff`: `‖ι_m((Kint¹ σ - Kint² σ) y)‖ ≤ (C₁ δ_b + C₂ δ) ‖y‖` for `y ∈ W^{m+2,p}`, where `Kint = B_{bcInt} - NInt` of `sa16y5_approx3`,
`δ_b` bounds the components of `b¹ - b²` through `C^{m+1}` and `δ` the weights of `μ¹ - μ²` through order `m+2`.  `C₁, C₂` depend only
on `d,m,s,p,MB,Λ`.  (`B` is additive in the coefficient: `sa16so_B_sub`, both coefficients being individually bounded.)
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Kd
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

set_option maxHeartbeats 3200000 in
theorem sa16y11_Kint_diff (d m : ℕ) (hd : 1 ≤ d) (s p MB Λ : ℝ) [Fact (2 ≤ p)] (hs0 : 0 ≤ s)
    (hs1 : s < (d : ℝ) - 1) (hfar : (d : ℝ) < p * (s + 1)) :
    ∃ C1 C2 : ℝ, 0 < C1 ∧ 0 < C2 ∧ ∀ M : Matrix (Fin d) (Fin d) ℝ, (∀ i j, |M i j| ≤ MB) →
      ∀ (t : ℝ), 0 < t → ∀ μ1 μ2 : ℝ → Euc d → ℝ,
      (∀ r ∈ Icc (0 : ℝ) t, IsRegularDensityW (m + 3) Λ (μ1 r)) →
      (∀ r ∈ Icc (0 : ℝ) t, IsRegularDensityW (m + 3) Λ (μ2 r)) →
      ∀ δ : ℝ, 0 ≤ δ → (∀ r ∈ Icc (0 : ℝ) t, sa16y5_Dec (m + 2) δ (fun y => μ1 r y - μ2 r y)) →
      ∀ b1 b2 : ℝ → Euc d → Euc d, ∀ δb : ℝ, 0 ≤ δb →
      (∀ r ∈ Icc (0 : ℝ) t, ∀ j : Fin d, ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fun y => b1 r y j) ∧
        ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (fun y => b2 r y j)) →
      (∀ r ∈ Icc (0 : ℝ) t, ∀ j : Fin d, ∀ k ≤ m + 1, ∀ x,
        ‖iteratedFDeriv ℝ k (fun y => b1 r y j - b2 r y j) x‖ ≤ δb) →
      ∀ N : ℕ, 1 ≤ N → ∀ σ ∈ Icc (0 : ℝ) t, ∀ (B1 B2 : ℝ),
      SA16BddCoef (m + 1) B1 (sa16y4_bcInt d N t b1 σ) → SA16BddCoef (m + 1) B2 (sa16y4_bcInt d N t b2 σ) →
      ∀ y : WmpSpace d (m + 1 + 1) p,
        ‖sa16r_iota d m p ((sa16y5_Kint d m N p s M t μ1 b1 σ - sa16y5_Kint d m N p s M t μ2 b2 σ) y)‖ ≤
          (C1 * δb + C2 * δ) * ‖y‖ := by
  obtain ⟨Cn, hCn, hN⟩ := sa16y11_NInt_diff d m hd s p MB Λ hs0 hs1 hfar
  obtain ⟨Cb, hCb1, hCb⟩ := sa16y11_bcInt_diff d m hd
  set C1 : ℝ := sa16so_cB d (m + 1) Cb with hC1
  have hC1pos : 0 < C1 := by
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
    have hCb0 : 0 < Cb := by linarith
    rw [hC1, sa16so_cB]
    exact mul_pos (by positivity) (mul_pos hdpos (mul_pos (by positivity) (mul_pos hCb0 (by positivity))))
  refine ⟨C1, Cn, hC1pos, hCn, fun M hM t ht μ1 μ2 h1 h2 δ hδ hDd b1 b2 δb hδb hsm hder N hN1 σ hσ B1 B2 hb1 hb2 y => ?_⟩
  have hbc := hCb δb hδb t ht b1 b2 N hN1 hsm hder σ hσ
  have hBsub := sa16so_B_sub (p := p) hb1 hb2
  have hBn : ‖sa16so_B d (m + 1) p (fun j x => sa16y4_bcInt d N t b1 σ j x - sa16y4_bcInt d N t b2 σ j x)‖ ≤
      C1 * δb := by
    refine (sa16so_B_norm (p := p) hbc).trans (le_of_eq ?_)
    rw [hC1, sa16so_cB, sa16so_cB]; ring
  have hNn := hN M hM t ht μ1 μ2 h1 h2 δ hδ hDd N hN1 σ hσ y
  have e : (sa16y5_Kint d m N p s M t μ1 b1 σ - sa16y5_Kint d m N p s M t μ2 b2 σ) y =
      (sa16so_B d (m + 1) p (fun j x => sa16y4_bcInt d N t b1 σ j x - sa16y4_bcInt d N t b2 σ j x)) y -
        (sa16y5_NInt d m N p s M t μ1 σ - sa16y5_NInt d m N p s M t μ2 σ) y := by
    rw [hBsub]
    unfold sa16y5_Kint
    simp only [ContinuousLinearMap.sub_apply]
    abel
  rw [e, map_sub]
  refine (norm_sub_le _ _).trans ?_
  have h2' : ‖sa16r_iota d m p ((sa16so_B d (m + 1) p (fun j x => sa16y4_bcInt d N t b1 σ j x -
      sa16y4_bcInt d N t b2 σ j x)) y)‖ ≤ C1 * δb * ‖y‖ := by
    have h3 := (sa16r_iota d m p).le_opNorm ((sa16so_B d (m + 1) p (fun j x => sa16y4_bcInt d N t b1 σ j x -
      sa16y4_bcInt d N t b2 σ j x)) y)
    have h4 := sa16y4_iota_norm (d := d) (p := p) m
    have h5 := (sa16so_B d (m + 1) p (fun j x => sa16y4_bcInt d N t b1 σ j x -
      sa16y4_bcInt d N t b2 σ j x)).le_opNorm y
    have h6 := norm_nonneg ((sa16so_B d (m + 1) p (fun j x => sa16y4_bcInt d N t b1 σ j x -
      sa16y4_bcInt d N t b2 σ j x)) y)
    calc _ ≤ ‖sa16r_iota d m p‖ * ‖(sa16so_B d (m + 1) p (fun j x => sa16y4_bcInt d N t b1 σ j x -
          sa16y4_bcInt d N t b2 σ j x)) y‖ := h3
      _ ≤ 1 * ‖(sa16so_B d (m + 1) p (fun j x => sa16y4_bcInt d N t b1 σ j x -
          sa16y4_bcInt d N t b2 σ j x)) y‖ := mul_le_mul_of_nonneg_right h4 h6
      _ ≤ (C1 * δb) * ‖y‖ := by
          rw [one_mul]
          exact h5.trans (mul_le_mul_of_nonneg_right hBn (norm_nonneg _))
  nlinarith [h2', hNn]

end Kd

end HRS.Whole.AppendixA.Phase2SA16R

end
