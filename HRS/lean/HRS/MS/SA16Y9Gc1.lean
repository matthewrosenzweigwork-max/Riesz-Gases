import HRS.MS.SA16Y9Dm1
import HRS.MS.SA16Y4Ap2

/-!
# S.A.16 (SA16Y9) Gc1: level compatibility and norm bound of the interpolated nonlocal operators `GInt` (stability, G2d, part 3)

`sa16y9_GInt_low`: for `μ` regular of order `m+4`, `ι²_m ∘ GInt_{m+2} = GInt_m ∘ ι²_m` and `‖GInt_m‖ ≤ CGl` (from `sa16y4_approx2` at levels
`m` and `m+1`, with the zero drift).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Gc1
variable {d : ℕ}

lemma sa16y9_zero_drift (m : ℕ) (t : ℝ) :
    ∀ r ∈ Icc (0 : ℝ) t, ContDiff ℝ ((m + 2 : ℕ) : WithTop ℕ∞)
        ((fun (_ : ℝ) (_ : EuclideanSpace ℝ (Fin d)) => (0 : EuclideanSpace ℝ (Fin d))) r) ∧
      ‖(fun (_ : ℝ) (_ : EuclideanSpace ℝ (Fin d)) => (0 : EuclideanSpace ℝ (Fin d))) r 0‖ ≤ 0 ∧
      ∀ j, 1 ≤ j → j ≤ m + 2 → ∀ x, ‖iteratedFDeriv ℝ j
        ((fun (_ : ℝ) (_ : EuclideanSpace ℝ (Fin d)) => (0 : EuclideanSpace ℝ (Fin d))) r) x‖ ≤ 0 := by
  intro r _
  refine ⟨contDiff_const, by simp, fun j hj _ x => ?_⟩
  rw [iteratedFDeriv_const_of_ne (by omega)]
  simp

set_option maxHeartbeats 3200000 in
theorem sa16y9_GInt_low (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (m : ℕ) (p : ℝ) [Fact (2 ≤ p)] (MB Λ : ℝ)
    (hsub : s ≤ (d : ℝ) - 2 ∧ (d : ℝ) < p * (s + 1)) :
    ∃ CGl : ℝ, 0 ≤ CGl ∧ ∀ (M : Matrix (Fin d) (Fin d) ℝ), (∀ i j, |M i j| ≤ MB) →
      ∀ (μ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (t : ℝ), 0 < t →
      (∀ r ∈ Icc (0 : ℝ) t, IsRegularDensityW (m + 4) Λ (μ r)) → ∀ N : ℕ, 1 ≤ N →
      ∀ σ ∈ Icc (0 : ℝ) t,
        (sa16sz_iota2 d m p).comp (sa16y4_GInt d (m + 2) N p s M t μ σ) =
          (sa16y4_GInt d m N p s M t μ σ).comp (sa16sz_iota2 d m p) ∧
        ‖sa16y4_GInt d m N p s M t μ σ‖ ≤ CGl := by
  obtain ⟨cE1, CN1, B1, CG1, B1', Bk1, hCN1, hB1, hCG1, h1⟩ :=
    sa16y4_approx2 d m hd s p MB Λ 0 0 hs0 hsub.1 hsub.2 le_rfl le_rfl
  obtain ⟨cE2, CN2, B2, CG2, B2', Bk2, hCN2, hB2, hCG2, h2⟩ :=
    sa16y4_approx2 d (m + 1) hd s p MB Λ 0 0 hs0 hsub.1 hsub.2 le_rfl le_rfl
  refine ⟨CG1, hCG1, fun M hM μ t ht hμ N hN σ hσ => ?_⟩
  have hμ3 : ∀ r ∈ Icc (0 : ℝ) t, IsRegularDensityW (m + 3) Λ (μ r) := fun r hr =>
    sa16y9_regDensity_mono (by omega) (hμ r hr)
  have hμ4 : ∀ r ∈ Icc (0 : ℝ) t, IsRegularDensityW (m + 1 + 3) Λ (μ r) := hμ
  obtain ⟨u1, -, -, -, -, -, hT01, hc1, -⟩ :=
    h1 t ht M hM μ hμ3 (fun _ _ => 0) (sa16y9_zero_drift m t) N hN 1 one_pos 0
  obtain ⟨u2, -, -, -, -, -, hT02, hc2, -⟩ :=
    h2 t ht M hM μ hμ4 (fun _ _ => 0) (sa16y9_zero_drift (m + 1) t) N hN 1 one_pos 0
  refine ⟨?_, hT01 σ hσ⟩
  have e1 := hc1 σ hσ
  have e2 := hc2 σ hσ
  ext1 y
  simp only [ContinuousLinearMap.comp_apply, sa16sz_iota2]
  have e2y := congrArg (fun L => L y) e2
  simp only [ContinuousLinearMap.comp_apply] at e2y
  have e1y := congrArg (fun L => L (sa16r_iota d (m + 1) p y)) e1
  simp only [ContinuousLinearMap.comp_apply] at e1y
  rw [e2y, e1y]

end Gc1

end HRS.Whole.AppendixA.Phase2SA16R
