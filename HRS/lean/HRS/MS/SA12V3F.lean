import HRS.MS.SA12V3E

/-!
# S.A.12 N1/N2 (SA12V3 worker), part F: the nonlocal test term as a convolution expansion

`sa12v3_D1 ψ i = ∂_iψ`.  For a locally integrable kernel `γ`, `ψ ∈ C_c^∞` and `μ` differentiable,
`∑_{ij} M_{ji} ∂_j(μ ∂_i(γ*ψ)) = ∑_{ij} M_{ji} (∂_jμ · (γ*∂_iψ) + μ · (γ*∂_j∂_iψ))`
(`nonlocalTestPer` and `nonlocalTestRd` are both of this shape), and `∂_iψ`, `∂_j∂_iψ` are mean-zero tests.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff Pointwise

namespace HRS.MH.AdjointRd.Phase2SA12V3

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

/-- The coordinate derivative `∂_iψ`. -/
def sa12v3_D1 (ψ : Euc d → ℝ) (i : Fin d) (y : Euc d) : ℝ :=
  fderiv ℝ ψ y (EuclideanSpace.single i (1 : ℝ))

theorem sa12v3_D1_smooth {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (i : Fin d) :
    ContDiff ℝ ∞ (sa12v3_D1 ψ i) := by
  unfold sa12v3_D1
  exact (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single i (1 : ℝ) : Euc d)).contDiff.comp
    (hψ.fderiv_right (m := ∞) le_rfl)

theorem sa12v3_D1_supp {ψ : Euc d → ℝ} {R : ℝ} (hψ : ∀ y : Euc d, R < ‖y‖ → ψ y = 0) (i : Fin d) :
    ∀ y : Euc d, R < ‖y‖ → sa12v3_D1 ψ i y = 0 := by
  intro y hy
  have h : ψ =ᶠ[𝓝 y] fun _ => 0 := by
    have : {z : Euc d | R < ‖z‖} ∈ 𝓝 y := (isOpen_lt continuous_const continuous_norm).mem_nhds hy
    filter_upwards [this] with z hz using hψ z hz
  unfold sa12v3_D1
  rw [h.fderiv_eq]; simp

theorem sa12v3_int_D1 {g : Euc d → ℝ} (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (i : Fin d) :
    ∫ y, sa12v3_D1 g i y = 0 := by
  have hg1 : ContDiff ℝ 1 g := hg.of_le (by simp)
  have hd1 : Continuous (sa12v3_D1 g i) := (sa12v3_D1_smooth hg i).continuous
  have hdc : HasCompactSupport (sa12v3_D1 g i) := by
    have := hgc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i (1 : ℝ) : Euc d)
    exact this
  have hI2 : Integrable (fun x => fderiv ℝ g x (EuclideanSpace.single i (1 : ℝ))) (volume : Measure (Euc d)) :=
    hd1.integrable_of_hasCompactSupport hdc
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := (volume : Measure (Euc d)))
    (f := fun _ => (1 : ℝ)) (g := g) (v := (EuclideanSpace.single i (1 : ℝ) : Euc d))
    (by simp) (by simpa only [one_mul] using hI2)
    (by simpa using hg1.continuous.integrable_of_hasCompactSupport hgc)
    (fun x _ => differentiableAt_const _) (fun x _ => (hg1.differentiable (by simp)) x)
  simpa [sa12v3_D1] using h

theorem sa12v3_D1_compact {ψ : Euc d → ℝ} (hψc : HasCompactSupport ψ) (i : Fin d) :
    HasCompactSupport (sa12v3_D1 ψ i) :=
  hψc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i (1 : ℝ) : Euc d)

theorem sa12v3_Test.mono {R B B' : ℝ} {φ : Euc d → ℝ} (h : sa12v3_Test R B φ) (hB : B ≤ B') :
    sa12v3_Test R B' φ :=
  ⟨h.cont, h.supp, fun u => (h.bdd u).trans hB, h.mean⟩

theorem sa12v3_D1_test {ψ : Euc d → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) {R : ℝ}
    (hsupp : ∀ y : Euc d, R < ‖y‖ → ψ y = 0) (i : Fin d) : ∃ B : ℝ, sa12v3_Test R B (sa12v3_D1 ψ i) := by
  have hc := (sa12v3_D1_smooth hψ i).continuous
  obtain ⟨B, hB⟩ := hc.bounded_above_of_compact_support (sa12v3_D1_compact hψc i)
  exact ⟨B, hc, sa12v3_D1_supp hsupp i, fun u => by simpa [Real.norm_eq_abs] using hB u,
    sa12v3_int_D1 hψ hψc i⟩

theorem sa12v3_tests {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) :
    ∃ R B : ℝ, 0 ≤ R ∧ 0 ≤ B ∧ (∀ i, sa12v3_Test R B (sa12v3_D1 ψ i)) ∧
      ∀ i j, sa12v3_Test R B (sa12v3_D1 (sa12v3_D1 ψ i) j) := by
  obtain ⟨R, A, hR, hA, hjet, hvan⟩ := HRS.MH.AdjointRd.Phase2SA12Limit.sa12k_psi_data hψ
  have hsupp : ∀ y : Euc d, R < ‖y‖ → ψ y = 0 := by
    intro y hy
    have := hvan 0 y hy
    have h2 := norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := ψ) (x := y)
    rw [this, norm_zero] at h2
    exact norm_eq_zero.1 h2.symm
  have h1 := fun i => sa12v3_D1_test hψ.1 hψ.2 hsupp i
  choose B1 hB1 using h1
  have h2 := fun i j => sa12v3_D1_test (sa12v3_D1_smooth hψ.1 i) (sa12v3_D1_compact hψ.2 i)
    (sa12v3_D1_supp hsupp i) j
  choose B2 hB2 using h2
  refine ⟨R, (∑ i, B1 i) + ∑ i, ∑ j, B2 i j, by linarith, ?_, fun i => (hB1 i).mono ?_, fun i j => (hB2 i j).mono ?_⟩
  · have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => (hB1 i).B_nonneg)
    have := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) =>
      Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) => (hB2 i j).B_nonneg))
    linarith
  · have h3 := Finset.single_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => (hB1 i).B_nonneg)
      (Finset.mem_univ i)
    have := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) =>
      Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) => (hB2 i j).B_nonneg))
    linarith
  · have h3 := Finset.single_le_sum (f := fun j => B2 i j) (fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) =>
      (hB2 i j).B_nonneg) (Finset.mem_univ j)
    have h4 := Finset.single_le_sum (f := fun i => ∑ j, B2 i j) (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) =>
      Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin d))) => (hB2 i j).B_nonneg))
      (Finset.mem_univ i)
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => (hB1 i).B_nonneg)
    linarith

end HRS.MH.AdjointRd.Phase2SA12V3
