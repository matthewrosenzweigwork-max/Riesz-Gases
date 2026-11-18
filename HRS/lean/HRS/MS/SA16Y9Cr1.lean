import HRS.MS.SA16Y9Gc1

/-!
# S.A.16 (SA16Y9) Cr1: the stability estimate in the sub regime, modulo the source bound `Sa16SubSrc` (stability, G2d, part 4)

`Sa16SubSrc` is the explicit linear source bound (the G3 interface of `HANDOFF_SA16Y3.md`): for `v ∈ W^{m+2,p}`,
`‖(ν¹-ν²)Δ_m v + ι_m(B_{m+1}(bc¹_n) v - B_{m+1}(bc²_n) v) - (GInt¹_n - GInt²_n) ι²_m v‖ ≤ Ks (|ν¹-ν²| + δ) ‖v‖`.
`sa16y9_sub_stability`: under it, the `LpCase.sub` stability estimate of `adjoint_lp_stability` holds.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Cr1
variable {d : ℕ}

/-- the source bound required from the nonlocal and drift differences (sub regime) -/
def Sa16SubSrc (d : ℕ) (s : ℝ) (m : ℕ) (p : ℝ) [Fact (2 ≤ p)] (MB Λ ΛV G₀ νbar T : ℝ) : Prop :=
  ∃ Ks : ℝ, 0 ≤ Ks ∧ ∀ (D₁ D₂ : WholeDyn d) (μ₁ μ₂ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ),
    AdjointRdData s (m + 2) MB Λ ΛV G₀ νbar D₁ T μ₁ → AdjointRdData s (m + 2) MB Λ ΛV G₀ νbar D₂ T μ₂ →
    D₁.M = D₂.M → D₁.V = D₂.V → ∀ δ : ℝ, 0 ≤ δ →
    (∀ r ∈ Icc (0 : ℝ) T, coeffNormE d s m (μ₁ r - μ₂ r) ≤ ENNReal.ofReal δ) →
    ∀ t ∈ Ioc (0 : ℝ) T, ∀ n : ℕ, ∀ σ ∈ Icc (0 : ℝ) t, ∀ v : WmpSpace d (m + 1 + 1) p,
      ‖(D₁.invβ - D₂.invβ) • sa16so_Lap d m p v +
          sa16r_iota d m p (sa16so_B d (m + 1) p (sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D₁ (μ₁ r)) σ) v -
            sa16so_B d (m + 1) p (sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D₂ (μ₂ r)) σ) v) -
          (sa16y4_GInt d m (n + 1) p s D₁.M t μ₁ σ - sa16y4_GInt d m (n + 1) p s D₂.M t μ₂ σ)
            (sa16sz_iota2 d m p v)‖ ≤ Ks * (|D₁.invβ - D₂.invβ| + δ) * ‖v‖

end Cr1

end HRS.Whole.AppendixA.Phase2SA16R
