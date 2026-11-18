import HRS.MS.SA16Y9Cr2
import HRS.MS.SA16Y5Fin5

/-!
# S.A.16 (SA16Y9) Ci1: `Sa16IsoSrc`, the source bound required in the iso/hilbert regime `d-2 < s < d-1` (stability, step 1 of the iso pipeline)

Same shape as `Sa16SubSrc`, with the order-one nonlocal operators `sa16y5_NInt` (`W^{m+2,p} →L W^{m+1,p}`) of the interpolated, mollified densities in place of
`sa16y4_GInt`: for `v ∈ W^{m+2,p}`
`‖(ν¹-ν²)Δ_m v + ι_m(B_{m+1}(bc¹_n) v - B_{m+1}(bc²_n) v) - ι_m((NInt¹_n - NInt²_n) v)‖ ≤ Ks (|ν¹-ν²| + δ) ‖v‖`,
for level-`m+2` data with a common `M ∈ MCls` and common `V`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Ci1
variable {d : ℕ}

/-- the source bound required from the nonlocal and drift differences (iso/hilbert regime `s < d-1`) -/
def Sa16IsoSrc (d : ℕ) (s : ℝ) (m : ℕ) (p : ℝ) [Fact (2 ≤ p)] (MB Λ ΛV G₀ νbar T : ℝ)
    (MCls : Matrix (Fin d) (Fin d) ℝ → Prop) : Prop :=
  s < (d : ℝ) - 1 → 0 < s + 2 - d → (d : ℝ) < p * (s + 1) →
  ∃ Ks : ℝ, 0 ≤ Ks ∧ ∀ (D₁ D₂ : WholeDyn d) (μ₁ μ₂ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ),
    AdjointRdData s (m + 2) MB Λ ΛV G₀ νbar D₁ T μ₁ → AdjointRdData s (m + 2) MB Λ ΛV G₀ νbar D₂ T μ₂ →
    MCls D₁.M → D₁.M = D₂.M → D₁.V = D₂.V → ∀ δ : ℝ, 0 ≤ δ →
    (∀ r ∈ Icc (0 : ℝ) T, coeffNormE d s m (μ₁ r - μ₂ r) ≤ ENNReal.ofReal δ) →
    ∀ t ∈ Ioc (0 : ℝ) T, ∀ n : ℕ, ∀ σ ∈ Icc (0 : ℝ) t, ∀ v : WmpSpace d (m + 1 + 1) p,
      ‖(D₁.invβ - D₂.invβ) • sa16so_Lap d m p v +
          sa16r_iota d m p (sa16so_B d (m + 1) p (sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D₁ (μ₁ r)) σ) v -
            sa16so_B d (m + 1) p (sa16y4_bcInt d (n + 1) t (fun r => meanFieldDriftW D₂ (μ₂ r)) σ) v) -
          sa16r_iota d m p ((sa16y5_NInt d m (n + 1) p s D₁.M t μ₁ σ - sa16y5_NInt d m (n + 1) p s D₂.M t μ₂ σ) v)‖ ≤
        Ks * (|D₁.invβ - D₂.invβ| + δ) * ‖v‖

end Ci1

end HRS.Whole.AppendixA.Phase2SA16R
