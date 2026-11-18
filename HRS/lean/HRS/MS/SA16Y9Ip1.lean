import HRS.MS.SA16Y9Tl1
import HRS.MS.SA16Y4Ex1

/-!
# S.A.16 (SA16Y9) Ip1: a weakly continuous bounded path with the weak identity is an `IsLpSolutionRd` (stability, G2d, part 1)

`sa16y9_isLp_of_path`: the packaging step of `sa16y4_sub_exists` (Ex1), for any level `m`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Ip1
variable {d : ℕ}

set_option maxHeartbeats 1600000 in
theorem sa16y9_isLp_of_path (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m) (p : ℝ)
    [Fact (2 ≤ p)] (MB Λ ΛV G₀ νbar T : ℝ) (χ : EuclideanSpace ℝ (Fin d) → ℝ) (hχ : IsUlocCutoff χ)
    (D : WholeDyn d) (μ : ℝ → EuclideanSpace ℝ (Fin d) → ℝ) (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T) (φ : EuclideanSpace ℝ (Fin d) → ℝ) (G : ℝ → WmpSpace d m p) (Bg : ℝ)
    (hbd : ∀ τ ∈ Icc (0 : ℝ) t, ‖G τ‖ ≤ Bg)
    (hGw : ∀ ℓ : StrongDual ℝ (WmpSpace d m p), ContinuousOn (fun τ => ℓ (G τ)) (Icc (0 : ℝ) t))
    (hGid : ∀ {ψ : EuclideanSpace ℝ (Fin d) → ℝ}, IsCcInfty ψ →
          (∀ τ ∈ Icc (0 : ℝ) t, ∫ x, (fun τ x => wrep d m p (G τ) x) τ x * ψ x = (∫ x, φ x * ψ x) +
            ∫ σ in Icc (0 : ℝ) τ, forwardWeakTerm (D.coeff μ) t (fun τ x => wrep d m p (G τ) x) ψ σ) ∧
          IntegrableOn (fun σ => forwardWeakTerm (D.coeff μ) t (fun τ x => wrep d m p (G τ) x) ψ σ) (Icc 0 t)) :
    IsLpSolutionRd m p χ (D.coeff μ) t φ (fun τ x => wrep d m p (G τ) x) := by
  refine ⟨⟨?_, ?_, ?_⟩, sa16y3_wcont_of_path (Bg := Bg) G hGw, sa16y3_bounded_of_path G hbd, ?_⟩
  · intro ψ hψ σ hσ
    exact sa16y4_integrable_fields hd s hs0 hsd m hm p MB Λ ΛV G₀ νbar T D μ hD ht (G σ) hψ hσ
  · intro ψ hψ
    exact (hGid hψ).2
  · intro ψ hψ τ hτ
    exact (hGid hψ).1 τ hτ
  · intro m' hm' z τ₀ hτ₀ ε hε
    obtain ⟨h1, h2, h3⟩ := sa16y4_shift_cutoff hχ z
    exact sa16y4_cont_abstract m m' hm' h1 h2 h3 G hbd hGw hτ₀ hε

end Ip1

end HRS.Whole.AppendixA.Phase2SA16R
