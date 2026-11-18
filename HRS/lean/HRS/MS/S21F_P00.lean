import HRS.MS.S21F_E18
import HRS.MS.S21F_D01

/-!
# S21F, packet R26-T3.P00: a filtered version of every frozen strong realization

From the full-range producer `r26t3_global_filtered_version` (E18) with the exact fields of `Particle`; `p.s < p.d/2` and `2 ≤ p.d`
give its weaker hypotheses `0 ≤ s < d`, `2 ≤ d`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.R26T3
open HRS HRS.Whole

structure FilteredParticle {p : Parameters} {δ : ℝ} {R : Trajectory p δ} {N : ℕ}
    (A : Particle R N) where
  ℱ : Filtration ℝ A.mΩ
  Wc : ℝ≥0 → A.Ω → (Fin N × Fin p.d) → ℝ
  X : ℝ≥0 → A.Ω → EucConfig p.d N
  filtered : IsWholeFilteredSolution A.P ℱ Wc A.W X
  negative : ∀ t : ℝ, t ≤ 0 → ℱ t = ℱ 0
  strong : ∀ H : ℝ, IsWholeStrongSolution A.P
    (quadraticGradientDyn p.d p.s p.a p.β) H A.X₀ A.W X
  indist : ∀ᵐ ω ∂A.P, ∀ t : ℝ≥0, X t ω = A.X t ω

theorem r26t3_filtered_particle {p : Parameters} {δ : ℝ} {R : Trajectory p δ} {N : ℕ}
    (A : Particle R N) : Nonempty (FilteredParticle A) := by
  have hsd : p.s < (p.d : ℝ) := by
    have := p.hs
    have : (0 : ℝ) < p.d := by exact_mod_cast (by have := p.hd; omega : 0 < p.d)
    linarith
  obtain ⟨ℱ, Wc, X', hF, hneg, hstr, hae⟩ := r26t3_global_filtered_version p.d N p.s p.a p.β p.hd
    p.hs0 hsd p.ha p.hβ A.P A.X₀ A.W A.X A.brownian A.independent A.strong
  exact ⟨⟨ℱ, Wc, X', hF, hneg, hstr, hae⟩⟩

end HRS.MS.R26T3
