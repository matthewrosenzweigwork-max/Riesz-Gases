import HRS.MS.Fp81S21Radius
import HRS.MS.Fp81S21OscDatum
import HRS.MS.R2InterpAux30
import HRS.MS.CovMeasAux2
import HRS.MS.S21F_D01

/-!
# HRS S2.1(iii), moving-reference interpolation inputs

The standing-data and physical-input vocabularies for a moving trajectory. The trajectory-only
producers and their scope are in `Fp81S21MovingInputs2.lean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Whole.AppendixA
open HRS.MS.R26T3 HRS.MS.CovMeas HRS.MS.R2Interp

/-- Moving-reference replacement for the stationary interpolation standing assumptions.
`hGram` is continuity of each uncut Gram entry on the interval where both observation orbits are active. -/
structure Fp81MovingStd
    {d : ℕ} (C : WholeCoeff d) (m H : ℝ)
    (r : ℕ) (c : MultiIndex d → ℝ) (hH : 0 < H) : Prop where
  hD : S101Data C m H r c
  hν : 0 ≤ C.ν
  hint : ∀ u ∈ Set.Icc (0 : ℝ) H, Integrable (C.ρ u)
  hnn : ∀ u ∈ Set.Icc (0 : ℝ) H, ∀ x, 0 ≤ C.ρ u x
  hcls : ∀ (α : MultiIndex d) (t : ℝ), t ∈ Set.Icc (0 : ℝ) H →
    ∃ f, IsClassicalAdjointW C t (oscTestFun m α) f
  hGram : ∀ (L : ℕ) (i j : Fin (s102_q d L)),
    ContinuousOn (fun u => s102_gram C m hH L u i j)
      (Set.Icc 0 (min (s102_tk hH L i) (s102_tk hH L j)))

/-- Exposed physical inputs for the moving-reference interpolation argument. -/
structure Fp81MovingPhysicalInputs
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (H : ℝ) : Prop where
  regular : ∃ Λ : ℝ, IsRegularMFRd p.s 3 Λ H R.ρ
  density_joint : Measurable
    (fun q : Set.Icc (0 : ℝ) H × Euc p.d => R.ρ q.1 q.2)
  round2 : ∃ M L : ℝ, ∀ u ∈ Set.Icc (0 : ℝ) H,
    IsRound2Density p.d p.s M L (R.ρ u)
  gaussian_upper : ∃ C₀ c₀ : ℝ, 0 < c₀ ∧
    ∀ u ∈ Set.Icc (0 : ℝ) H, ∀ x,
      R.ρ u x ≤ C₀ * Real.exp (-c₀ * ‖x‖ ^ 2)
  actual_density : ∃ q K : ℝ, 1 < q ∧
    ∀ u ∈ Set.Icc (0 : ℝ) H,
      HasR2ActualDensity p.s p.β q K
        (r26t3_mu R u) (A.P.map (A.X u.toNNReal))
  reference_moment : ∃ Mρ : ℝ, ∀ u ∈ Set.Icc (0 : ℝ) H,
    Integrable (fun x : Euc p.d => R.ρ u x * jbracket x ^ (2 * ((p.d : ℝ) + 2))) ∧
    (∫ x : Euc p.d, R.ρ u x * jbracket x ^ (2 * ((p.d : ℝ) + 2))) ≤ Mρ
  particle_moment : ∃ Cm : ℝ, ∀ u ∈ Set.Icc (0 : ℝ) H,
    Integrable (fun x : Euc p.d => HRS.Whole.jbracket x ^ ((p.d : ℝ) + 2))
      (HRS.Whole.meanEmpirical (A.P.map (A.X u.toNNReal))) ∧
    (∫ x : Euc p.d, HRS.Whole.jbracket x ^ ((p.d : ℝ) + 2)
      ∂(HRS.Whole.meanEmpirical (A.P.map (A.X u.toNNReal)))) ≤ Cm

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.Fp81MovingStd.mk
#print axioms HRS.Fp81.S21.Fp81MovingPhysicalInputs.mk
