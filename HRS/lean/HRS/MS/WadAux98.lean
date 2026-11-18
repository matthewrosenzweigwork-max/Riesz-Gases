import HRS.MS.WadAux97

/-!
# S8.3, packet S8E-6, part 2: assembly of `weighted_adjoint_decay` from the open clauses

The four clauses of the frozen statement that are not yet proved for all `j` are isolated as the propositions
`S8eC2b` ((2b), all `j`; proved for `j ≤ 1` in `s8e_clause2b_le_one`), `S8eC3` ((3), all `j`; proved for `j ≤ 1` in
`s8e_clause3_le_one`), `S8eC4b` ((4b)) and `S8eC5` ((5), pair inverse).  `s8e_wad_of_open` assembles the frozen statement from
them, with the existence conjunct, clause (2a) and clause (4a) proved.  Once the four hypotheses are discharged, the
frozen row is `fun hd a β ha hβ ρβ hρ M hM => s8e_wad_of_open hd ha hβ hρ hM h2b h3 h4b h5`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

/-- Clause (2b) of the frozen statement, for the semigroup `U`. -/
def S8eC2b (a β : ℝ) (ρβ : Euc d → ℝ) (M : ℝ) (U : ℝ → (Euc d → ℝ) → Euc d → ℝ) : Prop :=
  ∀ j : ℕ, ∃ Cj c : ℝ, 0 < c ∧ ∀ t : ℝ, 1 ≤ t → ∀ f, MemCM M f →
    MemCMj M j (U t (HRS.Whole.projMean (HRS.Whole.withDensityReal ρβ) f)) ∧
    weightedSupE j (-M) (U t (HRS.Whole.projMean (HRS.Whole.withDensityReal ρβ) f)) ≤
      ENNReal.ofReal (Cj * Real.exp (-c * t)) * weightedSupE 0 (-M) f

/-- Clause (3) of the frozen statement. -/
def S8eC3 (M : ℝ) (U : ℝ → (Euc d → ℝ) → Euc d → ℝ) : Prop :=
  ∀ (j : ℕ) (T : ℝ), 0 ≤ T → ∃ K : ℝ, ∀ t ∈ Set.Icc 0 T, ∀ f, MemCMj M j f →
    MemCMj M j (U t f) ∧ weightedSupE j (-M) (U t f) ≤ ENNReal.ofReal K * weightedSupE j (-M) f

/-- Clause (4b) of the frozen statement. -/
def S8eC4b (a β : ℝ) (ρβ : Euc d → ℝ) (M : ℝ) (U : ℝ → (Euc d → ℝ) → Euc d → ℝ) : Prop :=
  ∀ j : ℕ, ∃ Cj c : ℝ, 0 < c ∧ ∀ t : ℝ, 1 ≤ t → ∀ R : Euc d → Euc d → ℝ, MemCMpair M 0 R →
    IsDoublyCentered (HRS.Whole.withDensityReal ρβ) R →
    MemCMpair M j (tensorU U t R) ∧
    pairNormE M j (tensorU U t R) ≤ ENNReal.ofReal (Cj * Real.exp (-c * t)) * pairNormE M 0 R

/-- Clause (5) (pair inverse) of the frozen statement. -/
def S8eC5 (a β : ℝ) (ρβ : Euc d → ℝ) (M : ℝ) (U : ℝ → (Euc d → ℝ) → Euc d → ℝ) : Prop :=
  ∀ j : ℕ, 2 ≤ j → ∀ R : Euc d → Euc d → ℝ, ContDiff ℝ j (Function.uncurry R) →
    IsDoublyCentered (HRS.Whole.withDensityReal ρβ) R →
    (∃ K : ℝ, K < M ∧ ∀ k : ℕ, k ≤ j → ∃ CR : ℝ, ∀ x y : Euc d,
      ‖iteratedFDeriv ℝ k (Function.uncurry R) (x, y)‖ ≤ CR * jbracket x ^ K * jbracket y ^ K) →
    (∀ x y, IntegrableOn (fun t => tensorU U t R x y) (Set.Ioi 0)) ∧
    ContDiff ℝ j (Function.uncurry (pairInverseW U R)) ∧
    (∀ k : ℕ, k ≤ j → ∃ CΨ : ℝ, ∀ x y : Euc d,
      ‖iteratedFDeriv ℝ k (Function.uncurry (pairInverseW U R)) (x, y)‖ ≤
        CΨ * jbracket x ^ M * jbracket y ^ M) ∧
    ∀ x y : Euc d,
      -(projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) 0
          (fun x' => pairInverseW U R x' y) x +
        projGeneratorW (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) 0
          (pairInverseW U R x) y) = R x y

theorem s8e_wad_of_open (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) {ρβ : Euc d → ℝ}
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) {M : ℝ} (hM : 0 < M)
    (h2b : ∀ U, IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U → S8eC2b a β ρβ M U)
    (h3 : ∀ U, IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U → S8eC3 M U)
    (h4b : ∀ U, IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U → S8eC4b a β ρβ M U)
    (h5 : ∀ U, IsWeightedSemigroup (critCoeff d a β ρβ) (HRS.Whole.withDensityReal ρβ) M U → S8eC5 a β ρβ M U) :
    type_of% (@HRS.Whole.weighted_adjoint_decay d hd a β ha hβ ρβ hρ M hM) := by
  refine ⟨⟨s85_Ulim a β ρβ M, s85_exists_semigroup hd ha hβ hρ hM⟩, fun U hU => ?_⟩
  exact ⟨s8d_clause2a hd ha hβ hρ hM hU, h2b U hU, h3 U hU, s8e_clause4a hd ha hβ hρ hM hU,
    h4b U hU, h5 U hU⟩

end HRS.MS.Wad
