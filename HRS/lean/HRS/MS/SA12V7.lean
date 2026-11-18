import HRS.MS.SA12AssemblyP3
import HRS.MS.AdjRdUniqueness

/-!
# S.A.12 P4 (conditional on P2): the frozen `adjoint_rd` from the periodic approximation sequence

The skeleton body of `adjoint_rd_from_cells` (Pro `SA12-ASSEMBLY.lean`, P4), with the producer P2
`sequence_from_cell_producers` as an explicit hypothesis `hP2` (P2 is not yet proved).  The limit passage is the
proved P3 `limit_from_sequence`; uniqueness is the proved adapter `HRS.MS.SA12BD.sa12_uniqueness`.
Once P2 is proved, `sa12v_adjoint_rd_of_P2 sequence_from_cell_producers` is the frozen tie.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Assembly

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd

/-- The statement of the producer P2 (verbatim from the skeleton). -/
def SA12P2Statement : Prop :=
  ∀ (d : ℕ) (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s<d) (m : ℕ) (hm : 1 ≤ m) (Rg : PDE.Regime)
    (MB Λ ΛV G₀ νbar T : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ),
    ∃ C : ℝ, 0<C ∧ ∀ (D : WholeDyn d) (ν₀ : ℝ) (μ : ℝ → Euc d → ℝ),
      AdjointRdData s m MB Λ ΛV G₀ νbar D T μ →
      RdRegimeHolds Rg d s D.M D.invβ ν₀ →
      ∀ t ∈ Ioc (0 : ℝ) T, ∀ φ : Euc d → ℝ, ulocNormE m χ φ<⊤ →
        Nonempty (ApproximationSequence χ m (D.coeff μ) t φ (rdProfile Rg C ν₀ s m χ φ))

-- BEGIN SA12.P4
/-- P4: the exact frozen assembly, conditional on the producer P2. -/
theorem sa12v_adjoint_rd_of_P2 (hP2 : SA12P2Statement) :
    type_of% @HRS.Whole.AppendixA.adjoint_rd := by
  intro d hd s hs0 hsd m hm Rg MB Λ ΛV G₀ νbar T χ hχ
  obtain ⟨C,hC,hSeq⟩ := hP2 d hd s hs0 hsd m hm Rg MB Λ ΛV G₀ νbar T χ hχ
  refine ⟨C,hC,?_⟩
  intro D ν₀ μ hD hR t ht φ hφ
  obtain ⟨a⟩ := hSeq D ν₀ μ hD hR t ht φ hφ
  obtain ⟨G,hG,hbound⟩ := limit_from_sequence d hd s hs0 hsd m hm MB Λ ΛV G₀ νbar T χ hχ D μ hD
    t ht φ hφ (rdProfile Rg C ν₀ s m χ φ) a
  refine ⟨⟨G,hG,?_⟩,?_⟩
  · intro τ hτ
    calc ulocNormE m χ (G τ) ≤ ENNReal.ofReal (rdProfile Rg C ν₀ s m χ φ τ) := hbound τ hτ
      _ = ENNReal.ofReal (C*Real.exp (Rg.lambdaM C ν₀ (PDE.thetaOrder d s)*τ))*ulocNormE m χ φ := by
        unfold rdProfile
        rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_toReal hφ.ne]
  · intro F₁ F₂ h₁ h₂
    exact HRS.MS.SA12BD.sa12_uniqueness d hd s hs0 hsd m hm Rg MB Λ ΛV G₀ νbar T χ hχ
      D ν₀ μ hD hR t ht φ F₁ F₂ h₁ h₂
-- END SA12.P4

end HRS.MH.AdjointRd.Phase2SA12Assembly
