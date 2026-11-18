import HRS.MS.SA12AssemblyP3
import HRS.MS.SA12CompB2
import HRS.MS.AdjRdUniqueness

/-!
# S.A.12 B7: the weighted norm bound passes from an approximation sequence to the solution
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Companions

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Assembly HRS.MH.AdjointRd.Phase2SA12Limit

variable {d : ℕ}

-- BEGIN SA12.B7
theorem weighted_bound_from_sequence (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (m : ℕ) (hm : 1 ≤ m) (Rg : PDE.Regime) (MB Λ ΛV G₀ νbar T : ℝ)
    (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ)
    (D : WholeDyn d) (ν₀ : ℝ) (μ : ℝ → Euc d → ℝ)
    (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ)
    (hR : RdRegimeHolds Rg d s D.M D.invβ ν₀)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) T) (φ : Euc d → ℝ) (hφ : ulocNormE m χ φ < ⊤)
    (profile : ℝ → ℝ) (a : ApproximationSequence (d := d) χ m (D.coeff μ) t φ profile)
    (W : ℝ → ℝ≥0∞) (hW : ∀ n, ∀ τ ∈ Icc (0 : ℝ) t, varpiNormE m χ (a.F n τ) ≤ W τ)
    (F : ℝ → Euc d → ℝ) (hF : IsUlocSolutionRd χ m (D.coeff μ) t φ F) :
    ∀ τ ∈ Icc (0 : ℝ) t, varpiNormE m χ (F τ) ≤ W τ := by
  intro τ hτ
  obtain ⟨n, G, hn, hG, hbound, hconv, hGloc⟩ :=
    sa12y_limit_data d hd s hs0 hsd m hm MB Λ ΛV G₀ νbar T χ hχ D μ hD t ht φ hφ profile a
  have hGF := HRS.MS.SA12BD.sa12_uniqueness d hd s hs0 hsd m hm Rg MB Λ ΛV G₀ νbar T χ hχ D ν₀ μ hD
    hR t ht φ G F hG hF
  rw [← (norm_congr_ae m χ (G τ) (F τ) (hGF τ hτ)).2.1]
  have hlsc := (local_norm_lower_semicontinuity hd m χ hχ (profile τ) (fun k => a.F (n k) τ) (G τ)
    (hGloc τ hτ) (fun ψ hψ => hconv ψ hψ τ hτ) (fun k => a.bound (n k) τ hτ)).2.2
  refine hlsc.trans ?_
  calc liminf (fun k => varpiNormE m χ (a.F (n k) τ)) atTop
      ≤ liminf (fun _ : ℕ => W τ) atTop :=
        Filter.liminf_le_liminf (Eventually.of_forall fun k => hW (n k) τ hτ)
    _ = W τ := Filter.liminf_const _
-- END SA12.B7

end HRS.MH.AdjointRd.Phase2SA12Companions
