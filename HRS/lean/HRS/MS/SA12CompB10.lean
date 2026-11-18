import HRS.Whole.AppendixAAdjoint
import HRS.MS.SA12CompB2
import HRS.MS.SA12CompB8
import HRS.MS.UlocModes
import HRS.MS.AdjRdNorms

/-!
# S.A.12 B10: the plane-wave clause (b), from the existence theorem

`adjoint_rd_planewave_of_existence`: the written assembly B10 with `adjoint_rd` (the content of P4) as the explicit
hypothesis `hex`.  B2, B8 and `UlocModes.uloc_embedding_modes_proof` are proved.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Companions

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd

-- BEGIN SA12.B10
theorem adjoint_rd_planewave_of_existence (hex : type_of% @HRS.Whole.AppendixA.adjoint_rd) :
    type_of% @HRS.Whole.AppendixA.adjoint_rd_planewave := by
  intro d hd s hs0 hsd m hm Rg MB Λ ΛV G₀ νbar T χ hχ
  obtain ⟨C₀,hC₀,hmain⟩ := hex hd s hs0 hsd m hm Rg MB Λ ΛV G₀ νbar T χ hχ
  obtain ⟨Cp,hp⟩ := HRS.MS.UlocModes.uloc_embedding_modes_proof m χ hχ
  let C := max C₀ (C₀*max 1 Cp)
  refine ⟨C,lt_of_lt_of_le hC₀ (le_max_left _ _),?_⟩
  intro D ν₀ μ hD hR t ht k φ hφ F hF τ hτ
  have hin : ulocNormE m χ φ ≤ ENNReal.ofReal (max 1 Cp*(1+‖k‖)^m) := by
    have hbase : ulocNormE m χ φ ≤ ENNReal.ofReal (Cp*(1+‖k‖)^m) := by
      rcases hφ with rfl|rfl
      · exact (hp k).1
      · exact (hp k).2
    exact hbase.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
  have hfin := lt_of_le_of_lt hin ENNReal.ofReal_lt_top
  obtain ⟨⟨G,hG,hGb⟩,huniq⟩ := hmain D ν₀ μ hD hR t ht φ hfin
  rw [← (norm_congr_ae m χ (G τ) (F τ) (huniq G F hG hF τ hτ)).1]
  have hrate := (rate_mono Rg C₀ C ν₀ s D.invβ D.M hR hC₀.le (le_max_left _ _)).2
  have hτ0 : 0 ≤ τ := hτ.1
  have hexp : Real.exp (Rg.lambdaM C₀ ν₀ (PDE.thetaOrder d s)*τ) ≤
      Real.exp (Rg.lambdaM C ν₀ (PDE.thetaOrder d s)*τ) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hrate hτ0)
  calc ulocNormE m χ (G τ)
      ≤ ENNReal.ofReal (C₀*Real.exp (Rg.lambdaM C₀ ν₀ (PDE.thetaOrder d s)*τ))*ulocNormE m χ φ := hGb τ hτ
    _ ≤ ENNReal.ofReal (C₀*Real.exp (Rg.lambdaM C₀ ν₀ (PDE.thetaOrder d s)*τ))*
        ENNReal.ofReal (max 1 Cp*(1+‖k‖)^m) := mul_le_mul' le_rfl hin
    _ ≤ ENNReal.ofReal (C*Real.exp (Rg.lambdaM C ν₀ (PDE.thetaOrder d s)*τ)*(1+‖k‖)^m) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      calc _ = (C₀*max 1 Cp)*Real.exp (Rg.lambdaM C₀ ν₀ (PDE.thetaOrder d s)*τ)*(1+‖k‖)^m := by ring
        _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul (le_max_right _ _) hexp (Real.exp_pos _).le
            (lt_of_lt_of_le hC₀ (le_max_left _ _)).le) (by positivity)
-- END SA12.B10

end HRS.MH.AdjointRd.Phase2SA12Companions
