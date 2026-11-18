import HRS.MS.SA12CompB1
import HRS.MS.SA12CompB3
import HRS.MS.SA12CompB5
import HRS.MS.SA12CompB8
import HRS.MS.FcauTie

/-!
# S.A.12 B9: the classical clause (a), from the existence theorem

`adjoint_rd_classical_of_existence`: the written assembly B9, with the (unproved) existence-and-uniqueness
statement `adjoint_rd` (the content of P4) taken as an explicit hypothesis `hex` in place of
`adjoint_rd_from_cells`.  Everything else is proved: B1, B3, B5, B8 and `Fcau.propagatorW_eq`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Companions

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.AdjointRd

-- BEGIN SA12.B9
theorem adjoint_rd_classical_of_existence (hex : type_of% @HRS.Whole.AppendixA.adjoint_rd) :
    type_of% @HRS.Whole.AppendixA.adjoint_rd_classical := by
  intro d hd s hs0 hsd Rg MB Λ ΛV G₀ νbar T χ hχ
  have hstar : 1 ≤ mStar d := by unfold mStar; omega
  obtain ⟨C₀,hC₀,hmain⟩ := hex hd s hs0 hsd (mStar d) hstar
    Rg MB Λ ΛV G₀ νbar T χ hχ
  obtain ⟨Ce,hCe,hrep⟩ := continuous_c2_representative hd χ hχ
  let C := max C₀ (Ce*C₀)
  have hC : 0 < C := lt_of_lt_of_le hC₀ (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro m hm D ν₀ μ hD hR t ht φ hφ hφfin F hF
  have hrest := restrict_data_and_solution s m (mStar d) hm MB Λ ΛV G₀ νbar T D μ hD
  have hφstar : ulocNormE (mStar d) χ φ<⊤ :=
    lt_of_le_of_lt (HRS.MS.SA12BD.sa12_uloc_mono d m (mStar d) hm χ φ) hφfin
  obtain ⟨⟨G,hG,hGb⟩,huniq⟩ := hmain D ν₀ μ hrest.1 hR t ht φ hφstar
  obtain ⟨u,huae,hucb,hub,huc⟩ := hrep (D.coeff μ) t φ G ht.1 hG
  have hcl := classical_of_regular_representative hd s hs0 hsd (mStar d) hstar
    MB Λ ΛV G₀ νbar T D μ hrest.1 t ht φ hφ G u hG.sol huae
    (fun τ hτ => (hucb τ hτ).1.1) hub huc
  have hGF := huniq G F hG (hrest.2 χ t φ F hF)
  refine ⟨⟨(fun r => u (t-r)),hcl,?_⟩,?_⟩
  · intro r hr
    have htr : t-r ∈ Icc (0 : ℝ) t := ⟨by linarith [hr.2],by linarith [hr.1]⟩
    exact (huae (t-r) htr).trans (hGF (t-r) htr)
  · intro r hr
    have htr : t-r ∈ Icc (0 : ℝ) t := ⟨by linarith [hr.2],by linarith [hr.1]⟩
    have heq := HRS.MS.Fcau.propagatorW_eq hd hs0 hsd (mStar d) hstar Rg
      T Λ ΛV G₀ MB νbar ν₀ D μ hrest.1.hs.1 hrest.1.hM hrest.1.hV
      hrest.1.hν hrest.1.hμ hR ⟨ht.1.le,ht.2⟩ hcl r hr
    rw [heq]
    refine ⟨(hucb (t-r) htr).1, (hucb (t-r) htr).2.trans ?_⟩
    have hb := ENNReal.toReal_mono
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hφstar).ne (hGb (t-r) htr)
    rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity)] at hb
    have hrate := (rate_mono Rg C₀ C ν₀ s D.invβ D.M hR hC₀.le (le_max_left _ _)).2
    have hexp : Real.exp (Rg.lambdaM C₀ ν₀ (PDE.thetaOrder d s)*(t-r)) ≤
        Real.exp (Rg.lambdaM C ν₀ (PDE.thetaOrder d s)*(t-r)) :=
      Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right hrate htr.1)
    calc Ce*(ulocNormE (mStar d) χ (G (t-r))).toReal
        ≤ Ce*(C₀*Real.exp (Rg.lambdaM C₀ ν₀ (PDE.thetaOrder d s)*(t-r))*
            (ulocNormE (mStar d) χ φ).toReal) := mul_le_mul_of_nonneg_left hb hCe.le
      _ = (Ce*C₀)*Real.exp (Rg.lambdaM C₀ ν₀ (PDE.thetaOrder d s)*(t-r))*
            (ulocNormE (mStar d) χ φ).toReal := by ring
      _ ≤ C*Real.exp (Rg.lambdaM C ν₀ (PDE.thetaOrder d s)*(t-r))*
            (ulocNormE (mStar d) χ φ).toReal :=
        mul_le_mul_of_nonneg_right (mul_le_mul (le_max_right _ _) hexp (Real.exp_pos _).le hC.le)
          ENNReal.toReal_nonneg
-- END SA12.B9

end HRS.MH.AdjointRd.Phase2SA12Companions
