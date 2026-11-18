import HRS.MS.IidInitAux8
import HRS.MP.RdInitClose

/-!
# SA27: S.A.27 `iid_init_path_rd` (transported independent initial fields on `ℝ^d`)

`iid_init_path_rd_proof` has exactly the type of the frozen statement
`HRS.Whole.AppendixALemmas.iid_init_path_rd` (`HRS/Whole/AppendixALemmas2.lean`; the unproved-statement warning of the tie is
expected).  Route: modulus and continuous versions from S.A.23 (`path_initial_modulus_rd_proof`), fixed-time `W₁`
convergence in `H^{-(Γ+2)}` (S.B.2 + the `L²` coupling with the stability input), finite-dimensional convergence
(Gaussian bridge and multi-time S.B.2), tightness from the weak convergence of the fixed-time marginals, and the
tight + finite-dimensional ⟹ weak convergence on `C([0,T]; H^{-q})` of `IidInitAux1/2`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.IidInit

theorem iid_init_path_rd_proof : type_of% @HRS.Whole.AppendixALemmas.iid_init_path_rd := by
  intro d s fd ν₀ MB Λ ΛV G₀ νbar T Cin C₀ m20 Kadj Cw Kst m₀ χ hχ S hs hT hinv hH R 𝔈 hid hst hpath
    ε hε εf Iemp I hTI hDist Iq Jq Zemp Zη hrepr hZe hZη L hL hStab hCC Ω' _ P' _ η' hη' J Jc hJm hJ
    hJc hΦc
  subst hT
  obtain ⟨C, hC⟩ := HRS.MP.RdInitClose.path_initial_modulus_rd_proof s fd ν₀ MB Λ ΛV G₀ νbar S.T
    Kadj Cw Cin m₀ hε.m₀_le χ hχ
  have h23 := hC S hs rfl hinv hH hst.matrix_bound hst.mean_field hst.potential hpath R ε
    (fun _ => ∅) hε εf Iemp I hTI hDist Iq Jq hrepr
  exact sa27_main S L R hid (fun N hN => (hst.flow N hN).init_meas) (fd.Gamma + 2) fd.Gamma m₀ Kadj Kst hε.m₀_pos hpath.adjoint
    hL.adjoint hStab hCC.tendsto Iq Jq Zemp Zη hrepr hZe hZη h23.2.1 h23.2.2 P' η' hη' J Jc hJm hJ
    hJc hΦc
