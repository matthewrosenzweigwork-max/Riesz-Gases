import HRS.MS.SA12DE8E
import HRS.MS.SA12LimitL19

/-!
# S.A.12(c), packet E7.08 (worker S82Z2), part F: the tie of `adjoint_rd_sobolev` from the periodic box energy statement

`sa12de8_adjoint_rd_sobolev_of_box (hbox : Sa12BoxPeriodicStmt) : type_of% @HRS.Whole.AppendixA.adjoint_rd_sobolev`.

Proof: `sa12de8_sequence_data` (constant `Cbox` of `hbox`, chosen before `D, ν₀, μ`) gives the approximation sequence with the periodic
box energy data.  `sa12y_limit_data` gives a subsequence and a solution `G` of `IsUlocSolutionRd` with compact-test convergence at every time
and `G τ ∈ L²_loc`.  The given `F` equals `G` almost everywhere at each time (uniqueness of `adjoint_rd`, tie `sa12x3_adjoint_rd_from_cells`).
At each `τ`, `sa12de8_limit_bound` (zero-extended centred cells, weak compactness, lower semicontinuity, exact Plancherel jet identity of E7.07,
`δ → 0` with the cut-off datum estimate `sa12de7_periodic_datum_box_energy`) gives `‖G τ‖_{H^m} ≤ e^{Λ_m τ}‖φ‖_{H^m}`, which transfers to `F τ`.
Weak continuity follows from `forward_scalar_continuity` for `F` and `sobolev_weak_continuity`.
-/

set_option autoImplicit false
set_option maxHeartbeats 6400000
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.SA12DE8

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12Assembly HRS.MH.AdjointRd.Phase2SA12Limit

theorem sa12de8_adjoint_rd_sobolev_of_box (hbox : Sa12BoxPeriodicStmt) :
    type_of% @HRS.Whole.AppendixA.adjoint_rd_sobolev := by
  intro d hd s hs0 hsd hs m hm Rg MB Λ ΛV G₀ νbar T χ hχ
  obtain ⟨Cbox, hCbox, C, hCpos, hseqd⟩ :=
    sa12de8_sequence_data hbox d hd s hs0 hsd hs m hm Rg MB Λ ΛV G₀ νbar T χ hχ
  obtain ⟨C0, hC0pos, h0⟩ :=
    sa12x3_adjoint_rd_from_cells hd s hs0 hsd m hm Rg MB Λ ΛV G₀ νbar T χ hχ
  refine ⟨Cbox, hCbox, fun D ν₀ μ hD hR t ht φ hφsob hφ F hF => ?_⟩
  obtain ⟨a, Ln, hLpos, hLt, hsm, hbnd, hdat⟩ := hseqd D ν₀ μ hD hR t ht φ hφsob hφ
  obtain ⟨n, G, hn, hG, -, hGconv, hGloc⟩ :=
    sa12y_limit_data d hd s hs0 hsd m hm MB Λ ΛV G₀ νbar T χ hχ D μ hD t ht φ hφ _ a
  have huniq := (h0 D ν₀ μ hD hR t ht φ hφ).2 F G hF hG
  set lam : ℝ := Rg.lambdaM Cbox ν₀ (PDE.thetaOrder d s) with hlam
  set n0 : ℝ := Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (m : ℝ) φ) with hn0def
  have hn0 : 0 ≤ n0 := Real.sqrt_nonneg _
  -- the bound at each time, for `F τ`
  have hGE : ∀ τ ∈ Icc (0 : ℝ) t, HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) (F τ) ∧
      Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq (m : ℝ) (F τ)) ≤ Real.exp (lam * τ) * n0 := by
    intro τ hτ
    have hlim := sa12de8_limit_bound (m := m) (fun k => a.F (n k) τ) (fun k => a.datum (n k))
      (fun k => Ln (n k)) (G τ) (lam := lam) (τ := τ) (n0 := n0) hn0 (fun k => hLpos _)
      (hLt.comp hn.tendsto_atTop) (fun k => (hsm (n k) τ hτ).1) (fun k => (hsm (n k) τ hτ).2)
      (fun k => hbnd (n k) τ hτ) (fun δ hδ => hn.tendsto_atTop.eventually (hdat δ hδ))
      (sa12de8_locInt_of_ball (hGloc τ hτ)) (fun ψ hψ => hGconv ψ hψ τ hτ)
    have hae := huniq τ hτ
    have hFmem : HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) (F τ) := (sa12de8_sobolev_ae hae _).1.2 hlim.1
    refine ⟨hFmem, ?_⟩
    have hE : sobolevNormE (m : ℝ) (F τ) = sobolevNormE (m : ℝ) (G τ) := by
      unfold sobolevNormE
      rw [if_pos hFmem, if_pos hlim.1, (sa12de8_sobolev_ae hae _).2]
    have h2 := hlim.2
    rw [← hE] at h2
    unfold sobolevNormE at h2
    rw [if_pos hFmem] at h2
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.exp_pos _).le hn0)).1 h2
  refine ⟨fun τ hτ => (hGE τ hτ).1, ?_, fun τ hτ => (hGE τ hτ).2⟩
  -- weak continuity
  have hT : 0 ≤ t := ht.1.le
  refine HRS.MH.AdjointRd.Phase2SA12Limit.sobolev_weak_continuity hd m t (Real.exp (|lam| * t) * n0) F
    (fun τ hτ => ⟨(hGE τ hτ).1, (hGE τ hτ).2.trans ?_⟩)
    (fun ψ hψ => forward_scalar_continuity (D.coeff μ) t φ F hF.sol ψ hψ)
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) hn0
  calc lam * τ ≤ |lam| * τ := mul_le_mul_of_nonneg_right (le_abs_self _) hτ.1
    _ ≤ |lam| * t := mul_le_mul_of_nonneg_left hτ.2 (abs_nonneg _)

end HRS.MS.SA12DE8
