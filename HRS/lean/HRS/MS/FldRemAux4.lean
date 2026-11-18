import HRS.MS.FldRemAux3
import HRS.MS.StarTie

/-!
# S5.3 (`field_remainder`), part 4: uniqueness of classical adjoint solutions for the frozen coefficient (F-CAU)

For `D = ⟨s, -1, quadV Q 0, ν⟩` (`ν > 0`) and a Schwartz probability density `ρ`, the frozen coefficient is the one of
`propagatorW_unique_star` (a gradient drift, `c = -∇g*ρ`, `σ = 0`): we verify its hypotheses
(`CoeffHypRd` for the constant-in-time Schwartz `ρ`, `VHypRd` after symmetrizing `Q`, the regime `R1` or the corner
`UlocStarRegime`, since `-1` is symmetric nonpositive), and identify the coefficient with
`fixedViscosityCoeff s (-1) Q' ν c ρ`, `Q' = (Q + Qᵀ)/2`.  The result is `S52bUniq`.
-/

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S53

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.Ul HRS.MS.S52B HRS.MS.Go

variable {d : ℕ}

lemma s53_jbracket_le (x : Euc d) : jbracket x ≤ 1 + ‖x‖ := by
  unfold jbracket
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [norm_nonneg x]

/-- A rapidly decreasing function has finite weighted sup norms. -/
lemma s53_wse_of_rapid {h : Euc d → ℝ} (hh : HRS.MS.Ul.UlRapid h) (n : ℕ) (L : ℝ) :
    ∃ Λ : ℝ, weightedSupE n L h ≤ ENNReal.ofReal Λ := by
  choose C hC using fun j : ℕ => hh.2 j ⌈L⌉₊
  refine ⟨∑ j ∈ Finset.range (n + 1), |C j|, HRS.MS.Go.s55_dse_le fun j hj i x => ?_⟩
  have hj' : j ∈ Finset.range (n + 1) := Finset.mem_range.2 (by omega)
  have h1 : |partialDeriv i h x| ≤ ‖iteratedFDeriv ℝ j h x‖ := HRS.MP.RdInit.mri_abs_partialDeriv_le i h x
  have hjb1 : 1 ≤ jbracket x := HRS.MS.Adj.ad1_one_le_jb x
  have h2 : jbracket x ^ L ≤ (1 + ‖x‖) ^ ⌈L⌉₊ := by
    calc jbracket x ^ L ≤ jbracket x ^ ((⌈L⌉₊ : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hjb1 (Nat.le_ceil L)
      _ = jbracket x ^ ⌈L⌉₊ := Real.rpow_natCast _ _
      _ ≤ (1 + ‖x‖) ^ ⌈L⌉₊ := pow_le_pow_left₀ (by linarith) (s53_jbracket_le x) _
  have h3 : 0 ≤ |partialDeriv i h x| := abs_nonneg _
  calc jbracket x ^ L * |partialDeriv i h x| ≤ (1 + ‖x‖) ^ ⌈L⌉₊ * ‖iteratedFDeriv ℝ j h x‖ :=
        mul_le_mul h2 h1 h3 (by positivity)
    _ ≤ C j := hC j x
    _ ≤ |C j| := le_abs_self _
    _ ≤ ∑ j ∈ Finset.range (n + 1), |C j| :=
        Finset.single_le_sum (f := fun j => |C j|) (fun _ _ => abs_nonneg _) hj'


lemma s53_coeffHyp (hd1 : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) {ρ : Euc d → ℝ}
    (hρ : IsSchwartzDensity ρ) (T : ℝ) :
    ∃ Λ : ℝ, CoeffHypRd s 1 Λ T (fun _ => ρ) := by
  obtain ⟨hρp, ψ, hψ⟩ := hρ
  have hrap : HRS.MS.Ul.UlRapid ρ := by rw [← hψ]; exact HRS.MS.Ul.ult_schwartz_rapid ψ
  obtain ⟨Λ1, hw⟩ := s53_wse_of_rapid hrap 4 ((d : ℝ) + 3)
  obtain ⟨hmem, hfin, hcb⟩ := s55f_regular_slice (d := d) (n := 4) 4 le_rfl (le_refl ((d : ℝ) + 3))
    (hrap.1.of_le (by norm_num)) hw
  obtain ⟨-, -, -, hBd, -⟩ := HRS.MS.Ul.tail_conv_rapid hd1 hs0 hsd hrap
  obtain ⟨B, hB⟩ := hBd 0
  have hB0 : ∀ x, ‖convGradConvW (rieszKernelGrad d s) ρ x‖ ≤ B := fun x => by
    have := hB x
    rwa [norm_iteratedFDeriv_zero] at this
  have hBnn : 0 ≤ B := (norm_nonneg _).trans (hB0 0)
  refine ⟨max ((∑ j ∈ Finset.range 5, (d : ℝ) ^ j + 1) * max Λ1 0) (|(rieszConst d s)⁻¹| * B), ?_⟩
  refine ⟨fun _ _ => hρp, ⟨fun t ht => ⟨hmem, hfin, hcb.trans (le_max_left _ _)⟩, fun _ t ht x => ?_⟩, ?_⟩
  · refine le_trans ?_ (le_max_right _ _)
    show ‖(rieszConst d s)⁻¹ • convGradConvW (rieszKernelGrad d s) ρ x‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hB0 x) (abs_nonneg _)
  · intro ψ' _ _
    exact continuousOn_const


/-! ### The coefficient -/

lemma s53_matVec_neg_one (v : Euc d) : Torus.matVec (-1 : Matrix (Fin d) (Fin d) ℝ) v = -v := by
  simp [Torus.matVec]

lemma s53_inner_matVec_symm (Q : Matrix (Fin d) (Fin d) ℝ) (x : Euc d) :
    inner ℝ x (Torus.matVec Q x) = inner ℝ x (Torus.matVec (Torus.symPart Q) x) := by
  have h1 : Torus.matVec (Torus.symPart Q) x =
      (1 / 2 : ℝ) • (Torus.matVec Q x + Torus.matVec Q.transpose x) := by
    simp [Torus.symPart, Torus.matVec, map_add, map_smul]
  have h2 : inner ℝ x (Torus.matVec Q.transpose x) = inner ℝ x (Torus.matVec Q x) := by
    have : Torus.matVec Q.transpose x = (Matrix.toEuclideanLin Q).adjoint x := by
      have := Matrix.toEuclideanLin_conjTranspose_eq_adjoint Q
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial, Torus.matVec] using congrArg (fun A => A x) this
    rw [this, LinearMap.adjoint_inner_right]
    exact real_inner_comm _ _
  rw [h1, inner_smul_right, inner_add_right, h2]
  ring

lemma s53_symPart_isSymm (Q : Matrix (Fin d) (Fin d) ℝ) : (Torus.symPart Q).IsSymm := by
  unfold Matrix.IsSymm Torus.symPart
  rw [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]

lemma s53_quadV_symm (Q : Matrix (Fin d) (Fin d) ℝ) : quadV Q 0 = quadV (Torus.symPart Q) 0 := by
  funext x
  simp only [quadV, s53_inner_matVec_symm Q x]

lemma s53_grad_quadV (Q : Matrix (Fin d) (Fin d) ℝ) (x : Euc d) :
    gradient (quadV Q 0) x = Torus.matVec (Torus.symPart Q) x := by
  rw [s53_quadV_symm Q, HRS.MS.Adj.ad_gradient_quadV (s53_symPart_isSymm Q)]
  simp

lemma s53_coeff_eq (s ν : ℝ) (Q : Matrix (Fin d) (Fin d) ℝ) (ρ : Euc d → ℝ) :
    (⟨s, -1, quadV Q 0, ν⟩ : WholeDyn d).coeff (fun _ => ρ) =
      fixedViscosityCoeff s (-1) (Torus.symPart Q) ν
        (fun x => (fun _ : Euc d => (0 : Euc d)) x - convGradConvW (rieszKernelGrad d s) ρ x) ρ := by
  unfold WholeDyn.coeff fixedViscosityCoeff
  congr 1
  funext t x
  simp only [meanFieldDriftW, s53_matVec_neg_one, s53_grad_quadV]
  abel

/-! ### Uniqueness (F-CAU) for the frozen coefficient -/

lemma s53_uniq (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) {ν : ℝ} (hν : 0 < ν)
    (Q : Matrix (Fin d) (Fin d) ℝ) {ρ : Euc d → ℝ} (hρ : IsSchwartzDensity ρ) (T : ℝ) :
    S52bUniq ((⟨s, -1, quadV Q 0, ν⟩ : WholeDyn d).coeff (fun _ => ρ)) T := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨Λ, hΛ⟩ := s53_coeffHyp hd1 hs0 hsd hρ T
  obtain ⟨ΛV, G₀, hV⟩ := s55f_vhyp_quadV (d := d) (s53_symPart_isSymm Q) 0 (1 + 3)
  have hreg : RdRegimeHolds PDE.Regime.R1 d s (-1 : Matrix (Fin d) (Fin d) ℝ) ν 0 ∨
      HRS.MS.Star.UlocStarRegime d s (-1 : Matrix (Fin d) (Fin d) ℝ) := by
    by_cases hs : s ≤ (d : ℝ) - 2
    · exact Or.inl hs
    · refine Or.inr ⟨by linarith, ?_⟩
      refine HRS.MS.Star.star_matrix_symNonpos_of_lam (lam := 1) (A := 0) zero_le_one (by simp) (by simp)
  intro t ht φ f₁ f₂ h₁ h₂ r hr
  have hV' : VHypRd (1 + 3) ΛV G₀ (quadV Q 0) := by rw [s53_quadV_symm Q]; exact hV
  exact HRS.MS.Fcau.propagatorW_unique_star hd1 hs0 hsd 1 le_rfl PDE.Regime.R1 T Λ ΛV G₀
    (∑ i, ∑ j, |(-1 : Matrix (Fin d) (Fin d) ℝ) i j|) ν 0 (⟨s, -1, quadV Q 0, ν⟩ : WholeDyn d) (fun _ => ρ)
    rfl (s55f_matBound _) hV' ⟨hν.le, le_rfl⟩ hΛ hreg ht h₁ h₂ r hr

end HRS.MS.S53
