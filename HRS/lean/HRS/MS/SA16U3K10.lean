import HRS.MS.SA16U3K10h

/-!
# S.A.16 K10: `splice_gradient_pair` (worker SA16U3)

Write `P_{lj} = ∫ ∂_l Z a T ∂_j Z`.  Then `2 P_{lj} = (P_{lj} + P_{jl}) + (P_{lj} - P_{jl})`.  The sum is
`-∫ ∂_l Z [T,a]∂_j Z` (skew-adjointness of `T`, bounded by K5); the difference is `-A_l + A_j` with
`A_l = ∫ ∂_l a T(∂_j Z) Z` (integration by parts, the mixed second derivative terms cancel), and
`A_l = -∫ T(∂_l a Z) ∂_j Z` is bounded by K8 at `p = 2`.  The statement is copied verbatim from
`SA16-COMPATIBLE-CUTOFF.lean`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Cutoff
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 HRS.CZ.ElemA

lemma sa16u3_cb_mono {d : ℕ} (a : Euc d → ℝ) : cbNorm 1 a ≤ cbNorm 2 a := by
  unfold cbNorm
  rw [Finset.sum_range_succ _ 2]
  have : 0 ≤ ⨆ z, ‖iteratedFDeriv ℝ 2 a z‖ := Real.iSup_nonneg fun _ => norm_nonneg _
  linarith

lemma sa16u3_pd1 {d : ℕ} (g : Euc d → ℝ) (k : Fin d) :
    partialDeriv (fun _ : Fin 1 => k) g = fun x => fderiv ℝ g x (EuclideanSpace.single k (1 : ℝ)) := by
  funext x
  unfold partialDeriv
  rw [iteratedFDeriv_one_apply]

open LineDeriv in
/-- K10: the gradient-pair exchange avoids an artificial derivative loss
in the Hilbert beta=1 terms. a=partial_l mu costs only three mu derivatives. -/
theorem splice_gradient_pair (d : ℕ) (hd : 1 ≤ d) (θ : ℝ)
    (hθ1 : 1 < θ) (hθ2 : θ < 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ i j l : Fin d,
      ∀ a : Euc d → ℝ, MemCb 2 a → ∀ Z : SchwartzMap (Euc d) ℝ,
      |∫ x, partialDeriv (fun _ : Fin 1 => l) Z x*a x*
          spliceOdd d θ δ i (partialDeriv (fun _ : Fin 1 => j) Z) x| ≤
        C*cbNorm 2 a*((∫ x, Z x^2)+(∫ x, ‖fderiv ℝ Z x‖^2)) := by
  haveI : Fact (2 ≤ (2 : ℝ)) := ⟨le_refl _⟩
  obtain ⟨C5, hC5, h5⟩ := splice_commutator_bound d hd θ 2 hθ1 hθ2 le_rfl
  obtain ⟨C8, hC8, h8⟩ := splice_h1_bound d hd θ 2 hθ1 hθ2
  refine ⟨C5 + 2 * C8 + 1, by positivity, fun δ hδ i j l a ha Z => ?_⟩
  have hδ0 : 0 < δ := hδ.1
  have ha2 : ContDiff ℝ 2 a := by simpa using ha.1
  have ha1 : MemCb 1 a := ⟨ha2.of_le (by norm_num), fun j hj => ha.2 j (by omega)⟩
  obtain ⟨B0, B1, B2, hB0, hB1, hB2, hcb, hcb1, h0, h1, h2⟩ := elema_cb2_data ha
  set el : Euc d := EuclideanSpace.single l (1 : ℝ) with hel
  set ej : Euc d := EuclideanSpace.single j (1 : ℝ) with hej
  have hnel : ‖el‖ = 1 := by simp [hel]
  have hnej : ‖ej‖ = 1 := by simp [hej]
  set Zl : SchwartzMap (Euc d) ℝ := ∂_{el} Z with hZl
  set Zj : SchwartzMap (Euc d) ℝ := ∂_{ej} Z with hZj
  have hmix : ∀ y, fderiv ℝ (⇑Zj) y el = fderiv ℝ (⇑Zl) y ej := by
    intro y
    exact congrArg (fun S : SchwartzMap (Euc d) ℝ => S y) (sa16u3_mixed_symm Z el ej)
  have hid := sa16u3_main_identity hd hθ1 hδ0 i ha2 h0 h1 Z Zl Zj el ej (fun x => rfl) (fun x => rfl) hmix
  rw [sa16u3_pd1, sa16u3_pd1]
  show |∫ x, Zl x * a x * spliceOdd d θ δ i (⇑Zj) x| ≤ _
  -- the pieces
  set P : ℝ := ∫ x, Zl x * a x * spliceOdd d θ δ i (⇑Zj) x with hP
  set nZ : ℝ := sa16u3_N (⇑Z) with hnZ
  set nG : ℝ := sa16u3_N (fun x => ‖fderiv ℝ Z x‖) with hnG
  set cb : ℝ := cbNorm 2 a with hcbdef
  have hcb0 : 0 ≤ cb := sa16u3_cb_nonneg 2 a
  have hnZ0 : 0 ≤ nZ := sa16u3_N_nonneg _
  have hnG0 : 0 ≤ nG := sa16u3_N_nonneg _
  have hZl_le : sa16u3_N (⇑Zl) ≤ nG := sa16u3_N_dir_le Z el hnel
  have hZj_le : sa16u3_N (⇑Zj) ≤ nG := sa16u3_N_dir_le Z ej hnej
  have hcb1le : cbNorm 1 a ≤ cb := sa16u3_cb_mono a
  -- symmetric part
  have hS := sa16u3_S_bound hd hθ1 hδ0 i hC5.le (fun a' ha' W => h5 δ hδ 1 ⟨zero_le_one, le_rfl⟩ i a' ha' W)
    ha1 Zl Zj
  have hS' : |∫ x, Zl x * (spliceOdd d θ δ i (fun y => a y * Zj y) x -
      a x * spliceOdd d θ δ i (⇑Zj) x)| ≤ C5 * cb * (nG * nG) := by
    refine hS.trans ?_
    have e1 : sa16u3_N (⇑Zl) * (C5 * cbNorm 1 a * sa16u3_N (⇑Zj)) ≤ nG * (C5 * cb * nG) :=
      mul_le_mul hZl_le
        (mul_le_mul (mul_le_mul_of_nonneg_left hcb1le hC5.le) hZj_le (sa16u3_N_nonneg _)
          (mul_nonneg hC5.le hcb0))
        (mul_nonneg (mul_nonneg hC5.le (sa16u3_cb_nonneg 1 a)) (sa16u3_N_nonneg _)) hnG0
    exact e1.trans (le_of_eq (by ring))
  -- antisymmetric part
  have hAl := sa16u3_A_bound hd hθ1 hδ0 i hC8.le (fun b hb Z' => h8 δ hδ i b hb Z') ha el hnel Z Zj
  have hAj := sa16u3_A_bound hd hθ1 hδ0 i hC8.le (fun b hb Z' => h8 δ hδ i b hb Z') ha ej hnej Z Zl
  have hAl' : |∫ x, fderiv ℝ a x el * spliceOdd d θ δ i (⇑Zj) x * Z x| ≤
      C8 * cb * ((nZ + nG) * nG) := by
    refine hAl.trans ?_
    have : 0 ≤ C8 * cb * (nZ + nG) := by positivity
    calc C8 * cb * (nZ + nG) * sa16u3_N (⇑Zj) ≤ C8 * cb * (nZ + nG) * nG :=
          mul_le_mul_of_nonneg_left hZj_le this
      _ = _ := by ring
  have hAj' : |∫ x, fderiv ℝ a x ej * spliceOdd d θ δ i (⇑Zl) x * Z x| ≤
      C8 * cb * ((nZ + nG) * nG) := by
    refine hAj.trans ?_
    have : 0 ≤ C8 * cb * (nZ + nG) := by positivity
    calc C8 * cb * (nZ + nG) * sa16u3_N (⇑Zl) ≤ C8 * cb * (nZ + nG) * nG :=
          mul_le_mul_of_nonneg_left hZl_le this
      _ = _ := by ring
  -- assemble
  have h2P : |2 * P| ≤ C5 * cb * (nG * nG) + (C8 * cb * ((nZ + nG) * nG) + C8 * cb * ((nZ + nG) * nG)) := by
    rw [hid]
    refine (abs_add_le _ _).trans (add_le_add (by rwa [abs_neg]) ((abs_add_le _ _).trans
      (add_le_add (by rwa [abs_neg]) hAj')))
  have hP2 : |P| ≤ (C5 * cb * (nG * nG) + (C8 * cb * ((nZ + nG) * nG) + C8 * cb * ((nZ + nG) * nG))) / 2 := by
    rw [abs_mul, abs_two] at h2P
    linarith
  -- the squares
  have hsqZ : ∫ x, Z x ^ 2 = nZ ^ 2 := by
    rw [← sa16u3_sq_eq (sa16u3_memLp_schwartz Z)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [Real.norm_eq_abs, sq_abs]
  have hsqG : ∫ x, ‖fderiv ℝ Z x‖ ^ 2 = nG ^ 2 := by
    rw [← sa16u3_sq_eq (sa16u3_memLp_gradnorm Z)]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [norm_norm]
  rw [hsqZ, hsqG]
  refine hP2.trans ?_
  have key : (C5 * (nG * nG) + (C8 * ((nZ + nG) * nG) + C8 * ((nZ + nG) * nG))) / 2 ≤
      (C5 + 2 * C8 + 1) * (nZ ^ 2 + nG ^ 2) := by
    nlinarith [mul_nonneg hC8.le (sq_nonneg (nZ - nG)), mul_nonneg hC5.le (sq_nonneg nZ),
      mul_nonneg hC5.le (sq_nonneg nG), sq_nonneg nZ, sq_nonneg nG,
      mul_nonneg hC8.le (sq_nonneg nZ), mul_nonneg hC8.le (sq_nonneg nG)]
  calc (C5 * cb * (nG * nG) + (C8 * cb * ((nZ + nG) * nG) + C8 * cb * ((nZ + nG) * nG))) / 2
      = cb * ((C5 * (nG * nG) + (C8 * ((nZ + nG) * nG) + C8 * ((nZ + nG) * nG))) / 2) := by ring
    _ ≤ cb * ((C5 + 2 * C8 + 1) * (nZ ^ 2 + nG ^ 2)) := mul_le_mul_of_nonneg_left key hcb0
    _ = (C5 + 2 * C8 + 1) * cb * (nZ ^ 2 + nG ^ 2) := by ring

end HRS.Whole.AppendixA.Phase2SA16Cutoff
