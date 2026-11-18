import HRS.MS.SA16Y5Jt1

/-!
# S.A.16 (SA16Y5) Jt2: linearity and jets of the heat-convolved nonlocal operator (K3, jets part 2)

`sa16y5_Fam a M μ φ = ∑_{ij} M_{ji} T_{a,√a}(μφ, (∂_jμ)φ)` (`= g_a ⋆ eucNonlocal s M μ φ`, `sa16y5_Fam_eq`).
`sa16y5_Fam_add`, `sa16y5_Fam_smul`: linear in `φ`; `sa16y5_Fam_smooth`; `sa16y5_pd_Fam`: `∂^idx Fam φ = ∑ M_{ji} T(∂^idx(μφ), ∂^idx((∂_jμ)φ))`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Jt2
variable {d : ℕ} {s : ℝ}

lemma sa16y5_cc_add {P P' : Euc d → ℝ} (hP : IsCcInfty P) (hP' : IsCcInfty P') :
    IsCcInfty (fun y => P y + P' y) := ⟨hP.1.add hP'.1, hP.2.add hP'.2⟩

lemma sa16y5_cc_smul {P : Euc d → ℝ} (hP : IsCcInfty P) (c : ℝ) : IsCcInfty (fun y => c * P y) :=
  ⟨contDiff_const.mul hP.1, hP.2.mul_left⟩

lemma sa16y5_T_add (hd : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (hsd1 : (d : ℝ) < s + 1) {a : ℝ} (ha : 0 < a)
    {ε : ℝ} (hε : 0 < ε) (i j : Fin d) {P P' Q Q' : Euc d → ℝ} (hP : IsCcInfty P) (hP' : IsCcInfty P')
    (hQ : IsCcInfty Q) (hQ' : IsCcInfty Q') :
    sa16y5_T d s a ε i j (fun y => P y + P' y) (fun y => Q y + Q' y) =
      fun x => sa16y5_T d s a ε i j P Q x + sa16y5_T d s a ε i j P' Q' x := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := sa16y5_kernels_int hd hs hsd hsd1 ha hε i j
  funext x
  unfold sa16y5_T
  rw [sa16y5_cv_cv_eq h1 h2 (sa16y5_cc_add hP hP'), sa16y5_cv_cv_eq h1 h3 (sa16y5_cc_add hQ hQ'),
    sa16y5_cv_cv_eq h5 h4 (sa16y5_cc_add hP hP'), sa16y5_cv_cv_eq h5 h6 (sa16y5_cc_add hQ hQ'),
    sa16y5_cv_cv_eq h1 h2 hP, sa16y5_cv_cv_eq h1 h3 hQ, sa16y5_cv_cv_eq h5 h4 hP, sa16y5_cv_cv_eq h5 h6 hQ,
    sa16y5_cv_cv_eq h1 h2 hP', sa16y5_cv_cv_eq h1 h3 hQ', sa16y5_cv_cv_eq h5 h4 hP', sa16y5_cv_cv_eq h5 h6 hQ']
  have l1 := sa16y5_cv_locInt h1 h2
  have l2 := sa16y5_cv_locInt h1 h3
  have l3 := sa16y5_cv_locInt h5 h4
  have l4 := sa16y5_cv_locInt h5 h6
  rw [sa16r_cv_add l1 hP hP', sa16r_cv_add l2 hQ hQ', sa16r_cv_add l3 hP hP', sa16r_cv_add l4 hQ hQ']
  ring

lemma sa16y5_T_smul (hd : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (hsd1 : (d : ℝ) < s + 1) {a : ℝ} (ha : 0 < a)
    {ε : ℝ} (hε : 0 < ε) (i j : Fin d) {P Q : Euc d → ℝ} (hP : IsCcInfty P) (hQ : IsCcInfty Q) (c : ℝ) :
    sa16y5_T d s a ε i j (fun y => c * P y) (fun y => c * Q y) =
      fun x => c * sa16y5_T d s a ε i j P Q x := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := sa16y5_kernels_int hd hs hsd hsd1 ha hε i j
  funext x
  unfold sa16y5_T
  rw [sa16y5_cv_cv_eq h1 h2 (sa16y5_cc_smul hP c), sa16y5_cv_cv_eq h1 h3 (sa16y5_cc_smul hQ c),
    sa16y5_cv_cv_eq h5 h4 (sa16y5_cc_smul hP c), sa16y5_cv_cv_eq h5 h6 (sa16y5_cc_smul hQ c),
    sa16y5_cv_cv_eq h1 h2 hP, sa16y5_cv_cv_eq h1 h3 hQ, sa16y5_cv_cv_eq h5 h4 hP, sa16y5_cv_cv_eq h5 h6 hQ]
  rw [sa16r_cv_smul, sa16r_cv_smul, sa16r_cv_smul, sa16r_cv_smul]
  ring

/-- `g_a ⋆ eucNonlocal` in `T`-form -/
def sa16y5_Fam (d : ℕ) (s a : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (μ φ : Euc d → ℝ) : Euc d → ℝ :=
  fun x => ∑ i, ∑ j, M j i * sa16y5_T d s a (Real.sqrt a) i j (fun y => μ y * φ y)
    (fun y => fderiv ℝ μ y (sa16z_e j) * φ y) x

theorem sa16y5_Fam_eq (hd : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (hsd1 : (d : ℝ) < s + 1) {a : ℝ} (ha : 0 < a)
    (M : Matrix (Fin d) (Fin d) ℝ) {μ φ : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ) (hφ : IsCcInfty φ) :
    sa16y5_Fam d s a M μ φ = sa16r_cv (sa16r_g d a) (HRS.MH.AdjointRd.eucNonlocal s M μ φ) := by
  funext x
  rw [sa16y5_cv_euc hd hs hsd hsd1 ha M hμ hφ x]
  unfold sa16y5_Fam
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [sa16y5_Tm_eq_T hd hs hsd hsd1 ha (Real.sqrt_pos.2 ha) hμ hφ i j]

lemma sa16y5_Fam_add (hd : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (hsd1 : (d : ℝ) < s + 1) {a : ℝ} (ha : 0 < a)
    (M : Matrix (Fin d) (Fin d) ℝ) {μ : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ) {φ ψ : Euc d → ℝ}
    (hφ : IsCcInfty φ) (hψ : IsCcInfty ψ) :
    sa16y5_Fam d s a M μ (fun y => φ y + ψ y) = sa16y5_Fam d s a M μ φ + sa16y5_Fam d s a M μ ψ := by
  funext x
  simp only [Pi.add_apply]
  unfold sa16y5_Fam
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hdm : ContDiff ℝ ∞ (fun y => fderiv ℝ μ y (sa16z_e j)) :=
    (hμ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have := sa16y5_T_add hd hs hsd hsd1 ha (Real.sqrt_pos.2 ha) i j (sa16y5_cc_mul hμ hφ) (sa16y5_cc_mul hμ hψ)
    (sa16y5_cc_mul hdm hφ) (sa16y5_cc_mul hdm hψ)
  have e1 : (fun y => μ y * (φ y + ψ y)) = fun y => μ y * φ y + μ y * ψ y := by funext y; ring
  have e2 : (fun y => fderiv ℝ μ y (sa16z_e j) * (φ y + ψ y)) =
      fun y => fderiv ℝ μ y (sa16z_e j) * φ y + fderiv ℝ μ y (sa16z_e j) * ψ y := by funext y; ring
  rw [e1, e2, this]
  beta_reduce
  ring

lemma sa16y5_Fam_smul (hd : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (hsd1 : (d : ℝ) < s + 1) {a : ℝ} (ha : 0 < a)
    (M : Matrix (Fin d) (Fin d) ℝ) {μ : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ) {φ : Euc d → ℝ}
    (hφ : IsCcInfty φ) (c : ℝ) :
    sa16y5_Fam d s a M μ (fun y => c * φ y) = c • sa16y5_Fam d s a M μ φ := by
  funext x
  simp only [Pi.smul_apply, smul_eq_mul]
  unfold sa16y5_Fam
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hdm : ContDiff ℝ ∞ (fun y => fderiv ℝ μ y (sa16z_e j)) :=
    (hμ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  have := sa16y5_T_smul hd hs hsd hsd1 ha (Real.sqrt_pos.2 ha) i j (sa16y5_cc_mul hμ hφ)
    (sa16y5_cc_mul hdm hφ) c
  have e1 : (fun y => μ y * (c * φ y)) = fun y => c * (μ y * φ y) := by funext y; ring
  have e2 : (fun y => fderiv ℝ μ y (sa16z_e j) * (c * φ y)) =
      fun y => c * (fderiv ℝ μ y (sa16z_e j) * φ y) := by funext y; ring
  rw [e1, e2, this]
  beta_reduce
  ring

lemma sa16y5_Fam_smooth (hd : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (hsd1 : (d : ℝ) < s + 1) {a : ℝ} (ha : 0 < a)
    (M : Matrix (Fin d) (Fin d) ℝ) {μ φ : Euc d → ℝ} (hμ : ContDiff ℝ ∞ μ) (hφ : IsCcInfty φ) :
    ContDiff ℝ ∞ (sa16y5_Fam d s a M μ φ) := by
  unfold sa16y5_Fam
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => contDiff_const.mul ?_
  have hdm : ContDiff ℝ ∞ (fun y => fderiv ℝ μ y (sa16z_e j)) :=
    (hμ.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
  exact sa16y5_T_smooth hd hs hsd hsd1 ha (Real.sqrt_pos.2 ha) i j (sa16y5_cc_mul hμ hφ) (sa16y5_cc_mul hdm hφ)

lemma sa16y5_pd_dsum {G : Fin d → Fin d → Euc d → ℝ} (hG : ∀ i j, ContDiff ℝ ∞ (G i j)) (c : Fin d → Fin d → ℝ)
    {l : ℕ} (idx : Fin l → Fin d) :
    partialDeriv idx (fun x => ∑ i, ∑ j, c i j * G i j x) =
      fun x => ∑ i, ∑ j, c i j * partialDeriv idx (G i j) x := by
  funext x
  unfold partialDeriv
  have hc : ∀ i j, ContDiffAt ℝ (l : ℕ) (fun x => c i j * G i j x) x := fun i j =>
    (contDiff_const.mul (hG i j)).contDiffAt.of_le (by exact_mod_cast le_top)
  have hc2 : ∀ i, ContDiffAt ℝ (l : ℕ) (fun x => ∑ j, c i j * G i j x) x := fun i =>
    (ContDiff.sum fun j _ => contDiff_const.mul (hG i j)).contDiffAt.of_le (by exact_mod_cast le_top)
  rw [iteratedFDeriv_fun_sum_apply (fun i _ => hc2 i)]
  simp only [ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_fun_sum_apply (fun j _ => hc i j)]
  simp only [ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have := iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (i := l) (a := c i j) (f := G i j) (x := x)
    ((hG i j).contDiffAt.of_le (by exact_mod_cast le_top))
  simp only [smul_eq_mul] at this
  rw [this]
  simp

end Jt2

end HRS.Whole.AppendixA.Phase2SA16R
