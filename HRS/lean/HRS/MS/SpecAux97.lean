import HRS.MS.SpecAux96

/-!
# S8M: the `L²(μ)` bound `∫ ‖∇U‖² dμ ≤ 8 (ω + d τ)` (S8.7, R4)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  Sum of `s8p_DU_L2_dir` over the standard orthonormal basis, with the
uniform bound `s8p_T_unif` for the commutator terms and `∫ ‖∇e‖² dμ = ω`.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal RealInnerProductSpace ContDiff

namespace HRS.MS.Spec

open HRS HRS.Whole HRS.MS.MovDec

variable {d : ℕ} {s : ℝ} {ρ : Euc d → ℝ}

local notation "𝓢R" => SchwartzMap (Euc d) ℝ

theorem s8p_DU_memLp (hd : 1 ≤ d) (hs0 : 0 < s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ)
    (φ : 𝓢R) (v : Euc d) :
    MemLp (fun x => fderiv ℝ (s8p_U d s ρ φ) x v) 2 (HRS.Whole.withDensityReal ρ) := by
  haveI := mov2e_isProb hρ
  have hGk := s8p_rhoDw_good hρ hE φ v
  have hGt := s8p_wDrho_good hρ hE φ v
  obtain ⟨bK, hbK⟩ := hGk.conv_bound hs0 hsd
  obtain ⟨bT, hbT⟩ := hGt.conv_bound hs0 hsd
  have hKm := s8p_convFun_meas (s := s) hGk.1
  have hTm := s8p_convFun_meas (s := s) hGt.1
  have hKL : MemLp (HRS.Whole.convFun (rieszKernel d s) (fun y => ρ y * fderiv ℝ (s8p_ws ρ φ) y v)) 2
      (HRS.Whole.withDensityReal ρ) :=
    MemLp.of_bound hKm.aestronglyMeasurable bK (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hbK x)
  have hTL : MemLp (HRS.Whole.convFun (rieszKernel d s) (fun y => s8p_ws ρ φ y * fderiv ℝ ρ y v)) 2
      (HRS.Whole.withDensityReal ρ) :=
    MemLp.of_bound hTm.aestronglyMeasurable bT (Filter.Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact hbT x)
  have : (fun x => fderiv ℝ (s8p_U d s ρ φ) x v) = fun x =>
      HRS.Whole.convFun (rieszKernel d s) (fun y => ρ y * fderiv ℝ (s8p_ws ρ φ) y v) x +
      HRS.Whole.convFun (rieszKernel d s) (fun y => s8p_ws ρ φ y * fderiv ℝ ρ y v) x :=
    funext fun x => s8p_DU_split hd hs0 hsd hρ hE φ x v
  rw [this]; exact hKL.add hTL

theorem s8p_DE_memLp (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hρ : Mov2eRho d ρ) (hE : Mov2eEll d ρ)
    (β : ℝ) (φ : 𝓢R)
    (hint : Integrable (fun x => ‖fderiv ℝ (s8p_E d s β ρ φ) x‖ ^ 2) (HRS.Whole.withDensityReal ρ))
    (v : Euc d) :
    MemLp (fun x => fderiv ℝ (s8p_E d s β ρ φ) x v) 2 (HRS.Whole.withDensityReal ρ) := by
  have hsm := s8p_E_smooth hd hs0 hsd hρ hE β φ
  have hcont : Continuous fun x => fderiv ℝ (s8p_E d s β ρ φ) x v :=
    (hsm.continuous_fderiv (by simp)).clm_apply continuous_const
  refine (memLp_two_iff_integrable_sq hcont.aestronglyMeasurable).2 ?_
  refine Integrable.mono' (hint.mul_const (‖v‖ ^ 2)) (hcont.pow 2).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc (fderiv ℝ (s8p_E d s β ρ φ) x v) ^ 2 ≤ (‖fderiv ℝ (s8p_E d s β ρ φ) x‖ * ‖v‖) ^ 2 := by
        have := (fderiv ℝ (s8p_E d s β ρ φ) x).le_opNorm v
        rw [Real.norm_eq_abs] at this
        exact sq_le_sq' (by linarith [abs_nonneg (fderiv ℝ (s8p_E d s β ρ φ) x v), neg_abs_le (fderiv ℝ (s8p_E d s β ρ φ) x v)]) (le_trans (le_abs_self _) this)
    _ = _ := by ring

theorem s8p_DU_L2 (hd : 1 ≤ d) (hs0 : 0 < s) (hsd : s < d) (h32 : 3 * s / 2 < d) (hρ : Mov2eRho d ρ)
    (hE : Mov2eEll d ρ) {M : ℝ} (hM : S8pRho d s ρ M) {β : ℝ} (hβ : 0 < β) :
    ∃ τ : ℝ, 0 ≤ τ ∧ ∀ (φ : 𝓢R) (om : ℝ), s8p_W2 ρ φ ≤ β →
      Integrable (fun x => ‖fderiv ℝ (s8p_E d s β ρ φ) x‖ ^ 2) (HRS.Whole.withDensityReal ρ) →
      ∫ x, ‖fderiv ℝ (s8p_E d s β ρ φ) x‖ ^ 2 ∂(HRS.Whole.withDensityReal ρ) = om →
      Integrable (fun x => ‖fderiv ℝ (s8p_U d s ρ φ) x‖ ^ 2) (HRS.Whole.withDensityReal ρ) ∧
        ∫ x, ‖fderiv ℝ (s8p_U d s ρ φ) x‖ ^ 2 ∂(HRS.Whole.withDensityReal ρ) ≤ 8 * (om + d * τ) := by
  obtain ⟨τ, hτ0, hτ⟩ := s8p_T_unif hd hs0 hsd h32 hρ hE hM hβ.le
  refine ⟨τ, hτ0, fun φ om hW hint hom => ?_⟩
  haveI := mov2e_isProb hρ
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set b := EuclideanSpace.basisFun (Fin d) ℝ with hb
  have hbn : ∀ i, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
  have hUi : ∀ i, Integrable (fun x => fderiv ℝ (s8p_U d s ρ φ) x (b i) ^ 2) μ := fun i =>
    (memLp_two_iff_integrable_sq (s8p_DU_memLp hd hs0 hsd hρ hE φ (b i)).aestronglyMeasurable).1
      (s8p_DU_memLp hd hs0 hsd hρ hE φ (b i))
  have hEi : ∀ i, Integrable (fun x => fderiv ℝ (s8p_E d s β ρ φ) x (b i) ^ 2) μ := fun i =>
    (memLp_two_iff_integrable_sq (s8p_DE_memLp hd hs0.le hsd hρ hE β φ hint (b i)).aestronglyMeasurable).1
      (s8p_DE_memLp hd hs0.le hsd hρ hE β φ hint (b i))
  have hNU : ∀ x, ‖fderiv ℝ (s8p_U d s ρ φ) x‖ ^ 2 = ∑ i, fderiv ℝ (s8p_U d s ρ φ) x (b i) ^ 2 :=
    fun x => (s8p_N_eq b (s8p_U d s ρ φ) x).symm
  have hNE : ∀ x, ‖fderiv ℝ (s8p_E d s β ρ φ) x‖ ^ 2 = ∑ i, fderiv ℝ (s8p_E d s β ρ φ) x (b i) ^ 2 :=
    fun x => (s8p_N_eq b (s8p_E d s β ρ φ) x).symm
  have hint' : Integrable (fun x => ‖fderiv ℝ (s8p_U d s ρ φ) x‖ ^ 2) μ := by
    simp_rw [hNU]
    exact integrable_finset_sum _ fun i _ => hUi i
  refine ⟨hint', ?_⟩
  have hsumE : ∫ x, ‖fderiv ℝ (s8p_E d s β ρ φ) x‖ ^ 2 ∂μ =
      ∑ i, ∫ x, fderiv ℝ (s8p_E d s β ρ φ) x (b i) ^ 2 ∂μ := by
    simp_rw [hNE]
    exact integral_finset_sum _ fun i _ => hEi i
  have hsumU : ∫ x, ‖fderiv ℝ (s8p_U d s ρ φ) x‖ ^ 2 ∂μ =
      ∑ i, ∫ x, fderiv ℝ (s8p_U d s ρ φ) x (b i) ^ 2 ∂μ := by
    simp_rw [hNU]
    exact integral_finset_sum _ fun i _ => hUi i
  have hdir : ∀ i, ∫ x, fderiv ℝ (s8p_U d s ρ φ) x (b i) ^ 2 ∂μ ≤
      8 * (∫ x, fderiv ℝ (s8p_E d s β ρ φ) x (b i) ^ 2 ∂μ + τ) := fun i => by
    refine (s8p_DU_L2_dir hd hs0 hsd hρ hE hβ φ (b i)
      (s8p_DE_memLp hd hs0.le hsd hρ hE β φ hint (b i))).trans ?_
    gcongr
    exact hτ φ hW (b i) (hbn i).le
  rw [hsumU]
  calc ∑ i, ∫ x, fderiv ℝ (s8p_U d s ρ φ) x (b i) ^ 2 ∂μ
      ≤ ∑ i : Fin d, 8 * (∫ x, fderiv ℝ (s8p_E d s β ρ φ) x (b i) ^ 2 ∂μ + τ) :=
        Finset.sum_le_sum fun i _ => hdir i
    _ = 8 * (om + d * τ) := by
        rw [← Finset.mul_sum, Finset.sum_add_distrib, ← hsumE, hom]
        simp

end HRS.MS.Spec
