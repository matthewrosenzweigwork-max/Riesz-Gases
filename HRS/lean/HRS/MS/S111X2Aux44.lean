import HRS.MS.S111X2Aux43

/-!
# S11.1 X2, packet H02 (part 6): the response Gram matrices and the exact covariance difference
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxSynthPendingDepth 3
noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.S111X2

open HRS HRS.Whole
open HRS.Whole.Q34

variable {d : ℕ}

section Gram

variable {g : Euc d → ℝ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {K : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ} {Mg : ℝ}

theorem s111x2_Res_sum (hK : KRep g μ K Mg) {θ : ℝ} (hθ : 0 ≤ θ) {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (x : ι → Lp ℝ 2 μ) :
    s111x2_Res hK.posOp hθ (∑ p ∈ s, c p • x p) = ∑ p ∈ s, c p • s111x2_Res hK.posOp hθ (x p) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have := s111x2_Res_smul hK.posOp hθ 0 (0 : Lp ℝ 2 μ)
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, s111x2_Res_add, s111x2_Res_smul, ih]

/-- General positivity of the Gram matrix of the response form. -/
theorem s111x2_gram_psd_fin (hK : KRep g μ K Mg) {θ : ℝ} (hθ : 0 ≤ θ) {ι : Type*} (s : Finset ι)
    (F : ι → Euc d → ℝ) (hF : ∀ p, MemLp (F p) 2 μ) (c : ι → ℝ) :
    0 ≤ ∑ p ∈ s, ∑ q ∈ s, c p * c q * HRS.Whole.susceptibilityCov g μ θ (F p) (F q) := by
  set R := s111x2_Res hK.posOp hθ with hR
  have hb := (s111x2_Res_bounds hK.posOp hθ (∑ p ∈ s, c p • s111x2_cl (hF p))).1
  have hn : 0 ≤ ‖∑ p ∈ s, c p • s111x2_cl (hF p)‖ ^ 2 / (1 + θ * Mg) := by
    have := hK.nonneg
    positivity
  have h0 := hn.trans hb
  rw [← hR, hR, s111x2_Res_sum hK hθ] at h0
  rw [sum_inner] at h0
  refine h0.trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [s111x2_susc_eq hK hθ (hF p) (hF q), real_inner_smul_left, real_inner_smul_right]
  ring

theorem s111x2_susc_sub (hK : KRep g μ K Mg) {θ : ℝ} (hθ : 0 ≤ θ) {u v : Euc d → ℝ} (hu : MemLp u 2 μ)
    (hv : MemLp v 2 μ) :
    HRS.Whole.susceptibilityCov g μ θ (fun x => u x - v x) (fun x => u x - v x) =
      HRS.Whole.susceptibilityCov g μ θ u u - HRS.Whole.susceptibilityCov g μ θ u v -
        HRS.Whole.susceptibilityCov g μ θ v u + HRS.Whole.susceptibilityCov g μ θ v v := by
  have e : (fun x => u x - v x) = u + (-1 : ℝ) • v := by funext x; simp [sub_eq_add_neg]
  have hd : MemLp (u + (-1 : ℝ) • v) 2 μ := hu.add (hv.const_smul (-1))
  rw [e, s111x2_susc_eq hK hθ hd hd, s111x2_susc_eq hK hθ hu hu, s111x2_susc_eq hK hθ hu hv,
    s111x2_susc_eq hK hθ hv hu, s111x2_susc_eq hK hθ hv hv, s111x2_cl_lin hu hv (-1)]
  rw [s111x2_Res_add hK.posOp hθ, s111x2_Res_smul hK.posOp hθ]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  ring

end Gram

/-- The exact difference of the two window covariances. -/
theorem s111x2_pair_diff_eq (hd : 2 ≤ d) {s a β γ : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a)
    (hβ : 0 < β) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) {u t₁ t₂ : ℝ} (hu : 0 ≤ u) (ht₁ : 0 ≤ t₁)
    (ht₁₂ : t₁ ≤ t₂) {φ ψ : Euc d → ℝ} {f g : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) (u + t₁) φ f)
    (hg : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) (u + t₂) ψ g) :
    linearGaussianCov ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) β⁻¹
        (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ)
        (u + t₁) (u + t₂) φ ψ -
      linearGaussianCov ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) β⁻¹
        (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β) t₁ t₂ φ ψ =
      HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ
        (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 (u + t₁) φ)
        (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 (u + t₂) ψ) -
      HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β
        (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 (u + t₁) φ)
        (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 (u + t₂) ψ) := by
  obtain ⟨M, T⟩ := s111x2_td_of_thermal hd hs0 hs ha hβ hρ
  set C := (quadraticGradientDyn d s a β).coeff (fun _ => ρ) with hC
  have ht₂ : 0 ≤ t₂ := ht₁.trans ht₁₂
  have hr1 : 0 ≤ u + t₁ := by linarith
  have Q1 := s111x2_quench_ge (γ := γ) hd hs0 hs ha hβ hρ hr1 (by linarith : u + t₁ ≤ u + t₂) hf hg
  have hf₀ := s111x2_cls_shift T hu ht₁ hf
  have hg₀ := s111x2_cls_shift T hu ht₂ hg
  have Q2 := s111x2_quench_ge (γ := β) hd hs0 hs ha hβ hρ ht₁ ht₁₂ hf₀ hg₀
  have hsh := s111x2_prop_shift hd hs0 hs ha hβ hρ hu ht₁ ht₁₂ hg
  rw [Q1, Q2, hsh]
  ring

end HRS.MS.S111X2
