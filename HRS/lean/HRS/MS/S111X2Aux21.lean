import HRS.MS.S111X2Aux19
import HRS.MS.S111X1F2

/-!
# S11.1 X2, packets E04 (restriction and identification of the propagator) and E05 (exact quench identity)

* `s111x2_cls_restrict`: restriction of a classical adjoint solution on `[0,t]` to `[0,r]` is classical with terminal
  datum `f r`.
* `s111x2_prop_eq`: on the thermal reference `propagatorW C r t φ = f r` for any classical solution `f` (uniqueness `S85`).
* `s111x2_quench`: for `0 < r ≤ t` and classical solutions for `φ` on `[0,r]` and `ψ` on `[0,t]`,
  `Cov_γ(r,t)(φ,ψ) = C_β(φ, U^{r,t}ψ) + C_γ(U^{0,r}φ,U^{0,t}ψ) - C_β(U^{0,r}φ,U^{0,t}ψ)` (the noise covariance
  is exactly the response-form increment, E03).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X2

open HRS (Euc)
open HRS.Whole HRS.Whole.Q34

variable {d : ℕ}

theorem s111x2_cls_restrict {C : WholeCoeff d} {t r : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t φ f) (hr : 0 ≤ r) (hrt : r ≤ t) : IsClassicalAdjointW C r (f r) f := by
  have hsub : Icc (0 : ℝ) r ⊆ Icc 0 t := Icc_subset_Icc le_rfl hrt
  have hincl : Continuous fun p : Icc (0 : ℝ) r × Euc d => (Set.inclusion hsub p.1, p.2) :=
    ((continuous_inclusion hsub).comp continuous_fst).prodMk continuous_snd
  refine ⟨fun r' hr' => hf.c2 r' (hsub hr'), fun j hj => ?_, fun j hj => ?_, rfl, fun x r' hr' => ?_, ?_, ?_⟩
  · obtain ⟨B, hB⟩ := hf.bdd j hj
    exact ⟨B, fun r' hr' x => hB r' (hsub hr') x⟩
  · have h := (hf.cont_c2 j hj).comp hincl
    refine h.congr (fun p => ?_)
    rfl
  · exact hf.time_deriv x r' ⟨hr'.1, hr'.2.trans_le hrt⟩
  · have h := hf.cont_time_deriv.comp hincl
    refine h.congr (fun p => ?_)
    rfl
  · obtain ⟨B, hB⟩ := hf.bdd_time_deriv
    exact ⟨B, fun r' hr' x => hB r' (hsub hr') x⟩

variable {s β : ℝ}

/-- Identification of the propagator with a classical solution (thermal reference). -/
theorem s111x2_prop_eq (hd : 2 ≤ d) {s a β : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a) (hβ : 0 < β)
    {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) {t : ℝ} (ht : 0 ≤ t) {φ : Euc d → ℝ}
    {f : ℝ → Euc d → ℝ} (hf : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) t φ f)
    {r : ℝ} (hr : r ∈ Icc (0 : ℝ) t) :
    propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) r t φ = f r := by
  have hex : ∃ f', IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) t φ f' := ⟨f, hf⟩
  unfold propagatorW
  rw [dif_pos hex]
  exact HRS.MS.S111X1.uniq_of_thermal hd hs0 hs ha hβ hρ t ht φ _ f hex.choose_spec hf r hr

open HRS.MS.TcR (tc2_integral_nu)

/-- **E05.** The exact two-time covariance (quench identity). -/
theorem s111x2_quench (hd : 2 ≤ d) {s a β γ : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a) (hβ : 0 < β)
    {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) {r t : ℝ} (hr : 0 < r) (hrt : r ≤ t)
    {φ ψ : Euc d → ℝ} {f h' : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) r φ f)
    (hh : IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) t ψ h') :
    linearGaussianCov ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) β⁻¹
        (HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ) r t φ ψ =
      HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β φ
          (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) r t ψ) +
        HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) γ
          (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 r φ)
          (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 t ψ) -
        HRS.Whole.susceptibilityCov (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β
          (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 r φ)
          (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) 0 t ψ) := by
  set C := (quadraticGradientDyn d s a β).coeff (fun _ => ρ) with hC
  have ht : 0 ≤ t := hr.le.trans hrt
  have hhr : IsClassicalAdjointW C r (h' r) h' := s111x2_cls_restrict hh hr.le hrt
  obtain ⟨-, -, -, hftc⟩ := s111x2_classical_fd hd hs0 hs ha hβ hr hρ hf hhr
  have h1 := hftc 0 r le_rfl hr.le le_rfl
  obtain ⟨M, T⟩ := s111x2_td_of_thermal hd hs0 hs ha hβ hρ
  have p1 : ∀ s' ∈ Icc (0 : ℝ) r, propagatorW C s' r φ = f s' := fun s' hs' =>
    s111x2_prop_eq hd hs0 hs ha hβ hρ hr.le hf hs'
  have p2 : ∀ s' ∈ Icc (0 : ℝ) r, propagatorW C s' t ψ = h' s' := fun s' hs' =>
    s111x2_prop_eq hd hs0 hs ha hβ hρ ht hh ⟨hs'.1, hs'.2.trans hrt⟩
  have hnoise : noiseCovW C β⁻¹ r t φ ψ = 2 * β⁻¹ *
      ∫ s' in Icc 0 r, s111x2_dirichlet (HRS.Whole.withDensityReal ρ) (f s') (h' s') := by
    unfold noiseCovW
    rw [min_eq_left hrt]
    congr 1
    refine setIntegral_congr_fun measurableSet_Icc fun s' hs' => ?_
    beta_reduce
    rw [p1 s' hs', p2 s' hs']
    unfold s111x2_dirichlet
    rw [tc2_integral_nu T.prob]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [mul_comm]
    rfl
  have e_r : f r = φ := hf.terminal
  have e_hr : h' r = propagatorW C r t ψ := (s111x2_prop_eq hd hs0 hs ha hβ hρ ht hh ⟨hr.le, hrt⟩).symm
  have e_f0 : f 0 = propagatorW C 0 r φ := (p1 0 ⟨le_rfl, hr.le⟩).symm
  have e_h0 : h' 0 = propagatorW C 0 t ψ := (p2 0 ⟨le_rfl, hr.le⟩).symm
  unfold linearGaussianCov
  rw [hnoise, ← h1, e_r, e_hr, e_f0, e_h0]
  ring

end HRS.MS.S111X2
