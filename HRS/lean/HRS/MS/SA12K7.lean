import HRS.MS.SA12K6

/-!
# S.A.12 C1, regularity and bounds of the drift of a general periodic density

For `μ` with bounded jets up to order `m+3` and bounded cube `L¹` norms of its jets, the force part
`M ∇γ_L ⊛ μ` of `torusDriftL` is `C^{m+1}` with all derivatives bounded by `P (Bd + Bc)`,
where `P` depends only on `d, s, m, MB` (this is the second half of `expanding_tori_coefficients_B_proof`,
stated for an arbitrary density instead of the cutoff-normalised one).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MS.ToriCoefA HRS.MS.ToriCoefB

variable {d : ℕ}

theorem sa12k_drift_F (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (MB : ℝ) :
    ∃ P : ℝ, 0 ≤ P ∧ ∀ (L : ℝ), 1 ≤ L → ∀ γ : Euc d → ℝ, IsPeriodicRieszKernel d s L γ →
      ∀ M : Matrix (Fin d) (Fin d) ℝ, PDE.MatBound MB M → ∀ (μ : Euc d → ℝ) (Bd Bc : ℝ),
      0 ≤ Bd → 0 ≤ Bc → ContDiff ℝ ((m + 3 : ℕ) : WithTop ℕ∞) μ →
      (∀ i ≤ m + 3, ∀ y, ‖iteratedFDeriv ℝ i μ y‖ ≤ Bd) →
      (∀ i ≤ m + 1, ∀ x, ∫ z in tcb_Q d L, ‖iteratedFDeriv ℝ i μ (x - z)‖ ≤ Bc) →
      ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞)
        (fun x => Torus.matVec M (convGradConvL L (gradient γ) μ x)) ∧
      ∀ j ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ j
        (fun x => Torus.matVec M (convGradConvL L (gradient γ) μ x)) x‖ ≤ P * (Bd + Bc) := by
  obtain ⟨C₀, A₀, hC₀, hA₀, hkern⟩ := tcb_kern_coord hd hs0 hsd
  refine ⟨(d : ℝ) ^ 2 * |MB| * (d * (A₀ + C₀)), by positivity, ?_⟩
  intro L hL1 γ hγ M hM μ Bd Bc hBd hBc hcd hD hcube
  have hL0 : 0 < L := by linarith
  have hμ3 : ContDiff ℝ ((m + 1 + 2 : ℕ) : WithTop ℕ∞) μ := by
    have e : (m + 1 + 2 : ℕ) = m + 3 := by omega
    rw [e]; exact hcd
  have hμ1 : ContDiff ℝ 1 μ := hcd.of_le (by exact_mod_cast (by omega : 1 ≤ m + 3))
  have hμ0 : ∀ y, ‖μ y‖ ≤ Bd := fun y => by
    have := hD 0 (by omega) y
    rwa [norm_iteratedFDeriv_zero] at this
  have hμ1b : ∀ y, ‖fderiv ℝ μ y‖ ≤ Bd := fun y => by
    have := hD 1 (by omega) y
    rwa [norm_iteratedFDeriv_one] at this
  have hkc : ∀ i : Fin d, tcb_Kern L (fun z => gradient γ z i) C₀ ∧
      tcb_a (fun z => gradient γ z i) ≤ A₀ := fun i => hkern L hL1 γ hγ i
  set b : ℝ := A₀ * Bd + C₀ * Bc with hb
  have hb0 : 0 ≤ b := by positivity
  have hTi : ∀ i : Fin d,
      ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (tcb_T L (fun z => gradient γ z i) μ) ∧
      ∀ j ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ j (tcb_T L (fun z => gradient γ z i) μ) x‖ ≤ b := by
    intro i
    obtain ⟨h1, h2⟩ := tcb_main (hkc i).1 Bd Bc (m + 1) ℝ μ hμ3
      (fun i hi y => hD i (by omega) y) hcube
    refine ⟨h1, fun j hj x => (h2 j hj x).trans ?_⟩
    rw [hb]
    have := mul_le_mul_of_nonneg_right (hkc i).2 hBd
    linarith
  set F : Euc d → Euc d := convGradConvL L (gradient γ) μ with hF
  have hFc : ∀ x c, F x c = tcb_T L (fun z => gradient γ z c) μ x := fun x c =>
    tcb_conv_coord (gradient γ) (fun i => (hkc i).1) μ hμ1 Bd Bd hμ0 hμ1b x c
  have hFvec : F = fun x => ∑ i, tcb_T L (fun z => gradient γ z i) μ x •
      (EuclideanSpace.single i (1 : ℝ) : Euc d) := by
    funext x
    ext c
    rw [hFc x c]
    simp [Pi.single_apply]
  obtain ⟨hFcd, hFb⟩ := tcb_vec_bound (m + 1) (fun i => tcb_T L (fun z => gradient γ z i) μ) b
    (fun i => (hTi i).1) (fun i => (hTi i).2)
  rw [← hFvec] at hFcd hFb
  obtain ⟨Tm, hTm, hTmn⟩ := tcb_matVec_clm hd M MB hM
  have hTmn' : ‖Tm‖ ≤ (d : ℝ) ^ 2 * |MB| :=
    hTmn.trans (mul_le_mul_of_nonneg_left (le_abs_self MB) (by positivity))
  have hfun : (fun x => Torus.matVec M (F x)) = fun x => Tm (F x) := by
    funext x; rw [hTm]
  rw [hfun]
  refine ⟨Tm.contDiff.comp hFcd, fun j hj x => ?_⟩
  have h1 := Tm.norm_iteratedFDeriv_comp_left (hFcd.of_le (by exact_mod_cast hj)).contDiffAt
    (x := x) (le_refl (j : WithTop ℕ∞))
  have h2 := hFb j hj x
  have hbb : b ≤ (A₀ + C₀) * (Bd + Bc) := by rw [hb]; nlinarith
  calc _ ≤ ‖Tm‖ * ‖iteratedFDeriv ℝ j F x‖ := h1
    _ ≤ ((d : ℝ) ^ 2 * |MB|) * (d * b) :=
        mul_le_mul hTmn' h2 (norm_nonneg _) (by positivity)
    _ ≤ ((d : ℝ) ^ 2 * |MB|) * (d * ((A₀ + C₀) * (Bd + Bc))) := by
        gcongr
    _ = _ := by ring

end HRS.MH.AdjointRd.Phase2SA12Construction
