import HRS.Whole.Window
import HRS.MS.PoisKolmAux2

/-!
# S11.1 X1, part 1: gradient pairings of classical adjoint solutions
-/

set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111X1

open HRS HRS.Whole

variable {d : ℕ}

theorem x1_fderiv_eq (g : Euc d → ℝ) (x : Euc d) :
    fderiv ℝ g x = (continuousMultilinearCurryFin1 ℝ (Euc d) ℝ) (iteratedFDeriv ℝ 1 g x) := by
  ext v
  simp [continuousMultilinearCurryFin1]

/-- the gradient of a classical solution is jointly continuous -/
theorem x1_cont_fderiv {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (h : IsClassicalAdjointW C t φ f) :
    Continuous fun p : Set.Icc (0 : ℝ) t × Euc d => fderiv ℝ (f p.1) p.2 := by
  have := (continuousMultilinearCurryFin1 ℝ (Euc d) ℝ).continuous.comp (h.cont_c2 1 (by norm_num))
  convert this using 1
  funext p
  exact x1_fderiv_eq _ _

theorem x1_cont_gradient {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (h : IsClassicalAdjointW C t φ f) :
    Continuous fun p : Set.Icc (0 : ℝ) t × Euc d => gradient (f p.1) p.2 := by
  have := (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp (x1_cont_fderiv h)
  exact this

theorem x1_fderiv_bdd {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (h : IsClassicalAdjointW C t φ f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ x, ‖gradient (f r) x‖ ≤ B := by
  obtain ⟨B, hB⟩ := h.bdd 1 (by norm_num)
  refine ⟨max B 0, le_max_right _ _, fun r hr x => ?_⟩
  have := hB r hr x
  rw [norm_iteratedFDeriv_one] at this
  have e : ‖gradient (f r) x‖ = ‖fderiv ℝ (f r) x‖ := by
    unfold gradient
    exact (InnerProductSpace.toDual ℝ (Euc d)).symm.norm_map _
  rw [e]
  exact this.trans (le_max_left _ _)

theorem x1_pair_integrable {C : WholeCoeff d} {t t' : ℝ} {φ ψ : Euc d → ℝ} {f h : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t φ f) (hh : IsClassicalAdjointW C t' ψ h) {ρ : Euc d → ℝ}
    (hρi : Integrable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) t)
    (hs' : s ∈ Set.Icc (0 : ℝ) t') :
    Integrable fun x => inner ℝ (gradient (f s) x) (gradient (h s) x) * ρ x := by
  obtain ⟨Bf, hBf0, hBf⟩ := x1_fderiv_bdd hf
  obtain ⟨Bh, hBh0, hBh⟩ := x1_fderiv_bdd hh
  have hcf : Continuous fun x => gradient (f s) x :=
    (x1_cont_gradient hf).comp
      (Continuous.prodMk (continuous_const (y := (⟨s, hs⟩ : Set.Icc (0 : ℝ) t))) continuous_id)
  have hch : Continuous fun x => gradient (h s) x :=
    (x1_cont_gradient hh).comp
      (Continuous.prodMk (continuous_const (y := (⟨s, hs'⟩ : Set.Icc (0 : ℝ) t'))) continuous_id)
  refine (hρi.const_mul (Bf * Bh)).mono' ((hcf.inner hch).aestronglyMeasurable.mul hρi.aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 x)]
  refine mul_le_mul_of_nonneg_right ?_ (hρ0 x)
  exact (abs_real_inner_le_norm _ _).trans (mul_le_mul (hBf _ hs x) (hBh _ hs' x) (norm_nonneg _) hBf0)

theorem x1_pair_continuousOn {C : WholeCoeff d} {t t' T0 : ℝ} {φ ψ : Euc d → ℝ} {f h : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW C t φ f) (hh : IsClassicalAdjointW C t' ψ h) {ρ : Euc d → ℝ}
    (hρi : Integrable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (h1 : T0 ≤ t) (h2 : T0 ≤ t') :
    ContinuousOn (fun s => ∫ x, inner ℝ (gradient (f s) x) (gradient (h s) x) * ρ x)
      (Set.Icc (0 : ℝ) T0) := by
  obtain ⟨Bf, hBf0, hBf⟩ := x1_fderiv_bdd hf
  obtain ⟨Bh, hBh0, hBh⟩ := x1_fderiv_bdd hh
  rw [continuousOn_iff_continuous_domRestrict]
  let ι1 : Set.Icc (0 : ℝ) T0 → Set.Icc (0 : ℝ) t := Set.inclusion (Set.Icc_subset_Icc_right h1)
  let ι2 : Set.Icc (0 : ℝ) T0 → Set.Icc (0 : ℝ) t' := Set.inclusion (Set.Icc_subset_Icc_right h2)
  have hι1 : Continuous ι1 := continuous_inclusion _
  have hι2 : Continuous ι2 := continuous_inclusion _
  have hcf := x1_cont_gradient hf
  have hch := x1_cont_gradient hh
  refine continuous_of_dominated (bound := fun x => Bf * Bh * ρ x)
    (fun s => ?_) (fun s => Filter.Eventually.of_forall fun x => ?_) (hρi.const_mul _)
    (Filter.Eventually.of_forall fun x => ?_)
  · have hc : Continuous fun x : Euc d => inner ℝ (gradient (f (ι1 s)) x) (gradient (h (ι2 s)) x) :=
      (hcf.comp (Continuous.prodMk continuous_const continuous_id)).inner
        (hch.comp (Continuous.prodMk continuous_const continuous_id))
    exact (hc.aestronglyMeasurable).mul hρi.aestronglyMeasurable
  · show ‖inner ℝ (gradient (f s) x) (gradient (h s) x) * ρ x‖ ≤ Bf * Bh * ρ x
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 x)]
    refine mul_le_mul_of_nonneg_right ?_ (hρ0 x)
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (hBf _ (Set.Icc_subset_Icc_right h1 s.2) x) (hBh _ (Set.Icc_subset_Icc_right h2 s.2) x)
        (norm_nonneg _) hBf0)
  · have : Continuous fun s : Set.Icc (0 : ℝ) T0 => inner ℝ (gradient (f s) x) (gradient (h s) x) :=
      (hcf.comp (Continuous.prodMk hι1 continuous_const)).inner
        (hch.comp (Continuous.prodMk hι2 continuous_const))
    exact this.mul continuous_const

end HRS.MS.S111X1
