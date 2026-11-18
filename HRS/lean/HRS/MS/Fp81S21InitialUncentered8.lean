import HRS.MS.Fp81S21InitialUncentered9

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open S45
open HRS.Whole
open HRS (Euc)

/-- Symmetry of the Riesz potential against the centered corrector generator. The positive
power case uses `Q34.tk_symm`; the logarithmic case uses the shifted-log kernel symmetry. -/
theorem fp81s21_initial_integral_kernel_gen_symm
    {d : ℕ} {s q C c BU BB : ℝ} {ρ : Euc d → ℝ} {Bd : Euc d → Euc d}
    (hT : S47.TRef d s ρ q C c BU BB Bd)
    (hs0 : 0 ≤ s) (hsd : s < (d : ℝ))
    {χ : Euc d → ℝ} (hχ : ContDiff ℝ 2 χ)
    {B1 B2 : ℝ} (hB1 : ∀ x, ‖gradient χ x‖ ≤ B1)
    (hB2 : ∀ x, ‖fderiv ℝ (gradient χ) x‖ ≤ B2)
    (hgen2 : MemLp (HRS.Whole.weightedGen ρ χ) 2 (HRS.Whole.withDensityReal ρ)) :
    ∫ x, (∫ y, HRS.Whole.rieszKernel d s (x - y) * HRS.Whole.weightedGen ρ χ y
      ∂(HRS.Whole.withDensityReal ρ)) ∂(HRS.Whole.withDensityReal ρ) =
    ∫ y, HRS.Whole.convMeasure (HRS.Whole.rieszKernel d s)
      (HRS.Whole.withDensityReal ρ) y * HRS.Whole.weightedGen ρ χ y
      ∂(HRS.Whole.withDensityReal ρ) := by
  let μ : Measure (Euc d) := HRS.Whole.withDensityReal ρ
  let g : Euc d → ℝ := HRS.Whole.weightedGen ρ χ
  have hμ : IsProbabilityMeasure μ := by
    dsimp [μ]
    exact HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  letI : IsProbabilityMeasure μ := hμ
  have hg2 : MemLp g 2 μ := hgen2
  have hmean : ∫ x, g x ∂μ = 0 := by
    dsimp [g, μ]
    exact fp81s21_initial_integral_weightedGen_zero hT hχ hB1 hB2
  have hgmeas : Measurable g := by
    have heq : g = fun x => -Laplacian.laplacian χ x +
        ⟪q • x - Bd x, gradient χ x⟫ := by
      funext x
      exact S47.s47_gen_eq hT (χ := χ) x
    rw [heq]
    have hv : ContDiff ℝ 1 (gradient χ) := s45_contDiff_gradient hχ
    have hdiv : Continuous (fun x => S45.s45_div (gradient χ) x) :=
      s45_continuous_div hv
    have hlap : Laplacian.laplacian χ = S45.s45_div (gradient χ) :=
      funext fun x => (s45_div_gradient hχ x).symm
    rw [hlap]
    have hDrift : Continuous (fun x : Euc d => q • x - Bd x) :=
      (continuous_id.const_smul q).sub hT.Bd_cont
    exact (hdiv.neg.add (hDrift.inner hv.continuous)).measurable
  have h1m : Measurable (fun _ : Euc d => (1 : ℝ)) := measurable_const
  have h12 : MemLp (fun _ : Euc d => (1 : ℝ)) 2 μ := memLp_const 1
  by_cases hs : 0 < s
  · have hdpos : 0 < d := by exact_mod_cast (lt_trans hs hsd)
    have hd1 : 1 ≤ d := by omega
    have hM : ∀ x, ρ x ≤ C := S47.s47_le hT
    have hsym := HRS.Whole.Q34.tk_symm hd1 hs hsd hT.prob hM
      hgmeas h1m hg2 h12
    have htkGen : ∀ x, HRS.Whole.Q34.Tk s μ g x =
        ∫ y, rieszKernel d s (x - y) * g y ∂μ := by
      intro x
      unfold HRS.Whole.Q34.Tk
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      change ‖x - y‖ ^ (-s) * g y = rieszKernel d s (x - y) * g y
      rw [HRS.Whole.Q34.rieszKernel_eq (d := d) (s := s) hs.ne' (x - y)]
    have htkOne : ∀ x, HRS.Whole.Q34.Tk s μ (fun _ => (1 : ℝ)) x =
        HRS.Whole.convMeasure (HRS.Whole.rieszKernel d s) μ x := by
      intro x
      unfold HRS.Whole.Q34.Tk HRS.Whole.convMeasure
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      change ‖x - y‖ ^ (-s) * (1 : ℝ) = rieszKernel d s (x - y)
      rw [HRS.Whole.Q34.rieszKernel_eq (d := d) (s := s) hs.ne' (x - y)]
      simp
    calc
      ∫ x, (∫ y, rieszKernel d s (x - y) * g y ∂μ) ∂μ =
          ∫ x, HRS.Whole.Q34.Tk s μ g x * 1 ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        change (∫ y, rieszKernel d s (x - y) * g y ∂μ) =
          HRS.Whole.Q34.Tk s μ g x * 1
        calc
          _ = HRS.Whole.Q34.Tk s μ g x := (htkGen x).symm
          _ = HRS.Whole.Q34.Tk s μ g x * 1 := by ring
      _ = ∫ x, g x * HRS.Whole.Q34.Tk s μ (fun _ => (1 : ℝ)) x ∂μ := hsym
      _ = ∫ y, HRS.Whole.convMeasure (HRS.Whole.rieszKernel d s) μ y * g y ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        change g y * HRS.Whole.Q34.Tk s μ (fun _ => (1 : ℝ)) y = _
        rw [htkOne y]
        ring
  · have hs_eq : s = 0 := le_antisymm (le_of_not_gt hs) hs0
    subst s
    obtain ⟨L, hL⟩ := S47.s47_logmoment2 hT
    have hl2 : MemLp (HRS.MS.Thm.t67l : Euc d → ℝ) 2 μ := by
      dsimp [μ]
      exact S45.s45_l_memLp hT.prob hL
    have hM : ∀ x, ρ x ≤ C := S47.s47_le hT
    have hdpos : 0 < d := by exact_mod_cast hsd
    have hd1 : 1 ≤ d := by omega
    obtain ⟨Mg, hk⟩ := S45.s45_tcker hd1 hT.prob hM hl2
    exact fp81s21_initial_log_kernel_gen_symm hk hl2 hgmeas hg2 hmean

#print axioms fp81s21_initial_integral_kernel_gen_symm

end HRS.Fp81.S21

end
