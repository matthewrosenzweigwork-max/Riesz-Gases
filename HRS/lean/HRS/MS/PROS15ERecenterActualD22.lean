import HRS.MS.PROS15ERecenterL2D22

/-!
# S15e: recentered Hilbert--Schmidt Wick series under the genuine Gaussian tilt

This proves an unconditional tilted-L² convergence theorem for the actual
Hilbert--Schmidt spectral coordinates. The variance recentering changes the
quadratic by a finite *trace correction* even when the eigenvalues are not
trace-class. The result does not identify the physical all-smooth-ONB
Wick source with the spectral quadratic, and is not frozen S15e closure.
-/
set_option autoImplicit false
noncomputable section
open HRS MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.MS.R26T3
open HRS.MC.E213U13

theorem s15e_hs_recentered_tilted_L2
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → ℝ) (hξ : HRS.IsStdGaussianSeq P ξ)
    (lam : ℕ → ℝ) (hlam : ∀ j, 0 ≤ lam j)
    (hlam2 : Summable (fun j => lam j ^ 2))
    (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ Q : Ω → ℝ,
      HRS.TendstoL2 P (s21h2_s15c_Qn ξ lam) Q ∧
      Integrable (fun ω => Real.exp (-γ * Q ω)) P ∧
      Integrable (fun ω => Real.exp (-(2 * γ) * Q ω)) P ∧
      Tendsto (fun n => ∫ ω,
        (((1 / 2 : ℝ) * ∑ j ∈ Finset.range n,
          lam j * (ξ j ω ^ 2 - (1 + γ * lam j)⁻¹)) -
          (Q ω - (1 / 2 : ℝ) * ∑' j,
            lam j * ((1 + γ * lam j)⁻¹ - 1))) ^ 2
          ∂(r26t3_tilt P (fun ω => γ * Q ω)))
        atTop (𝓝 0) := by
  obtain ⟨Q, hT, hQ2, hE1, hE2, hconv⟩ :=
    s15e_hs_spectral_tilted_sections_L2 P ξ hξ lam hlam hlam2 γ hγ
  let Pt := r26t3_tilt P (fun ω => γ * Q ω)
  have hV : AEMeasurable (fun ω => γ * Q ω) P :=
    hT.1.aemeasurable.const_mul γ
  have hE1' : Integrable (fun ω => Real.exp (-(γ * Q ω))) P := by
    simpa only [neg_mul] using hE1
  have hE2' : Integrable (fun ω => Real.exp (-(2 * (γ * Q ω)))) P := by
    convert hE2 using 1
    funext ω
    congr 1
    ring
  letI : IsProbabilityMeasure Pt := r26t3_tilt_isProb P hV hE1'
  have hSections : ∀ n, InQ2 hξ (s21h2_s15c_Qn ξ lam n) :=
    s15e_diagonal_sections_second_chaos ξ hξ lam
  have hFm : ∀ n, MemLp (s21h2_s15c_Qn ξ lam n) 2 Pt := by
    intro n
    exact s15e_inQ2_tilt_memLp_two P hV hE2' (hSections n)
  have hGm : MemLp Q 2 Pt :=
    s15e_inQ2_tilt_memLp_two P hV hE2' hQ2
  have hs : Summable (fun j => lam j * ((1 + γ * lam j)⁻¹ - 1)) :=
    s15e_recenter_scalar_summable lam hlam hlam2 γ hγ
  have hc : Tendsto
      (fun n => (1 / 2 : ℝ) * ∑ j ∈ Finset.range n,
        lam j * ((1 + γ * lam j)⁻¹ - 1)) atTop
      (𝓝 ((1 / 2 : ℝ) * ∑' j, lam j * ((1 + γ * lam j)⁻¹ - 1))) :=
    (hs.hasSum.tendsto_sum_nat).const_mul (1 / 2 : ℝ)
  have hrec := s15e_recenter_L2_convergence Pt
    (s21h2_s15c_Qn ξ lam) Q hFm hGm
    (fun n => (1 / 2 : ℝ) * ∑ j ∈ Finset.range n,
      lam j * ((1 + γ * lam j)⁻¹ - 1))
    ((1 / 2 : ℝ) * ∑' j, lam j * ((1 + γ * lam j)⁻¹ - 1))
    (by simpa only [Pt] using hconv) hc
  refine ⟨Q, hT, hE1, hE2, ?_⟩
  have hfin : ∀ n ω,
      ((1 / 2 : ℝ) * ∑ j ∈ Finset.range n,
        lam j * (ξ j ω ^ 2 - (1 + γ * lam j)⁻¹)) =
      s21h2_s15c_Qn ξ lam n ω -
        (1 / 2 : ℝ) * ∑ j ∈ Finset.range n,
          lam j * ((1 + γ * lam j)⁻¹ - 1) := by
    intro n ω
    have h := s15e_finite_wick_recentering lam (fun j => ξ j ω) γ n
    dsimp only [s21h2_s15c_Qn]
    linarith
  convert hrec using 1
  funext n
  apply integral_congr_ae
  exact ae_of_all _ (fun ω => by
    exact congrArg
      (fun y : ℝ => (y - (Q ω - (1 / 2 : ℝ) * ∑' j,
        lam j * ((1 + γ * lam j)⁻¹ - 1))) ^ 2) (hfin n ω))

#print axioms s15e_hs_recentered_tilted_L2
end HRS.MS.R26T3
