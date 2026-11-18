import HRS.MS.R2InterpAux127
import HRS.MS.R2InterpAux96
import HRS.MS.R2InterpAux87

/-!
# S10.2 (worker S10S), part 128 (packet M3c): almost sure continuity of `τ ↦ ζ_N^τ(U^{τ,t}φ_α)` on `[0,t]`

From the orbit identity of Aux87: a constant, a continuous Itô integral and the primitive of a locally integrable drift.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

set_option maxHeartbeats 1600000 in
theorem s102_orbit_cont (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β : ℝ} (ha : 0 < a)
    (hβ : 0 < β) {ρ : Euc d → ℝ} (hρ : IsThermalEquilibrium d s a β ρ) {T : ℝ} (hT : 0 ≤ T) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (X₀ : Ω → EucConfig d N)
    (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hX : IsWholeStrongSolution P (quadraticGradientDyn d s a β) T X₀ W X) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsWholeFilteredSolution P ℱ W' W X) {M L p K : ℝ}
    (hp : 1 < p) (hρR : IsRound2Density d s M L ρ)
    (hdens : ∀ r ∈ Icc (0 : ℝ) T, HasR2ActualDensity s β p K (HRS.Whole.withDensityReal ρ) (P.map (X r.toNNReal)))
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (m : ℝ) (α : MultiIndex d)
    (hcls : ∃ f, IsClassicalAdjointW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) t (oscTestFun m α) f) :
    ∀ᵐ ζ ∂P, ContinuousOn
      (fun τ => s102_zf P X ζ τ (propagatorW ((quadraticGradientDyn d s a β).coeff (fun _ => ρ)) τ t (oscTestFun m α)))
      (Icc 0 t) := by
  classical
  set D := quadraticGradientDyn d s a β with hD
  set C := D.coeff (fun _ => ρ) with hC
  set μ := HRS.Whole.withDensityReal ρ with hμ
  have hμp : IsProbabilityMeasure μ := HRS.MS.R2Mt.s92_isProb_mu hρR.prob
  set f : ℝ → Euc d → ℝ := fun r => propagatorW C r t (oscTestFun m α) with hfdef
  have hf : IsClassicalAdjointW C t (oscTestFun m α) f := s102_propagator_classical hcls
  have hdual := s102_orbit_zeta hd hs0 hs ha hβ hρ hT hN P X₀ W X hX ℱ W' hF hp hρR hdens ht m α hcls
  obtain ⟨hK, B, hKm, hKr, hKb⟩ := s102_kernel_pkg hs0 hf
  have hXm : Measurable fun q : ℝ × Ω => X (min q.1 t).toNNReal q.2 :=
    measurable_progressive_min_gen (u := ofNNRealTime X) hF.progressive t
  have hdens' : ∀ r ∈ Icc (0 : ℝ) t, HasR2ActualDensity s β p K μ (P.map (X r.toNNReal)) :=
    fun r hr => hdens r ⟨hr.1, hr.2.trans ht.2⟩
  obtain ⟨-, hI2⟩ := s102_quad_prodInt hd hs0 hs M L β p K B hβ hp hρR hN P X t hXm hdens' hK hKm hKb
  obtain ⟨Bg, hBg⟩ := s102_Ig_bdd hf X
  have hΦ : IsProgressiveL2 P ℱ (s102_Ig f t X) :=
    IsProgressiveL2.of_bounded P (s102_Ig_progressive hf hF.progressive) Bg hBg
  have hIc := (isItoIntegral_itoIntegral hF.brownian hΦ).cont
  filter_upwards [hdual, hI2.prod_left_ae] with ζ h hint
  have hG : IntegrableOn (fun r => -(Real.sqrt N)⁻¹ * r2QuadField s μ P X r ζ (f r)) (Icc 0 t) := by
    refine IntegrableOn.congr_fun (hint.const_mul (-(Real.sqrt N)⁻¹)) (fun r hr => ?_) measurableSet_Icc
    simp only [r2QuadFluct, r2QuadField, hKr r hr]
    rfl
  have hprim : ContinuousOn (fun τ => ∫ r in Icc (0 : ℝ) τ, (-(Real.sqrt N)⁻¹ * r2QuadField s μ P X r ζ (f r)))
      (Icc 0 t) := by
    have h1 := intervalIntegral.continuousOn_primitive_interval (a := 0) (b := t) (μ := volume)
      (f := fun r => -(Real.sqrt N)⁻¹ * r2QuadField s μ P X r ζ (f r)) (by rwa [uIcc_of_le ht.1])
    rw [uIcc_of_le ht.1] at h1
    refine h1.congr fun τ hτ => ?_
    beta_reduce
    rw [intervalIntegral.integral_of_le hτ.1, integral_Icc_eq_integral_Ioc]
  have hR : ContinuousOn (fun τ => s102_zf P X ζ 0 (f 0) +
      (Real.sqrt N * (Real.sqrt (2 * β⁻¹) / N)) * itoIntegral P ℱ W' (s102_Ig f t X) τ ζ +
      ∫ r in Icc (0 : ℝ) τ, (-(Real.sqrt N)⁻¹ * r2QuadField s μ P X r ζ (f r))) (Icc 0 t) :=
    (continuousOn_const.add (continuousOn_const.mul (hIc ζ).continuousOn)).add hprim
  exact hR.congr fun τ hτ => h τ hτ

end HRS.MS.R2Interp

end
