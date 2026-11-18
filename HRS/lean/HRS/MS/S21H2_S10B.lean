import HRS.MS.S21H2_S10A
import HRS.MS.S21F_C09
import HRS.MS.S111X2Aux44

/-!
# S21H2, packet R26-T3.S10 (part B): the actual initial susceptibility form is a coercive symmetric form on `L²(μ₀)`

`susceptibilityCov _ μ₀ γ f g = ⟪[P f], Res_γ [P g]⟫` (`s111x2_susc_eq`) with `Res_γ = (I + γK)⁻¹` a bounded symmetric operator on `L²(μ₀)`
with `⟪x, Res x⟫ ≥ ‖x‖²/(1+γ M)` (`s111x2_Res_bounds`, `KRep` at the actual reference as in `r26t3_initial_cov_bound`).  Packaged as an `S21H2Form`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set InformationTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.MS.R26T3
open HRS HRS.Whole HRS.MS.S111X2

theorem s21h2_mu_prob {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (R : Trajectory p δ) :
    IsProbabilityMeasure (r26t3_mu R 0) := by
  obtain ⟨-, -, -, href⟩ := r26t3_reference_data p δ hδ hδh R
  obtain ⟨M, c, S, hc, hTc⟩ := href 0
  exact HRS.Whole.Q34.isProbabilityMeasure_nu hTc.prob

theorem s21h2_form_of_init {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) [IsProbabilityMeasure (r26t3_mu R 0)] :
    ∃ F : S21H2Form (Lp ℝ 2 (r26t3_mu R 0)), ∀ (f g : Euc p.d → ℝ) (hf : MemLp f 2 (r26t3_mu R 0))
      (hg : MemLp g 2 (r26t3_mu R 0)),
      HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ f g =
        inner ℝ (s111x2_cl hf) (F.A (s111x2_cl hg)) := by
  obtain ⟨-, -, -, href⟩ := r26t3_reference_data p δ hδ hδh R
  obtain ⟨M, c, S, hc, hTc⟩ := href 0
  have hd := p.hd
  have hsd : p.s < (p.d : ℝ) := by
    have := p.hs
    have : (0 : ℝ) < p.d := by exact_mod_cast (by omega : 0 < p.d)
    linarith
  have hP : IsProbabilityMeasure (HRS.Whole.withDensityReal (R.ρ 0)) := ‹IsProbabilityMeasure (r26t3_mu R 0)›
  obtain ⟨Mg, K, hK⟩ := HRS.MS.S111X2.s111x2_krep_of_tcref (by omega) p.hs0 hsd hc hTc
  have hK' : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg := hK
  have hθ := p.hγ
  set Rs := s111x2_Res hK'.posOp hθ with hRs
  let A : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0) :=
    LinearMap.mkContinuous
      { toFun := Rs
        map_add' := s111x2_Res_add hK'.posOp hθ
        map_smul' := fun c f => by simpa using s111x2_Res_smul hK'.posOp hθ c f } 1
      (fun f => by simpa using (s111x2_Res_bounds hK'.posOp hθ f).2.2)
  have hA : ∀ x, A x = Rs x := fun x => rfl
  have hMg := hK'.nonneg
  have hpos : 0 < (1 + p.γ * Mg)⁻¹ := by positivity
  refine ⟨⟨A, fun x y => by rw [hA, hA]; exact s111x2_Res_symm hK'.posOp hθ x y, (1 + p.γ * Mg)⁻¹,
    hpos, fun x => ?_⟩, fun f g hf hg => ?_⟩
  · rw [hA]
    have := (s111x2_Res_bounds hK'.posOp hθ x).1
    rwa [div_eq_inv_mul] at this
  · rw [s111x2_susc_eq hK' hθ hf hg, hA]

end HRS.MS.R26T3
