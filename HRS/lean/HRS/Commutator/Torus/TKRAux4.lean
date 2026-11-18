import HRS.Commutator.Torus.TKRAux3

/-!
# T-KR helpers, part 4: `∇g_{≤}` is a trigonometric polynomial; Fourier coefficients of `∇g_{>}`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS HRS.KernelGrad

variable {d : ℕ} {s η : ℝ}

lemma tkr_G_integrable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd1 : s + 1 < d) :
    Integrable (periodicRieszGrad d s : Torus d → Euc d) := by
  obtain ⟨C, hG⟩ := goodKernel_periodicRieszGrad hd hs0 (by linarith : s < d)
  exact hG.integrable_G hsd1

lemma tkr_Gi_integrable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd1 : s + 1 < d) (i : Fin d) :
    Integrable (fun y : Torus d => periodicRieszGrad d s y i) :=
  (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).integrable_comp (tkr_G_integrable hd hs0 hsd1)

lemma tkr_Gi_measurable (hd : 2 ≤ d) (hs : s < d) (i : Fin d) :
    Measurable (fun y : Torus d => periodicRieszGrad d s y i) :=
  (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).measurable.comp (measurable_periodicRieszGrad hs)

lemma tkr_glo (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd1 : s + 1 < d) (hη : 0 < η) (x : Torus d) (i : Fin d) :
    ((PleqT η (periodicRieszGrad d s) x i : ℝ) : ℂ) =
      HRS.PDE.Kern.trig (fun k : Lattice d => ((tkrChi η k : ℝ) : ℂ) * tkrCI d s i k) x := by
  have hL : 0 < η⁻¹ := inv_pos.2 hη
  set Ψ : Torus d → ℝ := perio (Whole.psiL η⁻¹ : Euc d → ℝ) with hΨ
  have hΨc : Continuous Ψ := tkr_perio_psi_continuous hL
  obtain ⟨B, hB⟩ := isCompact_univ.exists_bound_of_continuousOn hΨc.continuousOn
  have hGi := tkr_Gi_integrable hd hs0 hsd1 i
  have hGint := tkr_G_integrable hd hs0 hsd1
  have hGm : Measurable (periodicRieszGrad d s : Torus d → Euc d) := measurable_periodicRieszGrad (by linarith)
  -- integrability of the vector integrand
  have hint : Integrable (fun y : Torus d => Ψ (x - y) • periodicRieszGrad d s y) := by
    refine (hGint.norm.const_mul B).mono' ?_ (Eventually.of_forall fun y => ?_)
    · exact ((hΨc.measurable.comp (measurable_const.sub measurable_id)).smul hGm).aestronglyMeasurable
    · rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (by simpa using hB (x - y) (Set.mem_univ _)) (norm_nonneg _)
  have hcomp : PleqT η (periodicRieszGrad d s) x i = ∫ y, Ψ (x - y) * periodicRieszGrad d s y i := by
    unfold PleqT
    have := (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).integral_comp_comm hint
    simpa using this.symm
  rw [hcomp, ← integral_complex_ofReal]
  have hT : HRS.PDE.IsTrigPoly ⌈2 / η⌉₊ (fun k : Lattice d => ((tkrChi η k : ℝ) : ℂ)) :=
    tkr_isTrigPoly hη (fun k hk => by simpa using hk)
  have hT2 : HRS.PDE.IsTrigPoly ⌈2 / η⌉₊ (fun k : Lattice d => ((tkrChi η k : ℝ) : ℂ) * tkrCI d s i k) :=
    tkr_isTrigPoly hη (fun k hk => by
      intro h0; apply hk; simp [h0])
  rw [HRS.PDE.Kern.trig_eq_sum hT2]
  have hpt : ∀ y : Torus d, (((Ψ (x - y) * periodicRieszGrad d s y i : ℝ)) : ℂ) =
      ∑ k ∈ HRS.PDE.Kern.boxF d ⌈2 / η⌉₊, ((tkrChi η k : ℝ) : ℂ) * Torus.mode k x *
        (Torus.mode (-k) y * ((periodicRieszGrad d s y i : ℝ) : ℂ)) := by
    intro y
    have := tkr_perio_psi_eq hη (x - y)
    rw [HRS.PDE.Kern.trig_eq_sum hT] at this
    push_cast
    rw [this, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [tkr_mode_sub]; ring
  simp_rw [hpt]
  have hint2 : ∀ k : Lattice d, Integrable fun y : Torus d => Torus.mode (-k) y *
      ((periodicRieszGrad d s y i : ℝ) : ℂ) := by
    intro k
    have h1 : Integrable (fun y : Torus d => ((periodicRieszGrad d s y i : ℝ) : ℂ)) := hGi.ofReal
    refine h1.bdd_mul (c := 1) ?_ ?_
    · exact (Torus.continuous_mode _).aestronglyMeasurable
    · exact Eventually.of_forall fun y => by rw [Torus.norm_mode]
  rw [integral_finsetSum _ (fun k _ => (hint2 k).const_mul _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_const_mul, tkr_fcoef_G hd hs0 hsd1 k i]
  unfold tkrCI
  ring

end HRS.Commutator.TorusNote
