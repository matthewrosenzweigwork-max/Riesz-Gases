import HRS.MS.S113EndAux23
import HRS.MS.S113EndAux11

/-!
# S11.3 endpoint (worker S11X), part 24: positivity of the normalizers and `SbLogK` for the members of the class
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113BD

open HRS HRS.Whole

variable {d : ℕ}

theorem s113x_K_pos (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {q β : ℝ} (hβ : 0 < β) (hq : 0 < q)
    {ρ₀ : Euc d → ℝ} (hρ₀ : IsThermalEquilibrium d s q β ρ₀) {j m : ℕ} {εstar r c₀ c C₁ : ℝ} (hC₁ : 0 < C₁)
    (hc₀ : 0 < c₀) (hNL : MovNonlinearConclusion d s q β ρ₀ j m εstar r c₀ c C₁) {f0 : Euc d → ℝ}
    (hf0 : MovInitialClass ρ₀ j m εstar f0) {ρ : ℝ → Euc d → ℝ} (hρ : MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ)
    {N : ℕ} (hN : 2 ≤ N) {t : ℝ} (ht : 0 ≤ t) :
    0 < HRS.Whole.gibbsNormalizer (rieszKernel d s) N β (HRS.Whole.withDensityReal (ρ t)) := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  obtain ⟨M, L, E, c₁, hM1, hc₁, hE, hfam⟩ :=
    HRS.MS.MovEnt.s66_fam_exists hd hs0 hsd hq hβ hρ₀ hC₁ hc₀.le hNL
  have hfm := hfam f0 hf0 ρ hρ
  obtain ⟨C, -, hC⟩ := HRS.MS.R2Mt.s92_normalizer_bounds hd hs0 hs M L β (2 * β) hβ (by linarith)
  exact (hC (ρ t) ⟨hfm.prob t ht, hfm.bound t ht, hfm.logm t ht⟩ N hN β ⟨le_rfl, by linarith⟩).1.normalizer_pos

theorem s113x_SbLogK_class (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {q β : ℝ} (hβ : 0 < β)
    (hq : 0 < q) {ρ₀ : Euc d → ℝ} (hρ₀ : IsThermalEquilibrium d s q β ρ₀) {j m : ℕ}
    {εstar r c₀ c C₁ : ℝ} (hj : 1 ≤ j) (hm : (d : ℝ) / 2 + j + 6 < m) (hC₁ : 0 < C₁) (hε : 0 < εstar) (hc : 0 < c)
    (hc₀ : 0 < c₀) (hNL : MovNonlinearConclusion d s q β ρ₀ j m εstar r c₀ c C₁) {f0 : Euc d → ℝ}
    (hf0 : MovInitialClass ρ₀ j m εstar f0) {ρ : ℝ → Euc d → ℝ} (hρ : MovInSmallClass d s q β ρ₀ m r c₀ f0 ρ)
    (hF : S113XFacts d s q β ρ) {N : ℕ} (hN : 2 ≤ N) {T : ℝ} (hT : 0 ≤ T) :
    MfeConf.SbLogK (quadraticGradientDyn d s q β) N T ρ := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  obtain ⟨cg, Kg, M, hcg, hKg, hM, hG, hSl, -⟩ := hF
  have hprops := HRS.MS.MovEnt.s66_class_props hNL hf0 hρ hc₀.le
  have hmeas := s113x_meas hd hs0 hs hβ hq hρ₀ hj hm hC₁ hε hc₀ hNL f0 hf0 ρ hρ
  obtain ⟨hfin, hLi⟩ := s113x_L_props hj hNL hC₁ hε hc hc₀ hf0 hρ hmeas
  obtain ⟨C, Bp, C3, htr3⟩ := s113x_tr3_of_gauss (by omega : 1 ≤ d) hs0 hsd q β hcg hKg (hρ.solution T)
    (fun t ht y => (hprops t ht.1).2.1 y) (fun t ht => (hG t ht.1).1) (fun t ht => (hG t ht.1).2)
  have hKi : IntegrableOn (r2MovL d s q β ρ) (Set.Icc 0 T) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact (show IntegrableOn (r2MovL d s q β ρ) (Set.Ioi 0) volume from hLi).mono_set Set.Ioc_subset_Ioi_self
  refine MfeConf.sb1_logK_main htr3 hT (by show 0 < β⁻¹; exact inv_pos.2 hβ) (by omega) (r2MovL d s q β ρ) hKi ?_
  intro t ht
  rw [s113x_mfeTransport_eq]
  have hdiff : Differentiable ℝ (movU d s q β (ρ t)) := s113x_movU_diff hj hNL hc₀ hf0 hρ ht.1
  have hLt0 : 0 ≤ r2MovL d s q β ρ t := by unfold r2MovL; exact ENNReal.toReal_nonneg
  have hb : ∀ x, ‖fderiv ℝ (movU d s q β (ρ t)) x‖ ≤ r2MovL d s q β ρ t := fun x => by
    have : ENNReal.ofReal ‖fderiv ℝ (movU d s q β (ρ t)) x‖ ≤
        ⨆ x : Euc d, ENNReal.ofReal ‖fderiv ℝ (movU d s q β (ρ t)) x‖ :=
      le_iSup (fun x : Euc d => ENNReal.ofReal ‖fderiv ℝ (movU d s q β (ρ t)) x‖) x
    exact (ENNReal.ofReal_le_iff_le_toReal (hfin t ht.1).ne).1 this
  refine ⟨(r2MovL d s q β ρ t).toNNReal, ?_, by simp [Real.coe_toNNReal _ hLt0]⟩
  refine lipschitzWith_of_nnnorm_fderiv_le hdiff fun x => ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ hLt0]
  exact hb x

end HRS.MS.S113BD

end
