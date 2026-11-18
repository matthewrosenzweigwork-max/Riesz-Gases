import HRS.MC.CepP3Aux9

/-!
# Packet P3, Aux10: the covering-form equation `∫ L F dρ̃ = 0`
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MC.CepP3

open HRS

variable {d N : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem isCk_two_of_isSmooth {V : Torus d → ℝ} (hV : Torus.IsSmooth V) : Torus.IsCk 2 V :=
  (show ContDiff ℝ ∞ (Torus.lift V) from hV).of_le two_le_infty

theorem cov_fke [IsProbabilityMeasure P] (hN : 2 ≤ N) [NeZero N]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {D : DynData d} (hV : Torus.IsSmooth D.V) {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : SelectedFlow P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X)
    {F : ℝ × (Fin N → Euc d) → ℝ} (hFs : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F)
    (hFO : tsupport F ⊆ Ioo 0 T ×ˢ liftedFree d N) :
    ∫ p, Lop D.invβ (bC D) F p ∂(rhoCov (rhoM P T X)) = 0 := by
  obtain ⟨R, hR⟩ := exists_supp hFc
  have hC := selectedFlow_toContact hX
  have hperF : ∀ (w : Fin N → Lattice d) p, per F (tau w p) = per F p := fun w p => per_tau F w p
  have hcd : ContDiff ℝ ∞ (per F) := contDiff_per hFs hR
  have hΦ := isFKETest_PhiOf hT hFs hFc hFO
  have hfke := selected_law_fke_FKE hN (isCk_two_of_isSmooth hV) hT hX hF (PhiOf (per F)) hΦ
  have h0 : ∫ x, PhiOf (per F) 0 x ∂(selectedLaw P X 0) = 0 := by
    simp [PhiOf_time_zero hFO]
  rw [h0, neg_zero] at hfke
  have hm := measurable_joint hF.progressive
  have hXm : ∀ t : ℝ, Measurable (X (Real.toNNReal t)) := fun t => hC.adapted _
  haveI := isFiniteMeasure_rhoM (P := P) T X hm
  have hLc : Continuous (Lop D.invβ (bC D) F) := continuous_Lop D hV hFs hFO
  have hLs : Supp R (Lop D.invβ (bC D) F) := supp_Lop _ _ hR
  -- the integrand
  have hpt : ∀ r ∈ Ioo (0 : ℝ) T, ∀ x : Config d N,
      fkeGenerator D T (PhiOf (per F)) r x + fkeInteraction D (PhiOf (per F)) r x
        = per (Lop D.invβ (bC D) F) (psi 0 (r, x)) := by
    intro r hr x
    rw [fkeGI_eq_fkeIto D D.hsd, fkeIto_eq_Lop D (hcd.of_le two_le_infty) hperF hr,
      Lop_per _ (bC_tau D) hFs hR]
    simp [psi, lat_zero]
  obtain ⟨C, hCb⟩ := bounded_per_psi hLc hLs
  have hint : ∫ q, per (Lop D.invβ (bC D) F) (psi 0 q) ∂(rhoM P T X)
      = ∫ t in Ioo 0 T, ∫ x, per (Lop D.invβ (bC D) F) (psi 0 (t, x)) ∂(selectedLaw P X t) :=
    integral_rhoM T hm hXm (measurable_per_psi hLc hLs) hCb
  rw [integral_rhoCov _ hLc hLs, hint]
  rw [intervalIntegral.integral_of_le hT.le, integral_Ioc_eq_integral_Ioo] at hfke
  refine Eq.trans ?_ hfke.symm
  refine setIntegral_congr_fun (measurableSet_Ioo (a := (0 : ℝ)) (b := T)) fun r hr => ?_
  exact integral_congr_ae (Eventually.of_forall fun x => (hpt r hr x).symm)

end HRS.MC.CepP3
