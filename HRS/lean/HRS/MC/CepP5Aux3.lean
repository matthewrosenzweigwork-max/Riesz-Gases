import HRS.MC.CepP5Aux2

/-!
# Packet P5, Aux3: the weak forward equation for `ghat` on the covering space
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MC.CepP5

open HRS HRS.MC.CepP3 HRS.MC.CepP4

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d N : ℕ}

theorem Lop_eq_zero_off (c : ℝ) (b : ℝ × (Fin N → Euc d) → Fin N → Euc d)
    {F : ℝ × (Fin N → Euc d) → ℝ} {p : ℝ × (Fin N → Euc d)} (hp : p ∉ tsupport F) :
    HRS.MC.CepP3.Lop c b F p = 0 := by
  have h1 : fderiv ℝ F p = 0 := image_eq_zero_of_notMem_tsupport (fun h => hp (tsupport_fderiv_subset ℝ h))
  have h2 : fderiv ℝ (fderiv ℝ F) p = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hp (tsupport_fderiv_subset ℝ (tsupport_fderiv_subset ℝ h)))
  simp [HRS.MC.CepP3.Lop, h1, h2]

theorem weak_ghat [IsProbabilityMeasure P] (hN : 2 ≤ N) [NeZero N]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {D : DynData d} (hV : Torus.IsSmooth D.V) {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : SelectedFlow P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X)
    {f : ℝ → Config d N → ℝ}
    (hgm : Measurable (ghat f T))
    (hf0 : ∀ r ∈ Set.Ioo 0 T, ∀ x ∉ collisionSet d N, 0 ≤ f r x)
    (hρ : ∀ S : Set (ℝ × Config d N), MeasurableSet S → S ⊆ Set.Ioo 0 T ×ˢ (collisionSet d N)ᶜ →
        ∫⁻ t in Set.Ioo 0 T, selectedLaw P X t {x | (t, x) ∈ S} =
          ∫⁻ p in S, ENNReal.ofReal (f p.1 p.2) ∂((volume : Measure ℝ).prod (volume : Measure (Config d N))))
    {F : ℝ × (Fin N → Euc d) → ℝ} (hFs : ContDiff ℝ ∞ F) (hFc : HasCompactSupport F)
    (hFO : tsupport F ⊆ Ioo 0 T ×ˢ liftedFree d N) :
    ∫ p, ghat f T p * HRS.MC.CepP3.Lop D.invβ (bC D) F p = 0 := by
  classical
  have hm := measurable_joint hF.progressive
  have hC := selectedFlow_toContact hX
  have hXm : ∀ t : ℝ, Measurable (X (Real.toNNReal t)) := fun t => hC.adapted _
  have hcov := cov_fke hN hV hT hX hF hFs hFc hFO
  have hmeasO : MeasurableSet (Ioo 0 T ×ˢ liftedFree d N : Set (ℝ × (Fin N → Euc d))) :=
    (isOpen_Ioo.prod (isOpen_liftedFree d N)).measurableSet
  have hoff : ∀ p ∉ (Ioo 0 T ×ˢ liftedFree d N : Set (ℝ × (Fin N → Euc d))),
      HRS.MC.CepP3.Lop D.invβ (bC D) F p = 0 := fun p hp => Lop_eq_zero_off _ _ (fun h => hp (hFO h))
  have hres := rhoCov_restrict_O (P := P) hm hXm hgm hρ
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hoff] at hcov
  rw [hres, integral_withDensity_eq_integral_toReal_smul
    (show Measurable (fun p => ENNReal.ofReal (ghat f T p)) from ENNReal.measurable_ofReal.comp hgm)
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at hcov
  have h2 : ∫ p in Ioo 0 T ×ˢ liftedFree d N, (ENNReal.ofReal (ghat f T p)).toReal •
      HRS.MC.CepP3.Lop D.invβ (bC D) F p = ∫ p in Ioo 0 T ×ˢ liftedFree d N, ghat f T p *
      HRS.MC.CepP3.Lop D.invβ (bC D) F p := by
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [smul_eq_mul]
    rw [ENNReal.toReal_ofReal (ghat_nonneg hf0 p)]
  rw [h2] at hcov
  rw [← hcov]
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun p hp => by rw [hoff p hp, mul_zero])).symm

end HRS.MC.CepP5
