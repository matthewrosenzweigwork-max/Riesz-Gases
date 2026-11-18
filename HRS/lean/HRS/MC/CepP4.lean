import HRS.MC.CepP4Aux6

/-!
# Packet P4: every time slice has the smooth density
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MC.CepP4

open HRS HRS.MC.CepP3

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d N : ℕ}

theorem cep_P4_time_slices_proof [IsProbabilityMeasure P] (hN : 2 ≤ N) [NeZero N]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {D : DynData d} (hV : Torus.IsSmooth D.V) {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : SelectedFlow P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X)
    {f : ℝ → Config d N → ℝ}
    (hfs : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × (Fin N → Euc d) => f p.1 (fun i => Torus.mk (p.2 i)))
        (Set.Ioo 0 T ×ˢ {Y : Fin N → Euc d | (fun i => Torus.mk (Y i)) ∉ collisionSet d N}))
    (hf0 : ∀ r ∈ Set.Ioo 0 T, ∀ x ∉ collisionSet d N, 0 ≤ f r x)
    (hρ : ∀ S : Set (ℝ × Config d N), MeasurableSet S → S ⊆ Set.Ioo 0 T ×ˢ (collisionSet d N)ᶜ →
        ∫⁻ t in Set.Ioo 0 T, selectedLaw P X t {x | (t, x) ∈ S} =
          ∫⁻ p in S, ENNReal.ofReal (f p.1 p.2) ∂((volume : Measure ℝ).prod (volume : Measure (Config d N)))) :
    ∀ t ∈ Set.Ioo 0 T, (selectedLaw P X t).restrict (collisionSet d N)ᶜ =
      ((volume : Measure (Config d N)).restrict (collisionSet d N)ᶜ).withDensity
        (fun x => ENNReal.ofReal (f t x)) := by
  classical
  intro t ht
  have hCm : MeasurableSet (collisionSet d N)ᶜ := (isClosed_collisionSet d N).measurableSet.compl
  have hm := measurable_joint hF.progressive
  have hC := selectedFlow_toContact hX
  have hXm : ∀ t : ℝ, Measurable (X (Real.toNNReal t)) := fun t => hC.adapted _
  haveI := isProb_selectedLaw (P := P) hXm
  have hgc : ContinuousOn (fun p : ℝ × (Fin N → Euc d) => f p.1 (mkC p.2))
      (Ioo 0 T ×ˢ liftedFree d N) := hfs.continuousOn
  have hgm : Measurable (ghat f T) := measurable_ghat hfs
  have hstar : ∀ {G : ℝ × Config d N → ℝ≥0∞}, Measurable G →
      ∫⁻ t in Ioo 0 T, ∫⁻ x in (collisionSet d N)ᶜ, G (t, x) ∂(selectedLaw P X t)
      = ∫⁻ t in Ioo 0 T, ∫⁻ x in (collisionSet d N)ᶜ, ENNReal.ofReal (fhat f T (t, x)) * G (t, x) :=
    fun hG => star_identity hm hXm hfs hρ hG
  have hcongr : ((volume : Measure (Config d N)).restrict (collisionSet d N)ᶜ).withDensity
        (fun x => ENNReal.ofReal (f t x)) =
      ((volume : Measure (Config d N)).restrict (collisionSet d N)ᶜ).withDensity
        (fun x => ENNReal.ofReal (fhat f T (t, x))) := by
    refine withDensity_congr_ae ?_
    filter_upwards [ae_restrict_mem hCm] with x hx
    rw [fhat_eq ht hx]
  rw [hcongr]
  refine ext_of_good hN _ _ ?_ ?_
  · refine withDensity_absolutelyContinuous _ _ ?_
    rw [Measure.restrict_apply (isClosed_collisionSet d N).measurableSet, Set.inter_compl_self]
    exact measure_empty
  · intro ψ δ hψ
    rw [slice_good hX hm hXm hgc hgm hf0 hstar hψ ht,
      lintegral_withDensity_eq_lintegral_mul _
        (show Measurable (fun x : Config d N => ENNReal.ofReal (fhat f T (t, x))) from
          ENNReal.measurable_ofReal.comp (hgm.comp (measurable_const.prodMk measurable_repC)))
        (show Measurable (fun x : Config d N => ENNReal.ofReal (ψ x)) from
          ENNReal.measurable_ofReal.comp hψ.1.measurable)]
    rfl

end HRS.MC.CepP4
