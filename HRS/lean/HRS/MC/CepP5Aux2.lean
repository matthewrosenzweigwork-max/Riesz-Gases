import HRS.MC.CepP5Aux1

/-!
# Packet P5, Aux2: the lifted space-time measure restricted to `O` has density `ghat`
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MC.CepP5

open HRS HRS.MC.CepP3 HRS.MC.CepP4

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d N : ℕ}

theorem rhoCov_restrict_O [IsProbabilityMeasure P] {T : ℝ} {X : ℝ≥0 → Ω → Config d N}
    (hm : Measurable (fun q : ℝ × Ω => X (Real.toNNReal q.1) q.2))
    (hXm : ∀ t : ℝ, Measurable (X (Real.toNNReal t)))
    {f : ℝ → Config d N → ℝ}
    (hgm : Measurable (ghat f T))
    (hρ : ∀ S : Set (ℝ × Config d N), MeasurableSet S → S ⊆ Set.Ioo 0 T ×ˢ (collisionSet d N)ᶜ →
        ∫⁻ t in Set.Ioo 0 T, selectedLaw P X t {x | (t, x) ∈ S} =
          ∫⁻ p in S, ENNReal.ofReal (f p.1 p.2) ∂((volume : Measure ℝ).prod (volume : Measure (Config d N)))) :
    (rhoCov (rhoM P T X)).restrict (Ioo 0 T ×ˢ liftedFree d N) =
      (volume.restrict (Ioo 0 T ×ˢ liftedFree d N)).withDensity (fun p => ENNReal.ofReal (ghat f T p)) := by
  classical
  haveI := isAddHaar_volume_cov (d := d) (N := N)
  set O : Set (ℝ × (Fin N → Euc d)) := Ioo 0 T ×ˢ liftedFree d N with hOdef
  have hO : IsOpen O := isOpen_Ioo.prod (isOpen_liftedFree d N)
  set rc := rhoCov (rhoM P T X) with hrc
  have hshift : ∀ (w : Fin N → Lattice d) (A : Set (ℝ × (Fin N → Euc d))), MeasurableSet A → A ⊆ O →
      A ⊆ Ztile d N w → rc A = ∫⁻ p in A, ENNReal.ofReal (ghat f T p) := by
    intro w A hA hAO hAZ
    set a : ℝ × (Fin N → Euc d) := (0, lat w) with ha
    set A' : Set (ℝ × (Fin N → Euc d)) := (fun p => p + a) ⁻¹' A with hA'
    have hA'm : MeasurableSet A' := (measurable_add_const a) hA
    have hA'O : A' ⊆ O := fun p hp => (mem_O_add_lat T p w).1 (hAO hp)
    have hA'c : A' ⊆ cubeSet d N := by
      intro p hp
      refine ⟨mem_univ _, ?_⟩
      have h1 : flo (p.2 + lat w) = w := hAZ hp
      rw [flo_add_lat] at h1
      have h0 : flo p.2 = 0 := by simpa using h1
      have := flo_eq_iff.1 h0
      simpa [lat_zero] using this
    have h1 : rc A = rc A' := by
      have := map_tau_rhoCov (rhoM P T X) w
      have e : tau w ⁻¹' A = A' := by ext p; simp [tau_eq, hA', ha]
      rw [← e, ← Measure.map_apply (measurable_tau w) hA, this]
    have h2 : ∫⁻ p in A', ENNReal.ofReal (ghat f T p) = ∫⁻ p in A, ENNReal.ofReal (ghat f T p) := by
      have := (measurePreserving_add_right volume a).setLIntegral_comp_preimage_emb
        (measurableEmbedding_addRight a) (fun y => ENNReal.ofReal (ghat f T y)) A
      rw [← this]
      refine lintegral_congr fun x => ?_
      rw [ha, ghat_add_lat]
    rw [h1, ← h2]
    exact rhoCov_base hm hXm hgm hρ hA'm hA'c hA'O
  have hall : ∀ B : Set (ℝ × (Fin N → Euc d)), MeasurableSet B → B ⊆ O →
      rc B = ∫⁻ p in B, ENNReal.ofReal (ghat f T p) := by
    intro B hB hBO
    have hU : B = ⋃ w, B ∩ Ztile d N w := by
      ext p
      simp only [mem_iUnion, mem_inter_iff]
      exact ⟨fun hp => ⟨flo p.2, hp, rfl⟩, fun ⟨_, hp, _⟩ => hp⟩
    have hmeas : ∀ w, MeasurableSet (B ∩ Ztile d N w) := fun w => hB.inter (measurableSet_Ztile w)
    have hdisj : Pairwise (Function.onFun Disjoint fun w => B ∩ Ztile d N w) := by
      intro w w' hww'
      refine Set.disjoint_left.2 fun p hp hp' => hww' ?_
      exact hp.2.symm.trans hp'.2
    rw [hU, measure_iUnion hdisj hmeas, lintegral_iUnion hmeas hdisj]
    refine tsum_congr fun w => ?_
    exact hshift w _ (hmeas w) (inter_subset_left.trans hBO) inter_subset_right
  refine Measure.ext fun B hB => ?_
  rw [Measure.restrict_apply hB, withDensity_apply _ hB, Measure.restrict_restrict hB]
  exact hall (B ∩ O) (hB.inter hO.measurableSet) inter_subset_right

end HRS.MC.CepP5
