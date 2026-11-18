import HRS.MC.CepP3Aux16

/-!
# Packet P3: smooth space-time density on `(0,T) × Ω_N`
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MC.CepP3

open HRS

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {d N : ℕ}

theorem mem_O_add_lat (T : ℝ) (p : ℝ × (Fin N → Euc d)) (w : Fin N → Lattice d) :
    p + (0, lat w) ∈ Ioo 0 T ×ˢ liftedFree d N ↔ p ∈ Ioo 0 T ×ˢ liftedFree d N := by
  simp only [mem_prod, Prod.fst_add, Prod.snd_add, add_zero, liftedFree, mem_setOf_eq]
  have : (fun i => Torus.mk ((p.2 + lat w) i)) = mkC p.2 := mkC_add_lat p.2 w
  rw [this]
  rfl

theorem cep_P3_spacetime_density_proof [IsProbabilityMeasure P] (hN : 2 ≤ N) [NeZero N]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {D : DynData d} (hβ : 0 < D.invβ) (hV : Torus.IsSmooth D.V) {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hX : SelectedFlow P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X) :
    ∃ f : ℝ → Config d N → ℝ,
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun p : ℝ × (Fin N → Euc d) => f p.1 (fun i => Torus.mk (p.2 i)))
        (Set.Ioo 0 T ×ˢ {Y : Fin N → Euc d | (fun i => Torus.mk (Y i)) ∉ collisionSet d N}) ∧
      (∀ r ∈ Set.Ioo 0 T, ∀ x ∉ collisionSet d N, 0 ≤ f r x) ∧
      ∀ S : Set (ℝ × Config d N), MeasurableSet S → S ⊆ Set.Ioo 0 T ×ˢ (collisionSet d N)ᶜ →
        ∫⁻ t in Set.Ioo 0 T, selectedLaw P X t {x | (t, x) ∈ S} =
          ∫⁻ p in S, ENNReal.ofReal (f p.1 p.2) ∂((volume : Measure ℝ).prod (volume : Measure (Config d N))) := by
  classical
  set O : Set (ℝ × (Fin N → Euc d)) := Ioo 0 T ×ˢ liftedFree d N with hOdef
  have hO : IsOpen O := isOpen_Ioo.prod (isOpen_liftedFree d N)
  have hm := measurable_joint hF.progressive
  have hC := selectedFlow_toContact hX
  have hXm : ∀ t : ℝ, Measurable (X (Real.toNNReal t)) := fun t => hC.adapted _
  haveI := isFiniteMeasure_rhoM (P := P) T X hm
  obtain ⟨ft, hfs, hf0, hfeq⟩ := weyl_cov hO (contDiffOn_bC D hV) hβ
    (fun K _ hK => rhoCov_apply_compact (rhoM P T X) hK)
    (fun F hFs hFc hFO => cov_fke hN hV hT hX hF hFs hFc hFO)
  -- periodicity
  have hper : ∀ (w : Fin N → Lattice d), ∀ p ∈ O, ft (p + (0, lat w)) = ft p := by
    intro w p hp
    have hpa : p + (0, lat w) ∈ O := (mem_O_add_lat T p w).2 hp
    have := density_periodic hO (0, lat w) (fun p => mem_O_add_lat T p w)
      (by
        have e : (fun p : ℝ × (Fin N → Euc d) => p + (0, lat w)) = tau w := by
          funext p; exact (tau_eq w p).symm
        rw [e]; exact map_tau_rhoCov (rhoM P T X) w)
      hfs.continuousOn hf0 hfeq (p + (0, lat w)) hpa
    simpa using this.symm
  set fm : ℝ × (Fin N → Euc d) → ℝ := O.indicator ft with hfm
  have mfm : Measurable fm := by
    have := hfs.continuousOn.measurable_piecewise (g := fun _ => (0 : ℝ)) continuousOn_const
      hO.measurableSet
    convert this using 1
    funext x
    by_cases hx : x ∈ O <;> simp [hfm, hx]
  set f : ℝ → Config d N → ℝ := fun t x => fm (t, repC x) with hfdef
  have hclaim : ∀ p ∈ O, f p.1 (mkC p.2) = ft p := by
    intro p hp
    have h1 : (p.1, repC (mkC p.2)) = p + (0, lat (-flo p.2)) := by
      rw [repC_mkC]
      ext
      · simp
      · simp [lat_neg, sub_eq_add_neg]
    have h2 : p + (0, lat (-flo p.2)) ∈ O := (mem_O_add_lat T p _).2 hp
    show fm (p.1, repC (mkC p.2)) = ft p
    rw [h1, hfm, Set.indicator_of_mem h2, hper _ p hp]
  have hmem : ∀ r ∈ Ioo (0 : ℝ) T, ∀ x ∉ collisionSet d N, (r, repC x) ∈ O := by
    intro r hr x hx
    refine ⟨hr, ?_⟩
    show (fun i => Torus.mk (repC x i)) ∉ collisionSet d N
    rw [mk_repC]; exact hx
  have hfx : ∀ r ∈ Ioo (0 : ℝ) T, ∀ x ∉ collisionSet d N, f r x = ft (r, repC x) := by
    intro r hr x hx
    show fm (r, repC x) = _
    rw [hfm, Set.indicator_of_mem (hmem r hr x hx)]
  refine ⟨f, ?_, ?_, ?_⟩
  · refine hfs.congr (fun p hp => ?_)
    exact hclaim p hp
  · intro r hr x hx
    rw [hfx r hr x hx]
    exact hf0 _ (hmem r hr x hx)
  · intro S hS hSsub
    rw [← rhoM_apply T hm hXm hS]
    have hsubO : lift0 S ⊆ O := by
      intro p hp
      have h1 : Gm p ∈ S := hp.1
      have := hSsub h1
      exact ⟨this.1, this.2⟩
    have hcube : lift0 S ⊆ cubeSet d N := inter_subset_right
    have hr : rhoM P T X S = rhoCov (rhoM P T X) (lift0 S) := by
      rw [rhoCov_cube _ (measurableSet_lift0 hS) hcube, psi_zero_preimage_lift0]
    have hB : rhoCov (rhoM P T X) (lift0 S) = ∫⁻ x in lift0 S, ENNReal.ofReal (ft x) := by
      have := congrArg (fun m => m (lift0 S)) hfeq
      simp only [Measure.restrict_apply (measurableSet_lift0 hS),
        withDensity_apply _ (measurableSet_lift0 hS),
        Measure.restrict_restrict (measurableSet_lift0 hS)] at this
      rw [Set.inter_eq_left.2 hsubO] at this
      exact this
    have hE : ∫⁻ x in lift0 S, ENNReal.ofReal (ft x) = ∫⁻ p in lift0 S, ENNReal.ofReal (f (Gm p).1 (Gm p).2) := by
      refine setLIntegral_congr_fun (measurableSet_lift0 hS) (fun p hp => ?_)
      rw [← hclaim p (hsubO hp)]
      rfl
    have hFm : Measurable (fun y : ℝ × Config d N => ENNReal.ofReal (f y.1 y.2)) :=
      ENNReal.measurable_ofReal.comp (mfm.comp (measurable_fst.prodMk (measurable_repC.comp measurable_snd)))
    rw [hr, hB, hE]
    exact lintegral_lift0 (F := fun y : ℝ × Config d N => ENNReal.ofReal (f y.1 y.2)) hFm hS

end HRS.MC.CepP3
