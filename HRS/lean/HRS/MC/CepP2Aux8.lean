import HRS.MC.CepP2Aux7

/-!
# Packet CEPP2 (aux 8): local densities and gluing on `O`
-/

open MeasureTheory
open scoped ENNReal
noncomputable section
namespace HRS.MC.CepP2
variable {n : ℕ} {O : Set (XS n)}

variable {invβ : ℝ} {b : XS n → EuclideanSpace ℝ (Fin n)} {ρ : Measure (XS n)}

/-- Local density near a point of `O`. -/
theorem local_piece (hO : IsOpen O) (hb : ContDiffOn ℝ smTop b O)
    (hρ : ∀ K, K ⊆ O → IsCompact K → ρ K < ⊤) (hW : WeakEq O invβ b ρ) (hβ : 0 < invβ)
    {p0 : XS n} (hp0 : p0 ∈ O) :
    ∃ U : Set (XS n), IsOpen U ∧ p0 ∈ U ∧ U ⊆ O ∧ ∃ h : XS n → ℝ, ContDiff ℝ smTop h ∧
      (∀ p, 0 ≤ h p) ∧
      ρ.restrict U = ((volume : Measure (XS n)).restrict U).withDensity (fun p => ENNReal.ofReal (h p)) := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hO p0 hp0
  let χ : ContDiffBump p0 := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  let χt : ContDiffBump p0 := ⟨ε / 2, ε, by positivity, by linarith⟩
  have hsub : tsupport χ ⊆ O := by
    rw [χ.tsupport_eq]
    exact (Metric.closedBall_subset_ball (by show ε / 2 < ε; linarith)).trans hball
  have hχT : IsTest O χ := ⟨χ.contDiff, χ.hasCompactSupport, hsub⟩
  obtain ⟨h, hh, hnn, hν⟩ := exists_local_density hO hb hρ hW hβ hχT (fun p => χ.nonneg) χt.contDiff
    χt.hasCompactSupport (fun p hp => by
      apply χt.one_of_mem_closedBall
      rw [χ.tsupport_eq] at hp
      exact hp)
  refine ⟨Metric.ball p0 (ε / 4), Metric.isOpen_ball, Metric.mem_ball_self (by positivity), ?_, h, hh, hnn, ?_⟩
  · intro p hp
    exact hball (Metric.ball_subset_ball (by linarith) hp)
  · have e1 : ρ.restrict (Metric.ball p0 (ε / 4)) =
        (ρ.withDensity fun p => ENNReal.ofReal (χ p)).restrict (Metric.ball p0 (ε / 4)) := by
      ext A hA
      rw [Measure.restrict_apply hA, Measure.restrict_apply hA,
        withDensity_apply _ (hA.inter Metric.isOpen_ball.measurableSet)]
      rw [setLIntegral_congr_fun (hA.inter Metric.isOpen_ball.measurableSet) (g := fun _ => 1) (fun x hx => by
        have : χ x = 1 := χ.one_of_mem_closedBall (Metric.ball_subset_closedBall hx.2)
        simp [this])]
      simp
    rw [e1, hν, restrict_withDensity Metric.isOpen_ball.measurableSet]


lemma densities_eqOn {V : Set (XS n)} (hV : IsOpen V) {h1 h2 : XS n → ℝ}
    (hc1 : Continuous h1) (hc2 : Continuous h2) (hn1 : ∀ p, 0 ≤ h1 p) (hn2 : ∀ p, 0 ≤ h2 p)
    (e1 : ρ.restrict V = ((volume : Measure (XS n)).restrict V).withDensity (fun p => ENNReal.ofReal (h1 p)))
    (e2 : ρ.restrict V = ((volume : Measure (XS n)).restrict V).withDensity (fun p => ENNReal.ofReal (h2 p))) :
    Set.EqOn h1 h2 V := by
  have hae : (fun p => ENNReal.ofReal (h1 p)) =ᵐ[(volume : Measure (XS n)).restrict V]
      fun p => ENNReal.ofReal (h2 p) := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite₀ hc1.measurable.ennreal_ofReal.aemeasurable
      hc2.measurable.ennreal_ofReal.aemeasurable fun s hs _ => ?_
    have a1 := congrArg (fun m => m s) e1
    have a2 := congrArg (fun m => m s) e2
    simp only [withDensity_apply _ hs] at a1 a2
    rw [← a1, ← a2]
  have hae' : h1 =ᵐ[(volume : Measure (XS n)).restrict V] h2 := by
    filter_upwards [hae] with p hp
    exact (ENNReal.ofReal_eq_ofReal_iff (hn1 p) (hn2 p)).1 hp
  exact Measure.eqOn_open_of_ae_eq hae' hV hc1.continuousOn hc2.continuousOn


lemma dens_restrict_sub {U V : Set (XS n)} (hV : MeasurableSet V) (hVU : V ⊆ U) {g : XS n → ℝ≥0∞}
    (e : ρ.restrict U = ((volume : Measure (XS n)).restrict U).withDensity g) :
    ρ.restrict V = ((volume : Measure (XS n)).restrict V).withDensity g := by
  rw [← Measure.restrict_restrict_of_subset hVU, e, restrict_withDensity hV,
    Measure.restrict_restrict_of_subset hVU]

theorem weyl_XS (hO : IsOpen O) (hb : ContDiffOn ℝ smTop b O)
    (hρ : ∀ K, K ⊆ O → IsCompact K → ρ K < ⊤) (hW : WeakEq O invβ b ρ) (hβ : 0 < invβ) :
    ∃ f : XS n → ℝ, ContDiffOn ℝ smTop f O ∧ (∀ p ∈ O, 0 ≤ f p) ∧
      ρ.restrict O = ((volume : Measure (XS n)).restrict O).withDensity (fun p => ENNReal.ofReal (f p)) := by
  have loc : ∀ p0 : O, ∃ U : Set (XS n), IsOpen U ∧ p0.1 ∈ U ∧ U ⊆ O ∧ ∃ h : XS n → ℝ,
      ContDiff ℝ smTop h ∧ (∀ p, 0 ≤ h p) ∧
      ρ.restrict U = ((volume : Measure (XS n)).restrict U).withDensity (fun p => ENNReal.ofReal (h p)) :=
    fun p0 => local_piece hO hb hρ hW hβ p0.2
  choose U hUo hpU hUO h hh hnn hrest using loc
  classical
  let f : XS n → ℝ := fun q => if hq : q ∈ O then h ⟨q, hq⟩ q else 0
  -- f agrees with the local density on each chart
  have hf : ∀ p0 : O, Set.EqOn f (h p0) (U p0) := by
    intro p0 q hq
    have hqO : q ∈ O := hUO p0 hq
    have hfq : f q = h ⟨q, hqO⟩ q := by simp [f, hqO]
    rw [hfq]
    have hV : IsOpen (U ⟨q, hqO⟩ ∩ U p0) := (hUo _).inter (hUo _)
    have hmem : q ∈ U ⟨q, hqO⟩ ∩ U p0 := ⟨hpU ⟨q, hqO⟩, hq⟩
    have e1 := dens_restrict_sub (U := U ⟨q, hqO⟩) hV.measurableSet Set.inter_subset_left
      (hrest ⟨q, hqO⟩)
    have e2 := dens_restrict_sub (U := U p0) hV.measurableSet Set.inter_subset_right (hrest p0)
    exact densities_eqOn hV (hh _).continuous (hh _).continuous (hnn _) (hnn _) e1 e2 hmem
  -- smoothness and nonnegativity
  have hsm : ContDiffOn ℝ smTop f O := by
    intro q hq
    have hev : f =ᶠ[nhds q] h ⟨q, hq⟩ :=
      Filter.eventuallyEq_of_mem ((hUo ⟨q, hq⟩).mem_nhds (hpU ⟨q, hq⟩)) (hf ⟨q, hq⟩)
    exact ((hh ⟨q, hq⟩).contDiffAt.congr_of_eventuallyEq hev).contDiffWithinAt
  have hnn' : ∀ p ∈ O, 0 ≤ f p := by
    intro p hp
    have := hf ⟨p, hp⟩ (hpU ⟨p, hp⟩)
    rw [this]; exact hnn _ _
  refine ⟨f, hsm, hnn', ?_⟩
  -- countable cover
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable (fun p0 : O => U p0) hUo
  have hcover : (⋃ p0 ∈ T, U p0) = O := by
    rw [hTU]
    refine Set.Subset.antisymm (Set.iUnion_subset fun p0 => hUO p0) fun q hq => ?_
    exact Set.mem_iUnion.2 ⟨⟨q, hq⟩, hpU ⟨q, hq⟩⟩
  have key : ρ.restrict (⋃ p0 ∈ T, U p0) =
      ((volume : Measure (XS n)).withDensity (fun p => ENNReal.ofReal (f p))).restrict (⋃ p0 ∈ T, U p0) := by
    refine (Measure.restrict_biUnion_congr hTc).2 fun p0 _ => ?_
    rw [hrest p0, restrict_withDensity (hUo p0).measurableSet]
    refine withDensity_congr_ae ?_
    refine (ae_restrict_iff' (hUo p0).measurableSet).2 (Filter.Eventually.of_forall fun x hx => ?_)
    show ENNReal.ofReal (h p0 x) = ENNReal.ofReal (f x)
    rw [hf p0 hx]
  rw [hcover] at key
  rw [key, restrict_withDensity hO.measurableSet]

end HRS.MC.CepP2
