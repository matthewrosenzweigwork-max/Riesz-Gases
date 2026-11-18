import HRS.MC.CepP3Aux14

/-!
# Packet P3, Aux15: periodicity of the density
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MC.CepP3

open HRS

variable {d N : ℕ}

theorem tau_psi (w u : Fin N → Lattice d) (q : ℝ × Config d N) :
    tau w (psi u q) = psi (u + w) q := by
  simp only [tau, psi, lat_add, add_assoc]

theorem measurable_tau (w : Fin N → Lattice d) : Measurable (tau (d := d) w) :=
  (continuous_tau w).measurable

/-- The lifted measure is invariant under the lattice translations. -/
theorem map_tau_rhoCov (ρ : Measure (ℝ × Config d N)) (w : Fin N → Lattice d) :
    Measure.map (tau w) (rhoCov ρ) = rhoCov ρ := by
  refine Measure.ext fun B hB => ?_
  rw [Measure.map_apply (measurable_tau w) hB]
  unfold rhoCov
  rw [Measure.sum_apply _ (measurable_tau w hB), Measure.sum_apply _ hB]
  have : ∀ u : Fin N → Lattice d, (Measure.map (psi u) ρ) (tau w ⁻¹' B) = (Measure.map (psi (u + w)) ρ) B := by
    intro u
    rw [Measure.map_apply (measurable_psi u) (measurable_tau w hB),
      Measure.map_apply (measurable_psi (u + w)) hB]
    congr 1
    ext q
    simp only [mem_preimage, tau_psi]
  simp only [this]
  exact (Equiv.addRight w).tsum_eq (fun u => (Measure.map (psi u) ρ) B)

theorem density_periodic {O : Set (ℝ × (Fin N → Euc d))} (hO : IsOpen O)
    (a : ℝ × (Fin N → Euc d)) (hOa : ∀ p, p + a ∈ O ↔ p ∈ O)
    {ν : Measure (ℝ × (Fin N → Euc d))} (hν : Measure.map (fun p => p + a) ν = ν)
    {f : ℝ × (Fin N → Euc d) → ℝ} (hf : ContinuousOn f O) (hf0 : ∀ p ∈ O, 0 ≤ f p)
    (hνf : ν.restrict O = (volume.restrict O).withDensity (fun p => ENNReal.ofReal (f p))) :
    ∀ p ∈ O, f (p - a) = f p := by
  classical
  haveI := isAddHaar_volume_cov (d := d) (N := N)
  have hsub : ∀ p ∈ O, p - a ∈ O := fun p hp => (hOa (p - a)).1 (by simpa using hp)
  set g : ℝ × (Fin N → Euc d) → ℝ := fun p => f (p - a) with hg
  have hgc : ContinuousOn g O :=
    hf.comp (continuous_sub_right a).continuousOn (fun p hp => hsub p hp)
  set fm := O.indicator f with hfm
  set gm := O.indicator g with hgm
  have mfm : Measurable fm := by
    have := hf.measurable_piecewise (g := fun _ => (0 : ℝ)) continuousOn_const hO.measurableSet
    convert this using 1
    funext x
    by_cases hx : x ∈ O <;> simp [hfm, hx]
  have mgm : Measurable gm := by
    have := hgc.measurable_piecewise (g := fun _ => (0 : ℝ)) continuousOn_const hO.measurableSet
    convert this using 1
    funext x
    by_cases hx : x ∈ O <;> simp [hgm, hx]
  have h1 : ∀ B : Set (ℝ × (Fin N → Euc d)), MeasurableSet B → B ⊆ O →
      ν B = ∫⁻ x in B, ENNReal.ofReal (f x) := by
    intro B hBm hBO
    have := congrArg (fun m => m B) hνf
    simp only [Measure.restrict_apply hBm, withDensity_apply _ hBm,
      Measure.restrict_restrict hBm] at this
    rw [Set.inter_eq_left.2 hBO] at this
    rw [this]
  have hB : ∀ B : Set (ℝ × (Fin N → Euc d)), MeasurableSet B → B ⊆ O →
      ∫⁻ x in B, ENNReal.ofReal (fm x) = ∫⁻ x in B, ENNReal.ofReal (gm x) := by
    intro B hBm hBO
    have hpre : (fun p => p + a) ⁻¹' B ⊆ O := fun p hp => (hOa p).1 (hBO hp)
    have hmpre : MeasurableSet ((fun p => p + a) ⁻¹' B) := (measurable_add_const a) hBm
    have h2 : ∫⁻ x in B, ENNReal.ofReal (f x) = ∫⁻ x in B, ENNReal.ofReal (g x) := by
      calc ∫⁻ x in B, ENNReal.ofReal (f x) = ν B := (h1 B hBm hBO).symm
        _ = ν ((fun p => p + a) ⁻¹' B) := by
            rw [← Measure.map_apply (measurable_add_const a) hBm, hν]
        _ = ∫⁻ x in (fun p => p + a) ⁻¹' B, ENNReal.ofReal (f x) := h1 _ hmpre hpre
        _ = ∫⁻ x in (fun p => p + a) ⁻¹' B, ENNReal.ofReal (g (x + a)) := by
            refine lintegral_congr fun x => ?_
            simp [hg]
        _ = ∫⁻ y in B, ENNReal.ofReal (g y) :=
            (measurePreserving_add_right volume a).setLIntegral_comp_preimage_emb
              (measurableEmbedding_addRight a) (fun y => ENNReal.ofReal (g y)) B
    have e1 : ∫⁻ x in B, ENNReal.ofReal (fm x) = ∫⁻ x in B, ENNReal.ofReal (f x) :=
      setLIntegral_congr_fun hBm (fun x hx => by simp [hfm, Set.indicator_of_mem (hBO hx)])
    have e2 : ∫⁻ x in B, ENNReal.ofReal (gm x) = ∫⁻ x in B, ENNReal.ofReal (g x) :=
      setLIntegral_congr_fun hBm (fun x hx => by simp [hgm, Set.indicator_of_mem (hBO hx)])
    rw [e1, e2, h2]
  have hae : (fun x => ENNReal.ofReal (fm x)) =ᵐ[volume.restrict O] (fun x => ENNReal.ofReal (gm x)) := by
    refine ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite (μ := volume.restrict O)
      (ENNReal.measurable_ofReal.comp mfm) (ENNReal.measurable_ofReal.comp mgm) ?_
    intro s hs _
    rw [Measure.restrict_restrict hs]
    exact hB (s ∩ O) (hs.inter hO.measurableSet) Set.inter_subset_right
  have hae2 : f =ᵐ[volume.restrict O] g := by
    filter_upwards [hae, ae_restrict_mem hO.measurableSet] with x hx hxO
    have e1 : fm x = f x := Set.indicator_of_mem hxO _
    have e2 : gm x = g x := Set.indicator_of_mem hxO _
    rw [e1, e2] at hx
    exact (ENNReal.ofReal_eq_ofReal_iff (hf0 x hxO) (hf0 _ (hsub x hxO))).1 hx
  exact fun p hp => (Measure.eqOn_open_of_ae_eq (μ := volume) hae2 hO hf hgc hp).symm

end HRS.MC.CepP3
