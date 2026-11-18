import HRS.Appendix.B15DAux4

/-!
# Packet D2 (proofs, part 5): the `eqT` identity of the configuration weak solution

Relocated proof of `d1_law_eqT`: for `τ > 0` the expectation identity `d1_ito_expectation_proof` applied to
`f_r = d1_cl (Φ_r ∘ e⁻¹)` (bounded with bounded derivatives by periodicity), transported to the configuration
space by `integral_map`, and the Itô drift identified with `Φt + d1_configGen` by
`d1_itoGen_eq_configGen_proof`; the case `τ = 0` is trivial.  Uses `d1_isC12On_of_isC12Test` (the other
packet's sorried bridge, so the `_proof` depends on its `sorryAx`).  The frozen sorried statement lives in
`HRS/Appendix/B15DAux1.lean`; this file restates it verbatim as `d1_law_eqT_proof`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS

section D2proofs5

variable {d N : ℕ}

/-- Proof of `d1_law_eqT`. -/
theorem d1_law_eqT_proof {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hW' : IsBrownianFiltration P ℱ W') {κ : ℝ} (hκ : 0 ≤ κ) {bC : Config d N → Fin N → Euc d}
    (hbC : Continuous (d1_liftDrift bC)) {Y₀ : Ω → Fin N → Euc d}
    (hY₀ : ∀ t : ℝ, Measurable[ℱ t] Y₀) {Y : ℝ → Ω → Fin N → Euc d}
    (hY : IsAdditiveSDESolution P ℱ W' (fun _ => d1_liftDrift bC) (d1_noise d N κ) Y₀
      (fun _ => ⊤) Y)
    {T : ℝ} (τ : ℝ) (hτ : τ ∈ Set.Icc 0 T) (Φ Φt : ℝ → Config d N → ℝ)
    (hΦ : IsC12Test τ (fun r => Φ r ∘ (d1_configEquiv d N).symm)
      (fun r => Φt r ∘ (d1_configEquiv d N).symm)) :
    ∫ X, Φ τ X ∂(d1_lawOf P Y τ) = ∫ X, Φ 0 X ∂(d1_lawOf P Y 0) +
      ∫ s in Set.Icc 0 τ, ∫ X, (Φt s X + d1_configGen κ bC (Φ s) X) ∂(d1_lawOf P Y s) := by
  obtain ⟨hτ0, hτT⟩ := hτ
  rcases hτ0.eq_or_lt with h0 | hpos
  · subst h0
    simp
  have hf := (d1_isC12On_of_isC12Test_proof hpos hΦ).1
  -- the transported test functions are bounded with bounded derivatives, by periodicity
  set fn : ℝ → (Fin N → Euc d) → ℝ := fun r => d1_cl (Φ r ∘ (d1_configEquiv d N).symm) with hfn
  have hper1 : ∀ s (Y : Fin N → Euc d) (v : Fin N → Euc d), IsLatticeVec v → fn s (Y + v) = fn s Y := by
    intro s Y v hv
    simp only [hfn, d1_cl]
    rw [mk_add_lattice_vec hv Y]
  have hper2 : ∀ s (Y v : Fin N → Euc d), IsLatticeVec v →
      fderiv ℝ (fn s) (Y + v) = fderiv ℝ (fn s) Y :=
    fun s Y v hv => fderiv_periodic_add (fun x => hper1 s x v hv) Y
  have hper3 : ∀ s (Y v : Fin N → Euc d), IsLatticeVec v →
      fderiv ℝ (fderiv ℝ (fn s)) (Y + v) = fderiv ℝ (fderiv ℝ (fn s)) Y :=
    fun s Y v hv => fderiv_periodic_add (fun x => hper2 s x v hv) Y
  have hper4 : ∀ s (Y v : Fin N → Euc d), IsLatticeVec v →
      derivWithin (fun r => fn r (Y + v)) (Set.Icc 0 τ) s = derivWithin (fun r => fn r Y) (Set.Icc 0 τ) s := by
    intro s Y v hv
    have e : (fun r => fn r (Y + v)) = (fun r => fn r Y) := funext fun r => hper1 r Y v hv
    rw [e]
  obtain ⟨C1, h1⟩ := bounded_of_periodic (T := τ) (fun s y => fn s y) hf.cont
    (fun s Y v hv => hper1 s Y v hv)
  obtain ⟨C2, h2⟩ := bounded_of_periodic (T := τ) (fun s y => ‖fderiv ℝ (fn s) y‖)
    hf.cont_fderiv.norm (fun s Y v hv => by simp only [hper2 s Y v hv])
  have hc3 : ContinuousOn (fun p : ℝ × (Fin N → Euc d) => ‖fderiv ℝ (fderiv ℝ (fn p.1)) p.2‖)
      (Set.Icc 0 τ ×ˢ (Set.univ : Set (Fin N → Euc d))) :=
    ContinuousOn.norm (f := fun p : ℝ × (Fin N → Euc d) => fderiv ℝ (fderiv ℝ (fn p.1)) p.2)
      hf.cont_fderiv₂
  obtain ⟨C3, h3⟩ := bounded_of_periodic (T := τ) (fun s y => ‖fderiv ℝ (fderiv ℝ (fn s)) y‖)
    hc3 (fun s Y v hv => by simp only [hper3 s Y v hv])
  obtain ⟨C4, h4⟩ := bounded_of_periodic (T := τ)
    (fun s y => |derivWithin (fun r => fn r y) (Set.Icc 0 τ) s|)
    (continuous_abs.comp_continuousOn hf.cont_deriv) (fun s Y v hv => by simp only [hper4 s Y v hv])
  have hbd : ∃ C : ℝ, ∀ s ∈ Set.Icc 0 τ, ∀ y, |fn s y| ≤ C ∧ ‖fderiv ℝ (fn s) y‖ ≤ C ∧
      ‖fderiv ℝ (fderiv ℝ (fn s)) y‖ ≤ C ∧
        |derivWithin (fun r => fn r y) (Set.Icc 0 τ) s| ≤ C := by
    refine ⟨max (max C1 C2) (max C3 C4), fun s hs y => ⟨?_, ?_, ?_, ?_⟩⟩
    · have := h1 s hs y
      rw [Real.norm_eq_abs] at this
      exact this.trans (le_max_of_le_left (le_max_left _ _))
    · have := h2 s hs y
      rw [norm_norm] at this
      exact this.trans (le_max_of_le_left (le_max_right _ _))
    · have := h3 s hs y
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans (le_max_of_le_right (le_max_left _ _)))
    · have := h4 s hs y
      rw [Real.norm_eq_abs, abs_abs] at this
      exact this.trans (le_max_of_le_right (le_max_right _ _))
  -- the Dynkin expectation identity along the regularised solution
  have hExp := d1_ito_expectation_proof hW' hκ hbC hY₀ hY hτ0 (f := fn) hf hbd
    (t := τ) ⟨hτ0, le_refl τ⟩
  -- measurability on the configuration space
  have hcontτ : ∀ r ∈ Set.Icc (0 : ℝ) τ, Continuous (fun Y : Fin N → Euc d => fn r Y) := fun r hr =>
    ContinuousOn.comp_continuous (f := fun Y : Fin N → Euc d => (r, Y)) hf.cont
      (continuous_const.prodMk continuous_id) (fun Y => ⟨hr, mem_univ Y⟩)
  have hrep : Measurable (fun X : Config d N => fun i => Torus.rep (X i)) :=
    measurable_pi_iff.2 fun i => (measurable_torusRep d).comp (measurable_pi_apply i)
  have hΦm : ∀ r ∈ Set.Icc (0 : ℝ) τ, Measurable (Φ r) := by
    intro r hr
    have e : Φ r = fun X : Config d N => fn r (fun i => Torus.rep (X i)) := by
      funext X
      simp only [hfn, d1_cl, Torus.mk_rep, Function.comp_apply, MeasurableEquiv.symm_apply_apply]
    rw [e]
    exact (hcontτ r hr).measurable.comp hrep
  have hΦtm : ∀ r ∈ Set.Icc (0 : ℝ) τ, Measurable (Φt r) := by
    intro r hr
    have hc : Continuous (fun x : Torus (N * d) => Φt r ((d1_configEquiv d N).symm x)) :=
      hΦ.cont_time_deriv.comp (Continuous.prodMk (continuous_const (y := (⟨r, hr⟩ : Set.Icc (0 : ℝ) τ)))
        continuous_id)
    have e : Φt r = (fun x : Torus (N * d) => Φt r ((d1_configEquiv d N).symm x)) ∘
        (d1_configEquiv d N) := funext fun X => by simp
    rw [e]
    exact hc.measurable.comp (d1_configEquiv d N).measurable
  have hgen : ∀ s ∈ Set.Icc (0 : ℝ) τ, Measurable (fun X : Config d N => d1_configGen κ bC (Φ s) X) := by
    intro s hs
    have hsame : (fun X : Config d N => d1_configGen κ bC (Φ s) X) =
        (fun Y : Fin N → Euc d => κ * ∑ k : Fin N × Fin d,
            fderiv ℝ (fderiv ℝ (fn s)) Y (configBasis d N k) (configBasis d N k)
          + fderiv ℝ (fn s) Y (d1_liftDrift bC Y)) ∘ (fun X : Config d N => fun i => Torus.rep (X i)) := by
      funext X
      have hcl : configLift (fun _ => Φ s) 0 = fn s := by
        funext Y
        simp [configLift, hfn, d1_cl]
      have hdr : d1_liftDrift bC (fun i => Torus.rep (X i)) = bC X := by
        simp [d1_liftDrift, Torus.mk_rep]
      unfold d1_configGen
      simp only [Function.comp_apply]
      rw [hcl, hdr]
    rw [hsame]
    refine Measurable.comp ?_ hrep
    have h2s := ContinuousOn.comp_continuous (f := fun Y : Fin N → Euc d => ((s, Y) : ℝ × (Fin N → Euc d)))
      hf.cont_fderiv₂ (continuous_const.prodMk continuous_id) (fun Y => ⟨hs, mem_univ Y⟩)
    have h1s := ContinuousOn.comp_continuous (f := fun Y : Fin N → Euc d => ((s, Y) : ℝ × (Fin N → Euc d)))
      hf.cont_fderiv (continuous_const.prodMk continuous_id) (fun Y => ⟨hs, mem_univ Y⟩)
    have hdrift : Continuous (fun Y : Fin N → Euc d => d1_liftDrift bC Y) := hbC
    refine Continuous.measurable (continuous_const.mul (continuous_finset_sum _ fun k _ => ?_) |>.add ?_)
    · exact (h2s.clm_apply continuous_const).clm_apply continuous_const
    · exact h1s.clm_apply hdrift
  -- the time-slice integrals identified with the Itô drift
  have hsint : ∀ s ∈ Set.Icc (0 : ℝ) τ,
      ∫ X, (Φt s X + d1_configGen κ bC (Φ s) X) ∂(d1_lawOf P Y s)
        = ∫ ω, d1_itoGen κ bC τ (fun r => d1_cl (Φ r ∘ (d1_configEquiv d N).symm)) s (Y s ω) ∂P := by
    intro s hs
    have hm : Measurable (fun ω i => Torus.mk (Y s ω i)) :=
      d1_measurable_proj ((hY.adapted s).mono (ℱ.le s) le_rfl)
    unfold d1_lawOf
    have hmeas : AEStronglyMeasurable (fun X : Config d N => Φt s X + d1_configGen κ bC (Φ s) X)
        (Measure.map (fun ω i => Torus.mk (Y s ω i)) P) :=
      ((hΦtm s hs).add (hgen s hs)).aestronglyMeasurable
    rw [integral_map hm.aemeasurable hmeas]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    exact (d1_itoGen_eq_configGen_proof hκ hpos hΦ hs (Y s ω)).symm
  have hin : ∀ r ∈ Set.Icc (0 : ℝ) τ, ∫ X, Φ r X ∂(d1_lawOf P Y r) = ∫ ω, fn r (Y r ω) ∂P := by
    intro r hr
    have hm : Measurable (fun ω i => Torus.mk (Y r ω i)) :=
      d1_measurable_proj ((hY.adapted r).mono (ℱ.le r) le_rfl)
    unfold d1_lawOf
    rw [integral_map hm.aemeasurable (hΦm r hr).aestronglyMeasurable]
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp [hfn, d1_cl]
  rw [hin τ ⟨hτ0, le_refl τ⟩, hin 0 ⟨le_refl 0, hpos.le⟩, setIntegral_congr_fun measurableSet_Icc hsint]
  exact hExp

example := (@d1_law_eqT_proof : type_of% @d1_law_eqT)

end D2proofs5

end HRS
