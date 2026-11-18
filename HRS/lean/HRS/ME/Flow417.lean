import HRS.Sections.Sec4
import HRS.Stochastic.LyonsZhengSpec
import HRS.MD.DOMSpec
import HRS.Equilibrium.PairCorrection
import HRS.Stochastic.Particle
import HRS.MD.Stat
import HRS.Equilibrium.Parametrix.PXFIDAuxO

/-!
# Chunk E, row 4.17: packet M0 (flow bridge) and M1 (forcing equals minus the generator)

`flow_of_hypotheses_proof` (M0): the hypotheses of `integrated_forcing` give a stationary Gibbs flow
with initial configuration `X 0`.  The statements are copied verbatim from `HRS/ME/Spec417.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.ME

variable {d : ℕ}

open HRS HRS.LZ

/-- M0.  The hypotheses of `integrated_forcing` give a stationary Gibbs flow on every horizon, with the
initial configuration `X 0` (which is measurable and equals `X₀` almost surely). -/
theorem flow_of_hypotheses_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) {N : ℕ}
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hW : IsVectorBrownian P W)
    (hind : IndepFun X₀ (fun ω => fun t : ℝ≥0 => W t ω) P)
    (hlaw : P.map X₀ = canonicalGibbs (periodicRiesz d s) V N β)
    (hstr : ∀ T' : ℝ, 0 ≤ T' → IsStrongSolution P (PDE.mfData d s hs0 hsd V β hβ) T' X₀ W X)
    (hfilt : ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
      (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X)
    (H : ℝ) (hH : 0 ≤ H) :
    IsStationaryGibbsFlow P s hs0 hsd V β hβ H (X 0) W X := by
  classical
  haveI : BorelSpace (Torus d) := Pi.borelSpace
  haveI : BorelSpace (Config d N) := Pi.borelSpace
  set D : DynData d := PDE.mfData d s hs0 hsd V β hβ with hD
  have hs : IsStrongSolution P D H X₀ W X := hstr H hH
  have hV2 : Torus.IsCk 2 D.V :=
    (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift V) from hV).of_le
      (WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  have hb : IsLocLipschitzDrift (liftedFree d N) (fun _ Z => liftedDrift D Z) :=
    liftedDrift_locLipschitz D (kernelLocal_of_two_le hd D.hs0 D.hsd).smoothOffZero hV2
  have hae : X 0 =ᵐ[P] X₀ := hs.init
  have hstr0 : IsStrongSolution P D H (X 0) W X :=
    { lift := hs.lift
      init := Filter.Eventually.of_forall (fun _ => rfl)
      cont := hs.cont
      adapted := hs.adapted
      no_collision := hs.no_collision }
  refine ⟨?_, hfilt, ?_⟩
  · refine ⟨(hs.adapted 0), ?_, hW, ?_, Or.inl ⟨hstr0, ?_⟩⟩
    · exact hs.no_collision.mono fun ω h => h 0 (by simpa using hH)
    · exact hind.congr hae.symm (Filter.EventuallyEq.refl _ _)
    · exact pathwiseUnique_of_locLipschitz P D hb H (X 0) W hW
  · exact (Measure.map_congr hae).trans hlaw

/-- Measurability of the quadratic statistic `X ↦ D_N(h; ν)(X)` for a jointly measurable kernel `h`
(copy of the template `eqrem_quadStat_meas`, kept local to this packet). -/
theorem me_flow_quadStat_meas {N : ℕ} {h : Torus d → Torus d → ℝ} (hh : Measurable (Function.uncurry h))
    {ν : Measure (Torus d)} [SFinite ν] :
    Measurable (fun X : Config d N => quadStat h ν X) := by
  have hg : Measurable (fun x : Torus d => ∫ y, h x y ∂ν) :=
    (hh.stronglyMeasurable.integral_prod_right' (ν := ν)).measurable
  unfold quadStat
  have h1 : Measurable (fun X : Config d N => ∑ i, ∑ j ∈ Finset.univ.erase i, h (X i) (X j)) := by
    refine Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_
    exact (hh.comp ((measurable_pi_apply i).prodMk (measurable_pi_apply j)) :
      Measurable fun X : Config d N => Function.uncurry h (X i, X j))
  have h2 : Measurable (fun X : Config d N => ∑ i, ∫ y, h (X i) y ∂ν) :=
    Finset.measurable_sum _ fun i _ => hg.comp (measurable_pi_apply i)
  exact ((measurable_const.mul h1).sub (measurable_const.mul (measurable_const.mul h2))).add measurable_const

/-- M1.  Along a stationary Gibbs flow, for a smooth test `f` with pair corrector `ψ`, the centered
commutator forcing of `integrated_forcing` equals, for every `r ∈ [0,H]` simultaneously and almost
surely, the right-hand side of the normal form (`normal_form` with the generator written out). -/
theorem forcing_eq_generator_form_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (hcrit : s = d / 2) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β)
    (ρβ : Torus d → ℝ) (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ)
    (hρS : Torus.IsSmooth ρβ) (hρpos : ∀ x, 0 < ρβ x) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N) (H : ℝ)
    (hflow : IsStationaryGibbsFlow P s hs0 hsd V β hβ H X₀ W X)
    (f : Torus d → ℝ) (hf : Torus.IsSmooth f) (K₁ : ℝ) (ψ : Torus d → Torus d → ℝ)
    (hψ : IsPairCorrector d s V β ρβ f K₁ ψ) :
    ∀ᵐ ω ∂P, ∀ r : ℝ, 0 ≤ r → r ≤ H →
      centeredCommutatorForcing d s P (fun _ => withDensityReal ρβ) X f r ω =
        -particleGen d s V β (Fstat (N := N) ψ) (X r.toNNReal ω) +
          centeredUnder (canonicalGibbs (periodicRiesz d s) V N β) (errStat d s ρβ ψ)
            (X r.toNNReal ω) -
          (2 / (N : ℝ)) * (Real.sqrt N * centeredUnder (canonicalGibbs (periodicRiesz d s) V N β)
            (fun Y : Config d N => (1 / (N : ℝ)) * ∑ i, aCoef d s ρβ f (Y i)) (X r.toNNReal ω)) := by
  classical
  -- the strong solution on the horizon `H` (the second disjunct of `SelectedFlow` is impossible for `d ≥ 2`)
  have hsol : IsStrongSolution P (PDE.mfData d s hs0 hsd V β hβ) H X₀ W X := by
    rcases hflow.flow.flow with h | ⟨h1, -⟩
    · exact h.1
    · exact absurd h1 (by omega)
  -- stationarity of the marginals on `[0, H]`
  have hstat := HRS.MD.Stat.md_stat_gibbs_flow_stationary_proof hd hs0 hsd V hV β hβ H hN P X₀ W X hflow
  -- the commutator kernel is the transport kernel `hTransport`
  have hcomm : commKernel (periodicRieszGrad d s) (Torus.grad f) = hTransport d s f := by
    funext x y
    unfold commKernel hTransport
    by_cases hxy : x = y
    · subst hxy; simp
    · rw [if_neg hxy]
  have hTm : Measurable (Function.uncurry (hTransport d s f)) :=
    HRS.Parx.PXFID.measurable_hTransport hsd f
  haveI : SFinite (withDensityReal ρβ) := by unfold withDensityReal; infer_instance
  have hQm := me_flow_quadStat_meas (N := N) (h := hTransport d s f) hTm (ν := withDensityReal ρβ)
  have hFm : Measurable (fun Y : Config d N =>
      (1 / 2 : ℝ) * quadStat (hTransport d s f) (withDensityReal ρβ) Y) :=
    measurable_const.mul hQm
  have hFun : ∀ X : Config d N, modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad f)) X
      (withDensityReal ρβ) = (1 / 2 : ℝ) * quadStat (hTransport d s f) (withDensityReal ρβ) X := by
    intro X
    rw [hcomm]
    unfold modulatedEnergy quadStat
    ring
  -- the expectation of the modulated energy at time `t` is its Gibbs expectation
  have hint : ∀ t : ℝ≥0, (t : ℝ) ≤ H →
      ∫ ω', modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad f)) (X t ω')
        (withDensityReal ρβ) ∂P =
        ∫ Y, (1 / 2 : ℝ) * quadStat (hTransport d s f) (withDensityReal ρβ) Y
          ∂(canonicalGibbs (periodicRiesz d s) V N β) := by
    intro t ht
    simp only [hFun]
    have e := integral_map (μ := P) (φ := X t) (hsol.adapted t).aemeasurable hFm.aestronglyMeasurable
    rw [hstat t ht] at e
    exact e.symm
  -- the centered forcing is `½ √N` times the centered quadratic statistic
  have key : ∀ r : ℝ, 0 ≤ r → r ≤ H → ∀ ω : Ω,
      centeredCommutatorForcing d s P (fun _ => withDensityReal ρβ) X f r ω =
        Real.sqrt N / 2 * centeredUnder (canonicalGibbs (periodicRiesz d s) V N β)
          (quadStat (hTransport d s f) (withDensityReal ρβ)) (X r.toNNReal ω) := by
    intro r hr0 hrH ω
    have ht : ((r.toNNReal : ℝ≥0) : ℝ) = r := Real.coe_toNNReal r hr0
    have htH : ((r.toNNReal : ℝ≥0) : ℝ) ≤ H := by rw [ht]; exact hrH
    dsimp only [centeredCommutatorForcing, centeredUnder]
    rw [hint r.toNNReal htH, integral_const_mul, hFun (X r.toNNReal ω)]
    ring
  -- the normal form identity, off collisions
  obtain ⟨C, hC⟩ := normal_form_proof hd hcrit β hβ V hV ρβ hρβ ⟨hρβ.1, hρS, hρpos⟩
  have hid := (hC f K₁ ψ hf hψ N hN).2.2.2.1
  filter_upwards [hsol.no_collision] with ω hω
  intro r hr0 hrH
  have ht : ((r.toNNReal : ℝ≥0) : ℝ) = r := Real.coe_toNNReal r hr0
  have htH : ((r.toNNReal : ℝ≥0) : ℝ) ≤ H := by rw [ht]; exact hrH
  rw [key r hr0 hrH ω]
  exact hid (X r.toNNReal ω) (hω _ htH)

end HRS.ME

end
