import HRS.Sections.AdjKCAux2
import HRS.Sections.AdjKCAux3
import HRS.Sections.AdjKCAux5

/-!
# ADJKC: relocated proofs of the `AdjKSpec` packets C2, C3, B0, B3

Each `<name>_proof` has the statement of `HRS.AdjK.<name>` verbatim and is tied to it by an `example`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.AdjK

open HRS.Uniform

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem adjk_forcing_intervalIntegrable_proof (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    {N : ℕ} (hN : 2 ≤ N) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (T' : ℝ) (hT' : 0 ≤ T') (hX : IsParticleSystem P htr.dyn T' X₀ W X)
    (hF : ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
      (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X) :
    (∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T', ∀ k : NonzeroLattice d,
      IntervalIntegrable (fun r =>
        Real.sqrt N * modulatedEnergy
          (commKernel (periodicRieszGrad d htr.dyn.s)
            (Torus.grad (propagator htr.dyn ρ r t (Torus.realMode k))))
          (X r.toNNReal ω) (withDensityReal (ρ r))) volume 0 t) ∧
    ∀ t ∈ Set.Icc (0 : ℝ) T', ∀ k : NonzeroLattice d,
      AEMeasurable (Function.uncurry fun (r : ℝ) (ω : Ω) =>
        Real.sqrt N * modulatedEnergy
          (commKernel (periodicRieszGrad d htr.dyn.s)
            (Torus.grad (propagator htr.dyn ρ r t (Torus.realMode k))))
          (X r.toNNReal ω) (withDensityReal (ρ r))) ((volume.restrict (Set.Icc 0 t)).prod P) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨ρβ, hth, hsm, hpos, -⟩ := MovLog.movlog_relax2 hd htr
  have hex : ∀ k : NonzeroLattice d, ∀ t : ℝ, 0 ≤ t → ∃ F : ℝ → Torus d → ℝ,
      IsClassicalAdjointSolution htr.dyn ρ t (Torus.realMode k) F ∧
        ∀ r ∈ Set.Icc 0 t, propagator htr.dyn ρ r t (Torus.realMode k) = F r := fun k =>
    (Q40b.q40b_adjoint hd htr hth hsm hpos (j := 2 * d + 10) ⟨d + 5, by ring⟩
      (by push_cast; have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith)
      (HRS.FieldSingAux.isSmooth_realMode k)).1
  refine ⟨?_, ?_⟩
  · filter_upwards [hX.sol.cont, hX.sol.no_collision] with ω hcont hcol t ht k
    obtain ⟨F, hFs, hFp⟩ := hex k t ht.1
    have hc := AdjKC.adjkc_forcing_continuousOn hd htr ht.1 hFs (Xp := fun u => X u ω) hcont
      (fun u hu => hcol u (hu.trans ht.2))
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le ht.1]
    refine ContinuousOn.congr (f := fun r => Real.sqrt N * modulatedEnergy
      (commKernel (periodicRieszGrad d htr.dyn.s) (Torus.grad (F r))) (X r.toNNReal ω)
      (withDensityReal (ρ r))) (hc.const_smul (Real.sqrt N)) fun r hr => ?_
    simp only [hFp r hr]
  · intro t ht k
    obtain ⟨F, hFs, hFp⟩ := hex k t ht.1
    obtain ⟨ℱ, W', hFilt⟩ := hF
    obtain ⟨c₀, hc₀, Λ₁, hΛ₁⟩ := Q40b.q40b_rho_bounds hd1 htr
    have hm := Q40b.q40b_Fm_meas (N := N) (s := htr.dyn.s) (X := X) (ℱ := ℱ) ht.1 htr.dyn.hsd
      hFs.isC12Test (Q40b.q40b_jointCont hd1 htr t) (fun r hr => (hΛ₁ r hr.1).1) hFilt.progressive
    refine ((hm.const_mul (Real.sqrt N)).aemeasurable (μ := (volume.restrict (Set.Icc (0 : ℝ) t)).prod P)).congr ?_
    have h1 : ∀ᵐ r ∂(volume.restrict (Set.Icc (0 : ℝ) t)), r ∈ Set.Icc 0 t :=
      ae_restrict_mem measurableSet_Icc
    have h2 : ∀ᵐ p ∂((volume.restrict (Set.Icc (0 : ℝ) t)).prod P), p.1 ∈ Set.Icc 0 t :=
      Measure.QuasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_fst) h1
    filter_upwards [h2] with p hp
    simp only [Function.uncurry, Q40b.Fm, clampTI_of_mem hp, hFp p.1 hp]

example := (@adjk_forcing_intervalIntegrable_proof : type_of% @HRS.AdjK.adjk_forcing_intervalIntegrable)

theorem adjk_det_convolution_L2_proof (m : ℝ) (T CV c : ℝ) (hT : 0 < T) (hCV : 0 ≤ CV) (hc : 0 < c) :
    ∀ (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m),
      (∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ CV * Real.exp (-c * (t - u))) →
      ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (R : ℝ → Ω → NegSobolev d m), Measurable (Function.uncurry R) → ∀ b : ℝ, 0 ≤ b →
        (∀ r : ℝ, 0 ≤ r → ∫⁻ ω, ‖R r ω‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal (b ^ 2)) →
        ∀ a : ℝ, 0 ≤ a →
          ∫⁻ ω, (⨆ t ∈ ratIcc a (a + T),
              ‖∫ r in (0 : ℝ)..t, Vev t r (R r ω)‖ₑ) ^ 2 ∂P ≤
            ENNReal.ofReal ((CV * (1 / c + T) * b) ^ 2) :=
  AdjKC.adjkc_det_convolution_L2 m T CV c hT hCV hc

example := (@adjk_det_convolution_L2_proof : type_of% @HRS.AdjK.adjk_det_convolution_L2)

theorem adjk_particle_martingale_proof (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    (n : ℝ) (hn : (d : ℝ) / 2 + 2 < n) (T : ℝ) (hT : 0 < T) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hX : IsParticleSystem P htr.dyn T X₀ W X) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsFilteredSolution P ℱ W' W X) :
    ∃ M : ℝ → Ω → NegSobolev d n,
      IsHilbertMartingaleWithCovariation P ℱ T M
        (fun r ω => covForm n β⁻¹ (empirical (X r.toNNReal ω))) ∧
      ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
        NegSobolev.eval (M t ω) φ =
          Real.sqrt N * empiricalMartingale P ℱ W' htr.dyn T (fun _ => φ) X t ω :=
  AdjKC.adjkc_particle_martingale hd htr n hn T hT hN P X₀ W X hX ℱ W' hF

example := (@adjk_particle_martingale_proof : type_of% @HRS.AdjK.adjk_particle_martingale)

end HRS.AdjK
