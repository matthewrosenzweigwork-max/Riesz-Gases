import HRS.Uniform.Q48dAssembly
import HRS.Uniform.Q48eAux1
import HRS.Uniform.Q48eAux4

/-!
# Lemma 3.31 `stationary_noise`: relocated proof (packet Q48d)

`stationary_noise_proof` has the statement of `HRS.Uniform.stationary_noise` verbatim; it is `stationary_noise_of_evo`
(`HRS/Uniform/Q48dAssembly.lean`, sorry-free) applied to the single remaining input `q48d_evolution_input`
(`Q48d.EvoInput`: Lemma 3.27 for the frozen thermal coefficient, see the docstring there), which is open.
-/

noncomputable section

open HRS HRS.Uniform
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Uniform

universe u

variable {d : ℕ}

/-- OPEN INPUT (Q48e).  For the frozen thermal coefficient the dual evolution on `E_m`, `m ≥ m₁`, is a plain strongly
continuous evolution and satisfies the window maximal estimate of Lemma 3.27 (3) (`Q48d.WinMaxU`, convolutions a.e.
strongly measurable, probability spaces of every universe `u`), with constants independent of `Vev`.  It follows from
Lemma 3.27 / 3.17 once these are available in this form (see the report). -/
theorem q48d_evolution_input (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (_ : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (_ : IsThermalDensity (periodicRiesz d s) V β ρβ) (_ : Torus.IsSmooth ρβ) (_ : ∀ x, 0 < ρβ x) :
    Q48d.EvoInput.{u} d s hs0 hsd β hβ V ρβ := by
  rename_i hVs hth hρs hpos
  have hprob : IsProbDensity ρβ := hth.1
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  refine ⟨(PDE.mStar d : ℝ) + d, fun m hm => ?_⟩
  have hplain : ∀ Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m,
      IsDualEvolution (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) m Vev →
      ∀ T : ℝ, 0 ≤ T → IsPlainEvolution Vev T := fun Vev hdual T hT =>
    ⟨fun t ht => Q48e.vev_self hd s hs0 hsd β hβ V hVs ρβ hprob hρs hpos hdual t ht.1,
      fun a r t ha har hrt _ => Q48e.vev_comp hd s hs0 hsd β hβ V hVs ρβ hprob hρs hpos hdual a r t ha har hrt,
      fun x => Q48e.vev_cont hd s hs0 hsd β hβ V hVs ρβ hprob hρs hpos m hm hdual T hT x⟩
  refine ⟨fun T hT => ?_, hplain⟩
  obtain ⟨c, hc⟩ := Q48e.vev_quasi hd s hs0 hsd β hβ V hVs ρβ hprob hρs hpos m (by linarith)
  refine ⟨Kot.CD 2 (2 * c) T, Kot.CD_nonneg _ _ _, fun Vev hdual => ?_⟩
  refine Q48e.winmax_of_quasi (hplain Vev hdual) (K := 2 * c) (fun u t hu hut => ?_) hT.le
  rw [show 2 * c * (t - u) / 2 = c * (t - u) by ring]
  exact hc Vev hdual u t hu hut

theorem stationary_noise_proof (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (_ : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (_ : IsThermalDensity (periodicRiesz d s) V β ρβ) (_ : Torus.IsSmooth ρβ) (_ : ∀ x, 0 < ρβ x) :
    ∃ m₀ : ℝ, ∀ m : ℝ, m₀ ≤ m → ∀ Cv : ℝ, ∀ T : ℝ, 0 < T → ∃ C : ℝ, 0 ≤ C ∧
      ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
        (ℱ : Filtration ℝ mΩ) (𝒢 : InitialSigma ℱ) (N : ℕ) (_ : 1 ≤ N) (δ : ℝ) (_ : 0 ≤ δ)
        (X : ℝ → Ω → Config d N) (Q : Measure (Config d N)) [IsProbabilityMeasure Q] (_ : ∀ t : ℝ, 0 ≤ t → P.map (X t) = Q)
        (_ : ∀ f : Torus d → ℝ, Measurable f → MemLp f 2 (withDensityReal ρβ) →
          evariance (fun x : Config d N => pair (empirical x) f) Q ≤
            ENNReal.ofReal (Cv * (N : ℝ)⁻¹ * ∫ x, f x ^ 2 ∂(withDensityReal ρβ)))
        (g : Torus d → ℝ) (_ : Measurable g)
        (_ : (N : ℝ≥0∞)⁻¹ • ∑ i, Q.map (fun x : Config d N => x i) =
          (withDensityReal ρβ).withDensity fun x => ENNReal.ofReal (g x))
        (_ : ∫⁻ x, ‖g x - 1‖ₑ ^ 2 ∂(withDensityReal ρβ) ≤ ENNReal.ofReal ((Cv * δ) ^ 2))
        (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m)
        (_ : IsDualEvolution (PDE.mfData d s hs0 hsd V β hβ) (fun _ => ρβ) m Vev)
        (M : ℝ → Ω → NegSobolev d m)
        (_ : ∀ S : ℝ, 0 ≤ S →
          IsHilbertMartingaleWithCovariation P ℱ S M
            (fun r ω => covForm m β⁻¹ (empirical (X r ω)))),
        ∃ (Ω' : Type u) (mΩ' : MeasurableSpace Ω') (P' : ProbabilityMeasure Ω') (π : Ω' → Ω)
          (ℱ' : Filtration ℝ mΩ') (Gb : ℝ → Ω' → NegSobolev d m)
          (Sd : ℝ → Ω' → (NegSobolev d m →L[ℝ] NegSobolev d m →L[ℝ] ℝ))
          (Z : ℝ → Ω' → NegSobolev d m),
          IsAdaptedGaussianCoupling P ℱ ⊤ 𝒢 M (fun r ω => covForm m β⁻¹ (empirical (X r ω)))
            (fun r => covForm m β⁻¹ (withDensityReal ρβ)) (fun _ _ => True) (fun _ _ => 0)
            P' π ℱ' Gb Sd ∧
          (∀ t : ℝ, 0 ≤ t → IsStochConv (P' : Measure Ω') Vev (ContinuousLinearMap.id ℝ (NegSobolev d m))
            (fun τ ω' => M τ (π ω') - Gb τ ω') 0 t (Z t)) ∧
          (∀ᵐ ω' ∂(P' : Measure Ω'), ContinuousOn (fun t => Z t ω') (Set.Ici 0)) ∧
          ∀ a : ℝ, 0 ≤ a →
            (∫⁻ ω', (⨆ t ∈ Set.Icc a (a + T), ‖Z t ω'‖ₑ) ^ 2 ∂(P' : Measure Ω')) ^ (1 / 2 : ℝ) ≤
              ENNReal.ofReal (C * ((N : ℝ) ^ (-(1 : ℝ) / 2) + δ))
    := by
  rename_i hVs hth hρs hpos
  exact Q48d.stationary_noise_of_evo hd s hs0 hsd β hβ V hVs ρβ hth hρs hpos
    (q48d_evolution_input.{u} hd s hs0 hsd β hβ V hVs ρβ hth hρs hpos)

example := (@stationary_noise_proof : type_of% @HRS.Uniform.stationary_noise)

end Uniform

end HRS
