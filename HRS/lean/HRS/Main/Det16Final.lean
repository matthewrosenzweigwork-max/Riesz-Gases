import HRS.Main.Det16E1
import HRS.Main.TorusTheorems

/-!
# Example A.16: `deterministic_example_proof` (final assembly)

Relocated proof of `HRS.Main.deterministic_example` (statement copied verbatim), see `docs/det16e_notes.md`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory BoundedContinuousFunction

namespace HRS

namespace Main

variable {d : ℕ}

/-- Example A.16, proof of `HRS.Main.deterministic_example`. -/
theorem deterministic_example_proof (s : ℝ) :
    ∃ C₀min : ℝ, ∀ (Rg : PDE.Regime) (ν₀ MB Λ T VB : ℝ) (C₀ Cc Λ' : ℝ), C₀min ≤ C₀ →
    ∀ (hC : IsCoercivityPair d s C₀ Cc)
    (S : MainData d) (hs : S.s = s) (hT : S.T = T) (hβ : ∀ N, S.invβ N = 0)
    (R : ∀ N, Realization d N)
    (hflow : SelectedFlows S R)
    (hfilt : ∀ N : ℕ, 1 ≤ N → ∃ (ℱ : MeasureTheory.Filtration ℝ (R N).mΩ)
      (W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ),
      IsFilteredSolution (R N).P ℱ W' (R N).W (R N).X)
    (hregime : S.RegimeHolds Rg ν₀)
    (hmf : MeanFieldRegularity S (gammaIdx d + 2 + 3) Λ)
    (hmat : PDE.MatBound MB S.M) (hV : PDE.VHyp (gammaIdx d + 2) VB S.V)
    (hsym : Torus.SymNonpos S.M)
    (hΛ' : ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasTransportBound d s (meanFieldDrift (S.dyn N) (S.ρ N t)) Λ')
    (Y : ∀ N, Config d N) (hdet : ∀ N : ℕ, 1 ≤ N → ∀ᵐ ω ∂(R N).P, (R N).X₀ ω = Y N)
    (ηin : NegSobolev d (gammaIdx d : ℝ))
    (hconv : Tendsto (fun N => S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ)
      (empirical (Y N)) S.μ0) atTop (𝓝 ηin))
    (hη : ∀ N : ℕ, 1 ≤ N → ∀ ω, ∀ ψ : Torus d → ℝ, MemSobolev (gammaIdx d : ℝ) ψ →
      Torus.mean ψ = 0 → (R N).η ω ψ = NegSobolev.eval ηin ψ)
    (m₀ : ℕ) (ε : ℕ → ℝ) (Cin : ℝ) (hinit : InitialFluctuation S R m₀ Cin ε (fun _ => ∅))
    (hsmall : Tendsto (fun N => S.κ N * correctedEnergy (S.dyn N) C₀ Λ (S.ρ N) (Y N) 0)
      atTop (𝓝 0))
    (L : LimitCoeffs d)
    (hcoef : CoeffConvergence S L Rg ν₀ MB Λ VB (gammaIdx d + 2) (gammaIdx d)),
    ∀ {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
      (Y' : ℝ → Ω' → NegSobolev d ((gammaIdx d + 2 : ℕ) : ℝ)),
      IsLinearFluctuationSolution P' (L.dyn S) L.ρ ((gammaIdx d + 2 : ℕ) : ℝ) 0 T
        (fun _ => NegSobolev.embed ((gammaIdx d + 2 : ℕ) : ℝ) ηin) Y' →
      ConvergesInLaw
        (fun N => law (R N).P
          (flucPath ((gammaIdx d + 2 : ℕ) : ℝ) T (S.sigma N) (R N).X (S.ρ N)))
        (law P' (toPath ((gammaIdx d + 2 : ℕ) : ℝ) T Y')) := by
  by_cases hok : 1 ≤ d ∧ 0 ≤ s ∧ s < d
  swap
  · refine ⟨0, fun Rg ν₀ MB Λ T VB C₀ Cc Λ' _ hC S hs => ?_⟩
    exact absurd ⟨S.hd, hs ▸ S.hs0, hs ▸ S.hsd⟩ hok
  obtain ⟨hd, hs0, hsd⟩ := hok
  obtain ⟨C₁, hC1⟩ := Det16.det16c_sup_tendsto hd hs0 hsd
  refine ⟨C₁, fun Rg ν₀ MB Λ T VB C₀ Cc Λ' hC₀ hC S hs hT hβ R hflow hfilt hregime hmf hmat hV hsym
    hΛ' Y hdet ηin hconv hη m₀ ε Cin hinit hsmall L hcoef => ?_⟩
  intro Ω' _ P' _ Y' hY
  subst hT
  obtain ⟨𝔈, hS, εs, hεs, hbd⟩ := hC1 Rg ν₀ MB Λ VB C₀ Cc Λ' hC₀ hC S hs hβ R hflow hfilt hregime hmf
    hmat hV hsym hΛ' Y hdet hsmall
  obtain ⟨hcontξ, hlaw⟩ := Det16.det16d_limit_law s Rg ν₀ MB Λ S.T VB S hs rfl L hcoef ηin P' Y' hY
  rw [hlaw]
  have hLA := Det16.det16d_LA_eq_one S L Rg ν₀ MB Λ VB hβ hcoef
  have hγ3 : d + 3 ≤ gammaIdx d := by unfold gammaIdx; omega
  have hγγ : (gammaIdx d : ℝ) < ((gammaIdx d + 2 : ℕ) : ℝ) := by exact_mod_cast Nat.lt_add_of_pos_right (by omega)
  have hm2 : (d : ℝ) < 2 * ((gammaIdx d + 2 : ℕ) : ℝ) := by
    have h : (d : ℝ) + 3 ≤ gammaIdx d := by exact_mod_cast hγ3
    push_cast
    linarith
  have hV1 : Torus.IsCk 1 S.V :=
    hV.1.of_le (by exact_mod_cast (by omega : 1 ≤ gammaIdx d + 2 + 3))
  have key : ∀ N : ℕ, 2 ≤ N → ∃ ξ : PathSpace d ((gammaIdx d + 2 : ℕ) : ℝ) S.T,
      law (R N).P (flucPath ((gammaIdx d + 2 : ℕ) : ℝ) S.T (S.sigma N) (R N).X (S.ρ N)) =
        Measure.dirac ξ ∧
      ∀ t : Set.Icc (0 : ℝ) S.T, ‖PathSpace.at' ξ t - NegSobolev.embed ((gammaIdx d + 2 : ℕ) : ℝ)
        (transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ)
          (S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ) (empirical (Y N)) S.μ0))‖ ≤ εs N := by
    intro N hN
    obtain ⟨x, hx, ξ, hl, hξ⟩ := Det16.det16e_path_data hβ hflow (r := gammaIdx d + 2 + 3) (by omega)
      hmf hV1 (by omega : 1 ≤ N) (Y N) (hdet N (by omega)) hm2
    refine ⟨ξ, hl, fun t => ?_⟩
    obtain ⟨ω, h1, h2⟩ := (hx.and (hbd N hN _ hγγ.le)).exists
    have h3 := h2 t t.2
    rw [h1 (Real.toNNReal t) (by rw [Real.coe_toNNReal _ t.2.1]; exact t.2.2)] at h3
    rw [hξ t]
    exact h3
  choose! ξ hξl hξb using key
  haveI : Nonempty (Set.Icc (0 : ℝ) S.T) := ⟨⟨0, le_rfl, S.hT.le⟩⟩
  refine HRS.A34.a34_converges_congr (μ := fun N => Measure.dirac (ξ N)) ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with N hN
    exact (hξl N hN).symm
  refine Det16.det16b_dirac_conv ξ _ ?_
  rw [Metric.tendsto_nhds]
  intro η hη
  have hF := Det16.det16b_transport_unif_t s Rg ν₀ MB Λ S.T VB S hs rfl L hcoef
    (fun N => S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ) (empirical (Y N)) S.μ0) ηin hconv hγγ
    (η / 4) (by positivity)
  filter_upwards [eventually_ge_atTop 2, hF, hεs.eventually (Iio_mem_nhds (half_pos hη))] with N hN hN2 hN3
  rw [dist_eq_norm]
  have hlt : εs N + η / 4 < η := by
    have : εs N < η / 2 := hN3
    linarith
  refine lt_of_le_of_lt ?_ hlt
  refine (ContinuousMap.norm_le_of_nonempty (f := (ξ N : C(Set.Icc (0 : ℝ) S.T, _)) -
    (Det16.det16d_xiPath (L.dyn S) L.ρ ((gammaIdx d + 2 : ℕ) : ℝ) S.T ηin hcontξ :
      C(Set.Icc (0 : ℝ) S.T, _)))).2 fun t => ?_
  have h1 := hξb N hN t
  have h2 := hN2 t t.2
  rw [(Det16.det16d_zero_temp_scales S hβ N).2.1, hLA, one_smul, one_smul] at h2
  have h3 := norm_sub_le_norm_sub_add_norm_sub (PathSpace.at' (ξ N) t) (NegSobolev.embed ((gammaIdx d + 2 : ℕ) : ℝ)
        (transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ)
          (S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ) (empirical (Y N)) S.μ0)))
    (NegSobolev.embed ((gammaIdx d + 2 : ℕ) : ℝ) (transportField (L.dyn S) L.ρ t (gammaIdx d : ℝ) ηin))
  exact h3.trans (add_le_add h1 h2.le)

/-- the relocation tie. -/
example := (@deterministic_example_proof : type_of% @HRS.Main.deterministic_example)

end HRS.Main
