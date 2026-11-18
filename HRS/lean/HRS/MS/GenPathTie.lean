import HRS.MS.GenPathAux65

/-!
# S5.6 `general_paths`: the tie to the frozen statement

`general_paths_proof : type_of% @HRS.Whole.general_paths` (`HRS/Whole/Headline.lean`, Theorem S5.6).  Axioms: `propext`,
`Classical.choice`, `Quot.sound`.  The plan is in `HRS/MS/GenPathAux1.lean`; the packets are `GenPathAux1`-`GenPathAux65`:

* `Aux2`-`Aux16` (run 1): pathwise and moment trace comparison (`s56_trace_moment`), remainder moments (`s56_rem_moment`),
  `𝒯 : C([0,T];𝒦) → C([0,T];ℓ²)` (`s56_reconCLM`), the abstract smooth/Wasserstein comparison on `𝒦`.
* `Aux17`-`Aux26`: joint measurability of the orbit features, the clamped `𝒦`-valued Hilbert-Schmidt integrand `s56Phi`,
  the Itô integral `M` with covariation `featureForm` (`s56_particle_martingale`), the initial state `k₀`
  (`s56k0`: a line-integral of the gradient features against `σ(μ_N^0 - ρ_N^0)`, no value-Duhamel identity needed).
* `Aux27`-`Aux36`: the duality identity without pathwise uniqueness, the mild identity at fixed `(t,α)`
  (`s56_mild_coord`), continuity/measurability of `Ξ_N` in `B_m`, the remainder `R = Ξ - A(k₀) - 𝒯M` and its bound
  (`s56_R_bound`).
* `Aux37`-`Aux53`: the deterministic covariation density `Db` (`s56Db`, an `IsDetCovDensity`), whole-space initial enlargement,
  pathCoords machinery (`s56_path_law_eq`), the Gaussian pairings of `𝒯G` (`s56_Gb_fdd`, `s56_recon_coord_eq`), the law of the
  coordinate array of `Y` as `c'' + F` (`s56_Y_array_law`), the abstract comparison with a prescribed initial path (`s56_compare`).
* `Aux54`-`Aux63`: stage 1 / stage 2 assembly on the Gaussian coupling space (`s56_master`), constants (`s56_general_paths_core`).
* `Aux64`-`Aux65`: a.e. measurability of the initial functional from the independence of the Gaussian part
  (`s56_aem_of_indep_sum`; `Measure.map` of a non-a.e.-measurable map is a Dirac mass, so this is not free), then this file.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS HRS.Whole

theorem general_paths_proof : HRS.Whole.GeneralPathsStatement := by
  intro d b₀ hb
  obtain ⟨C₀min, hC⟩ := s56_general_paths_core b₀ hb
  refine ⟨C₀min, fun b hbeq hC0 => ?_⟩
  obtain ⟨C, hCpos, hCmain⟩ := hC b hbeq hC0
  refine ⟨C, hCpos, ?_⟩
  intro S N hN hCad M₂ Ω mΩ P hP X₀ W hW X hX hfilt η₀ hind hmom Y hY
  exact hCmain S N hN hCad M₂ P X₀ W hW X hX hfilt η₀ hind hmom Y hY (fun t α => s56_hη b S N P η₀ Y hY t α)

example := (@general_paths_proof : HRS.Whole.GeneralPathsStatement)

end HRS.MS.GenPath
