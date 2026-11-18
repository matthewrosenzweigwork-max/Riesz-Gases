import HRS.Sections.AdjKEAux9

/-!
# ADJKE: relocated proof of the `AdjKSpec` packet B3 (`adjk_mild_decomposition`, repaired statement with `hZm`)

Route: the mild identity for every rational time and mode (`adjke_identity_fixed`: `dyncmp_ae_identity`,
`adjke_pair_identification`, `dyncmp_fluc_eq`), then continuity in `t` of the four terms on a common full-measure set
(statistic coordinates: `adjke_lhs_continuousOn`; dual orbit: strong continuity of the evolution; `Z`: `hZc`;
forcing: locally Lipschitz, `adjke_forcing_lipschitz`) and density of the rationals.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.AdjK

open HRS.Uniform

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem adjk_mild_decomposition_proof (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    (m : ℝ) (hm : (d : ℝ) / 2 + 2 < m) (T : ℝ) (hT : 0 < T) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hX : IsParticleSystem P htr.dyn T X₀ W X) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsFilteredSolution P ℱ W' W X)
    (M : ℝ → Ω → NegSobolev d m)
    (hM : IsHilbertMartingaleWithCovariation P ℱ T M
      (fun r ω => covForm m β⁻¹ (empirical (X r.toNNReal ω))))
    (hMid : ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P,
      NegSobolev.eval (M t ω) φ =
        Real.sqrt N * empiricalMartingale P ℱ W' htr.dyn T (fun _ => φ) X t ω)
    (Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m) (hV : IsDualEvolution htr.dyn ρ m Vev)
    (Z : ℝ → Ω → NegSobolev d m)
    (hZ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      IsStochConv P Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) M 0 t (Z t))
    (hZm : ∀ t ∈ Set.Icc (0 : ℝ) T, AEMeasurable (Z t) P)
    (hZc : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 T)) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ k : NonzeroLattice d,
      NegSobolev.fourierCoeff (etaE m (X t.toNNReal ω) (withDensityReal (ρ t))) k =
        NegSobolev.fourierCoeff (Vev t 0 (etaE m (X 0 ω) (withDensityReal (ρ 0)))) k +
          NegSobolev.fourierCoeff (Z t ω) k + evolvingForcingCoord htr.dyn ρ X k t ω := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hN0 : 0 < N := by omega
  -- the identity at all rational times and modes
  have hQ := ratIcc_countable 0 T
  have hQid : ∀ᵐ ω ∂P, ∀ t ∈ ratIcc 0 T, ∀ k : NonzeroLattice d,
      NegSobolev.fourierCoeff (etaE m (X t.toNNReal ω) (withDensityReal (ρ t))) k =
        NegSobolev.fourierCoeff (Vev t 0 (etaE m (X 0 ω) (withDensityReal (ρ 0)))) k +
          NegSobolev.fourierCoeff (Z t ω) k + evolvingForcingCoord htr.dyn ρ X k t ω := by
    rw [ae_ball_iff hQ]
    intro t ht
    rw [ae_all_iff]
    intro k
    exact adjke_identity_fixed hd htr hm T hT hN P hX hF M hMid Vev hV Z ht.1 (hZ t ht.1) (hZm t ht.1) k
  have hint := (adjk_forcing_intervalIntegrable_proof hd htr hN P X₀ W X T hT.le hX ⟨ℱ, W', hF⟩).1
  filter_upwards [hQid, hZc, hX.sol.cont, hX.sol.no_collision, hint] with ω hid hzc hxc hco hin
  intro t ht k
  obtain ⟨Lc, hLc⟩ := adjke_forcing_lipschitz hd htr hN0 T hT k (fun u => X u ω) hxc hco
    (fun t ht => hin t ht k)
  have cA := adjke_lhs_continuousOn hd htr hm T hN0 (fun u => X u ω) hxc k
  have cB := adjke_orbit_coord_continuousOn hd htr m T hT.le hV
    (etaE m (X 0 ω) (withDensityReal (ρ 0))) k
  have hcoord : Continuous fun F : NegSobolev d m => NegSobolev.fourierCoeff F k := by
    have : (fun F : NegSobolev d m => NegSobolev.fourierCoeff F k) =
        fun F => Lattice.jp k.1 ^ m * NegSobolev.coord F k := rfl
    rw [this]
    exact continuous_const.mul (adjk_continuous_coord m k)
  have cZ : ContinuousOn (fun t => NegSobolev.fourierCoeff (Z t ω) k) (Set.Icc 0 T) :=
    hcoord.comp_continuousOn hzc
  have cD : ContinuousOn (fun t => evolvingForcingCoord htr.dyn ρ X k t ω) (Set.Icc 0 T) :=
    adjke_continuousOn_of_lip (fun t => adjkeD htr.dyn ρ (fun u => X u ω) k t) T Lc hLc
  exact Set.EqOn.of_subset_closure (s := ratIcc 0 T) (t := Set.Icc 0 T)
    (f := fun t => NegSobolev.fourierCoeff (etaE m (X t.toNNReal ω) (withDensityReal (ρ t))) k)
    (g := fun t => NegSobolev.fourierCoeff (Vev t 0 (etaE m (X 0 ω) (withDensityReal (ρ 0)))) k +
          NegSobolev.fourierCoeff (Z t ω) k + evolvingForcingCoord htr.dyn ρ X k t ω)
    (fun t ht => hid t ht k) cA ((cB.add cZ).add cD) (fun t ht => ht.1)
    (adjke_Icc_subset_closure_rat hT.le) ht

example := (@adjk_mild_decomposition_proof : type_of% @HRS.AdjK.adjk_mild_decomposition)

end HRS.AdjK
