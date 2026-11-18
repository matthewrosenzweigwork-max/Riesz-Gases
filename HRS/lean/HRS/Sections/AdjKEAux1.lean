import HRS.Sections.AdjKAAux7
import HRS.Sections.AdjKCFinal
import HRS.Sections.DynCmpAux1

/-!
# ADJKE part 1: adjoint data along a trajectory, regularity of the propagator, continuity of dual orbits

* `adjke_adjData`: `AdjointData` for the density path `ρ` itself (all horizons `T > 0`) at the level `J = j + 5`.
* `adjke_prop_dom`: for smooth `φ` and `0 ≤ u ≤ t`, `U^{u,t}φ` is continuous and lies in `H^j`.
* `adjke_orbit_continuousOn`: for every dual evolution `Vev` (no continuity hypothesis), `t ↦ Vev t 0 z` is continuous on `[0,T]`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.AdjK

open HRS HRS.PDE HRS.PDE.ET HRS.Uniform HRS.Uniform.Q54

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

/-- `AdjointData` for the trajectory `ρ` itself at level `J = j + 5`, for every horizon. -/
theorem adjke_adjData (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (j : ℕ)
    (hj : (d : ℝ) + 2 ≤ j) :
    ∃ (R : Regime) (Λ : ℝ), ∀ T : ℝ, 0 < T →
      AdjointData s (j + 5) R 1 Λ (Torus.cbNorm (j + 5 + 3) V) htr.dyn β⁻¹ T ρ := by
  have hd1 : 1 ≤ d := by omega
  set J : ℕ := j + 5 with hJ
  have hJr : (J : ℝ) = j + 5 := by rw [hJ]; push_cast; ring
  have hdd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  set K : ℕ := 2 * J + 4 * d + 20 with hKdef
  have hKr : (K : ℝ) = 2 * J + 4 * d + 20 := by rw [hKdef]; push_cast; ring
  have hKgt : (d : ℝ) / 2 + 6 < K := by rw [hKr, hJr]; linarith
  have hKJ : 2 * J + 4 * d + 20 ≤ K := le_rfl
  have hJd : (d : ℝ) / 2 + 4 < J := by rw [hJr]; linarith
  have hβI : β ∈ Set.Icc β β := ⟨le_rfl, le_rfl⟩
  have H := Q40b.q40b_finiteRegHyp htr hKgt
  obtain ⟨ρc, hρc, hρ⟩ := htr.global K hKgt
  obtain ⟨ρβ, hρβ, hρC, hpos, -⟩ := finite_reg_thermal hd1 s β β K V ρ₀ H β hβI
  obtain ⟨R, Λ, Λ₀, c₀, Cd, κ, hc₀, hκ, hall⟩ :=
    MFAdjoint.finiteReg_hypotheses hd1 s β β K V ρ₀ H J hJd hKJ
  obtain ⟨-, hAD, -⟩ := hall β hβI ρc hρc ρβ hρβ hρC hpos
  refine ⟨R, Λ, fun T hT => ?_⟩
  have hag : ∀ r ∈ Set.Icc (0 : ℝ) T, ρ r = PDE.mfPath ρc r := fun r hr => (hρ r hr.1).symm
  exact dyncmp_adjointData_congr (hAD T hT) hag

theorem adjke_mStar_le (d : ℕ) (j : ℕ) (hj : (d : ℝ) + 2 ≤ j) : mStar d ≤ j + 5 := by
  have h1 := Q54.mStar_le_aux d
  have hdd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have : (mStar d : ℝ) ≤ ((j + 5 : ℕ) : ℝ) := by push_cast; linarith
  exact_mod_cast this

/-- For smooth `φ` and `0 ≤ u ≤ t`, `U^{u,t}φ` is continuous and lies in `H^{j+5}`. -/
theorem adjke_prop_dom (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (j : ℕ)
    (hj : (d : ℝ) + 2 ≤ j) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) {u t : ℝ} (hu : 0 ≤ u)
    (hut : u ≤ t) :
    Continuous (propagator htr.dyn ρ u t φ) ∧ MemSobolev ((j : ℝ) + 5) (propagator htr.dyn ρ u t φ) := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨R, Λ, hA⟩ := adjke_adjData hd htr j hj
  have hJm := adjke_mStar_le d j hj
  have hD : Dom (j + 5) φ := dom_smooth hφ
  have hJr : (((j + 5 : ℕ)) : ℝ) = j + 5 := by push_cast; ring
  rcases hut.eq_or_lt with h0 | hlt
  · subst h0
    have hself : propagator htr.dyn ρ u u φ = φ := by
      rcases hu.eq_or_lt with h00 | hpos
      · rw [← h00]
        exact prop_self_zero hd1 s htr.hs0 htr.hsd (j + 5) R 1 Λ _ htr.dyn β⁻¹ 1 _ (hA 1 one_pos) hφ
      · exact prop_self_pos hd1 s htr.hs0 htr.hsd (j + 5) hJm R 1 Λ _ htr.dyn β⁻¹ u _ (hA u hpos)
          ⟨hpos, le_rfl⟩ hD
    rw [hself]
    exact ⟨hD.1, by rw [← hJr]; exact hD.2⟩
  · have ht0 : 0 < t := lt_of_le_of_lt hu hlt
    have hdom := prop_dom hd1 s htr.hs0 htr.hsd (j + 5) hJm R 1 Λ _ htr.dyn β⁻¹ t ρ
      (hA t ht0) ⟨ht0, le_rfl⟩ hD ⟨hu, hut⟩
    exact ⟨hdom.1, by rw [← hJr]; exact hdom.2⟩

/-- Every dual evolution has continuous orbits `t ↦ V^{t,0} z` on `[0,T]`: it coincides with the plain one by
uniqueness of the duality. -/
theorem adjke_orbit_continuousOn (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (m : ℝ)
    (T : ℝ) (hT : 0 ≤ T) {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m}
    (hV : IsDualEvolution htr.dyn ρ m Vev) (z : NegSobolev d m) :
    ContinuousOn (fun t => Vev t 0 z) (Set.Icc 0 T) := by
  obtain ⟨Cr, cr, -, -, V', hdual', hplain, -, -⟩ := adjk_evolution_along_trajectory hd htr m
  have h1 : ∀ t ∈ Set.Icc (0 : ℝ) T, Vev t 0 = V' t 0 := fun t ht =>
    adjka_dual_unique hV hdual' le_rfl ht.1
  have h2 := (hplain T hT).2.2 z
  have h3 : ContinuousOn (fun t : ℝ => V' t 0 z) (Set.Icc 0 T) := by
    have hmap : ContinuousOn (fun t : ℝ => (t, (0 : ℝ))) (Set.Icc 0 T) := by fun_prop
    exact h2.comp hmap fun t ht => ⟨le_rfl, ht.1, ht.2⟩
  exact h3.congr fun t ht => by rw [h1 t ht]

/-- The coordinates of the dual orbit are continuous in `t`. -/
theorem adjke_orbit_coord_continuousOn (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    (m : ℝ) (T : ℝ) (hT : 0 ≤ T) {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m}
    (hV : IsDualEvolution htr.dyn ρ m Vev) (z : NegSobolev d m) (k : NonzeroLattice d) :
    ContinuousOn (fun t => NegSobolev.fourierCoeff (Vev t 0 z) k) (Set.Icc 0 T) := by
  have hc : Continuous fun F : NegSobolev d m => NegSobolev.fourierCoeff F k := by
    have : (fun F : NegSobolev d m => NegSobolev.fourierCoeff F k) =
        fun F => Lattice.jp k.1 ^ m * NegSobolev.coord F k := rfl
    rw [this]
    exact continuous_const.mul (adjk_continuous_coord m k)
  exact hc.comp_continuousOn (adjke_orbit_continuousOn hd htr m T hT hV z)

end HRS.AdjK
