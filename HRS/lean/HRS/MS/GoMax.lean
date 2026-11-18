import HRS.MS.GoFeatTie
import HRS.MS.SuppU9

/-!
# S5.5 maximal estimate (conditional on `t`-measurability)

`s55f_orbit_maximal_const`: the body of `HRS.MS.U9.orbit_maximal_proof` with the constants made explicit
(`Ctr = 2 n B²`, `Cmax = (3 + √T)² C_BDG`, independent of the coefficients `C`), so that they are uniform in `S, N`.
`s55f_maximal_of_meas`: `OrbitMaximalConclusion` for `gradFeature (S.coeff N)`, constants independent of `S, N`, for every
`S` with `S55fMeas b S` (`GoFeatTie.lean`), from `s55f_features_of_meas` (bound `j = 0`, measurability from continuity).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.Go

open HRS HRS.Whole HRS.MS.U9

variable {d : ℕ}

theorem s55f_orbit_maximal_const (m T : ℝ) (hT : 0 ≤ T) (n : ℕ) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ (C : WholeCoeff d) (Dop : Fin n → (Euc d → ℝ) → Euc d → ℝ) (B : ℝ),
      (∀ a : Fin n, ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x : Euc d, ‖orbitFeature C m T (Dop a) r x‖ ≤ B) →
      (∀ a : Fin n, ∀ r ∈ Set.Icc (0 : ℝ) T,
        Measurable (fun x : Euc d => orbitFeature C m T (Dop a) r x)) →
      OrbitMaximalConclusion m T
        (fun (a : Fin n) (r : ℝ) (x : Euc d) => orbitFeature C m T (Dop a) r x)
        (2 * n * B ^ 2) ((3 + Real.sqrt T) ^ 2 * C₂) := by
  obtain ⟨C₂, hC₂, hbdg⟩ := HRS.HilbertBDG.hilbert_bdg 2 le_rfl
  refine ⟨C₂, hC₂, fun C Dop B hB hmeas => ⟨?_, ?_⟩⟩
  · intro q hq r hr ν hν
    haveI := hν
    obtain ⟨Bf, h1, h2, h3⟩ := u9_exists_form (ν := ν)
      (Γ := fun a => orbitFeature C m T (Dop a) r) hq (fun a => hmeas a r hr)
      (fun a x => hB a r hr x)
    exact ⟨Bf, h1, h2, h3⟩
  · intro Ω mΩ P hP ℱ M Sg hM
    refine ⟨?_, ?_⟩
    · filter_upwards [hM.cont] with ζ hζ
      exact u9_continuous_recon hT M ζ hζ
    · exact u9_bound hT hM C₂ hC₂ (hbdg Ω P ℱ (KSpace d m T) T M Sg hM)

theorem s55f_maximal_of_meas (b : WholeBounds d) (hb : b.Valid) :
    ∃ Ctr Cmax : ℝ, ∀ S : WholeSetup b, S55fMeas b S → ∀ N : ℕ, OrbitMaximalConclusion b.m b.T
      (fun (a : Fin d) (r : ℝ) (x : Euc d) => gradFeature (S.coeff N) b.m b.T a r x) Ctr Cmax := by
  obtain ⟨C, hC⟩ := s55f_features_of_meas b hb
  obtain ⟨C₂, hC₂, hmax⟩ := s55f_orbit_maximal_const (d := d) b.m b.T hb.hT.le d
  refine ⟨2 * d * C ^ 2, (3 + Real.sqrt b.T) ^ 2 * C₂, fun S hS N => ?_⟩
  refine hmax (S.coeff N) (fun a => gradComp a) C ?_ ?_
  · intro a r hr x
    have := (hC S hS N a r hr).2 0 (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero] at this
  · intro a r hr
    exact (hC S hS N a r hr).1.continuous.measurable

end HRS.MS.Go
