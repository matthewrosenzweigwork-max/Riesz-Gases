import HRS.MS.MovSchTie9

/-!
# S64 (row S6.11 `mov_translated_prepared`, `mov_translated_stationary`): PLAN, findings, and the proved reductions

Namespace `HRS.MS.MovSch`, prefix `s64_`.

## PLAN S6.11 (MovingDyn.lean ~:454, ~:520; TeX S L5189-5207)

Proof in the TeX: conjugate the complete particle system and both preparation laws by `x_i^t = y_i^t + b_t` (S6.8: clauses (1), (3), (4),
all proved, used in `MovSchAux6`-`MovSchAux10` for S6.9), apply S2.1(i) resp. S2.1(ii) at `ε = 0` (reference `μ_β`, both `still stated`, not proved)
to the untranslated process `Y = X - b_t`, and push forward the Gaussian comparators by the *exact field transformation*
(`W:r2mov:exact-field`, S L4971) whose norm is bounded by `(W:r2mov:translation-norm)`, `C_m(1+|a|)^m` (S L4982).

Proved here (conditional on the completion property of the stationary reference, i.e. on the first conjunct of S2.1(i)/(ii) at `ε = 0`):
* `s64_completion_translated`: the first conjunct of both rows (`0 ≤ F_N(X, ρ^t) + o_N` for the translate `ρ^t`) from the same property of `ρ_β`
  (S6.8(4): `F_N(X, T_aμ) = F_N(X - a, μ)`).

NOT provable with the present library (STOP report):
1. The exact field transformation is a statement about the dual spaces `B_m = OscDual d m` that is not in the project: the translation operator
   `Λ_b : B_m → B_m` (dual of `φ ↦ φ(· + b)` on `Σ^m`), its boundedness `‖Λ_b‖ ≤ C_m(1+|b|)^m` (Hermite-coefficient norm `Σ^m` versus
   translations; no translation/Weyl operator exists in `HRS/Whole/Oscillator.lean`, `MovOsc*`), its strong continuity in `b` (needed so that
   `t ↦ Λ_{b_t} y_t` is again a path in `C([0,T]; B_m)`), and `ζ_X^t = Λ_{b_t} ζ_Y^t` (`zetaB` is defined through `meanEmpirical (law X_t)`,
   which has to be translated as well).  Estimate 1.5-2.5k lines.
2. The transfer of the two path distances needs the induced (time-dependent) continuous linear map on `C([0,T]; B_m)` and
   `smoothDist_map_clm_le`, `wassersteinE_map_clm_le` (`HRS/Main/Headline.lean`); about 500 lines once 1. exists.
3. The Gaussian comparator: `IsLinearGaussianEvolutionW P' (coeff ρ^·) .. (susceptibilityCov (ρ^0) γ) Z` must be turned into the stationary
   `IsLinearGaussianEvolutionW P'' (coeff (fun _ => ρ_β))` for `Λ_{-b_t} Z_t`.  This is conjugation of the classical adjoint propagator
   `propagatorW` and of `noiseCovW` by translation (uniqueness of classical adjoint solutions, S5.x F-CAU, and the drift term `q a_t`);
   no such lemma exists.  Estimate 1k+ lines.
4. S2.1(i)/(ii) are `stated` (unproved) in `Headline.lean`; any reduction is conditional on `h21 : type_of% @HRS.Whole.whole_space_stationary` resp.
   `whole_space_prepared`.  For (ii) one also needs `IsResultingSolution` for the constant solution `ρ_β` (`IsWholeMeanFieldSolution` of the
   stationary density), not in the project.
Total honest estimate for the two rows: 4-6k lines, beyond the 5k stop rule of this packet together with S6.4 and S6.9.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MovSch

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

/-- First conjunct of `mov_translated_prepared` / `mov_translated_stationary`: the completion property is invariant under translation. -/
theorem s64_completion_translated {s q : ℝ} {C₀ : ℝ} {ρ₀ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ₀) (b : Euc d)
    (hc : ∀ N : ℕ, 2 ≤ N → ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
      0 ≤ rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ρ₀) + oN d s C₀ N) :
    ∀ N : ℕ, 2 ≤ N → ∀ t : ℝ, ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
      0 ≤ rieszModulatedEnergy d s X (HRS.Whole.withDensityReal (movTranslatedDensity q b ρ₀ t)) + oN d s C₀ N := by
  intro N hN t X hX
  have e : movTranslatedDensity q b ρ₀ t = fun x => ρ₀ (x - movShift q b t) := rfl
  have h1 : s64_NC X := s64_NC_of_not_mem hX
  have hX' : (fun i => X i - movShift q b t) ∉ eucCollisionSet d N := by
    refine s64_not_mem_of_NC fun i j hij h => h1 i j hij ?_
    exact sub_left_inj.1 h
  have := hc N hN _ hX'
  rw [e, s64_withDensityReal_translate]
  have h2 := movtr_modulatedEnergy_translate (rieszKernel d s) (HRS.Whole.withDensityReal ρ₀) (movShift q b t)
    (fun i => X i - movShift q b t)
  simp only [sub_add_cancel] at h2
  unfold rieszModulatedEnergy at this ⊢
  rw [h2]
  exact this

end HRS.MS.MovSch

end
