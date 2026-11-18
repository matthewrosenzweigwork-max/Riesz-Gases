import HRS.ME.UIPath
import HRS.Main.A9Aux29

/-!
# Packet SQ2: `tendstoInDistribution_of_smoothDist`

Proof of the convergence-in-law criterion from `smoothDist 2`-closeness to a weakly converging sequence of
probability measures (statement frozen in `HRS/ME/UIPathShiftedSpec.lean`, where it is still `unproved`).
Route: `HRS.Main.A9.a9_fd_converges` with `T = id` gives convergence of `∫ f` for every bounded continuous `f`,
and `tendstoInDistribution_iff_forall_integral_rclike_tendsto` turns this into `TendstoInDistribution`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace HRS.ME.UIPathShifted

open HRS HRS.Main

variable {d : ℕ}

/-- **Q2** (from `smoothDist 2 → 0` to convergence in law on `ℝ^p`; scope note Q2).  Generalised form, so that
`ui_path_initial` can reuse it: if `μ_n = law (Y n)` is `smoothDist 2`-close to probability measures `Λ_n`
(distance `→ 0`) and `Λ_n ⇒ law Z` weakly (tested against bounded continuous functions), then `Y_n → Z` in
distribution.  Fixed limit (Q1): `Λ_n = law Z` constant, hypothesis `hΛ` is `tendsto_const_nhds`.  Every
`Φ ∈ C_b^2` is a multiple of an element of the `C_b^2` unit ball, so `∫Φ dμ_n - ∫Φ dλ_0 → 0` for `Φ ∈ C_b^2`, and
`C_b^2` is convergence determining on `ℝ^p`.  Route: `a9_fd_converges` (`HRS/Main/A9Aux29.lean`, `T = id`)
and the `ProbabilityMeasure` criterion for `TendstoInDistribution`. -/
theorem tendstoInDistribution_of_smoothDist {p : ℕ}
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] (Y : ∀ n, Ω n → EuclideanSpace ℝ (Fin p))
    (hY : ∀ n, AEMeasurable (Y n) (P n))
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Z : Ω' → EuclideanSpace ℝ (Fin p)) (hZ : AEMeasurable Z P')
    (Λ : ℕ → Measure (EuclideanSpace ℝ (Fin p))) [∀ n, IsProbabilityMeasure (Λ n)]
    (hΛ : ∀ f : BoundedContinuousFunction (EuclideanSpace ℝ (Fin p)) ℝ,
      Tendsto (fun n => ∫ x, f x ∂(Λ n)) atTop (𝓝 (∫ ω, f (Z ω) ∂P')))
    (hd : Tendsto (fun n => smoothDist 2 (law (P n) (Y n)) (Λ n)) atTop (𝓝 0)) :
    TendstoInDistribution Y atTop Z P P' := by
  have hlc : ConvergesInLaw Λ (P'.map Z) := by
    unfold ConvergesInLaw
    intro f
    rw [integral_map hZ f.continuous.aestronglyMeasurable]
    exact hΛ f
  have key := A9.a9_fd_converges (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin p)))
    (fun n => (P n).map (Y n)) Λ (P'.map Z) hlc hd
  refine (tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ hY hZ).mpr ?_
  intro f
  have hmap : ∀ n, ∫ ω, f (Y n ω) ∂(P n) = ∫ x, f x ∂((P n).map (Y n)) := fun n =>
    (integral_map (hY n) f.continuous.aestronglyMeasurable).symm
  have hlim : ∫ ω, f (Z ω) ∂P' = ∫ x, f x ∂(P'.map Z) :=
    (integral_map hZ f.continuous.aestronglyMeasurable).symm
  rw [hlim]
  simp only [hmap]
  exact key f

end HRS.ME.UIPathShifted
