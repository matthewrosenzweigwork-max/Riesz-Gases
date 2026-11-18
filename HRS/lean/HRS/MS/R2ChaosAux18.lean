import HRS.MS.R2ChaosAux17
import HRS.MS.R2MtAux3

/-!
# HRS.MS.R2ChaosAux18 -- uniform-in-time moment bounds from S9.2 along the time marginals

Packet S94, namespace `HRS.MS.R2Chaos`, helper prefix `s94_`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.haveILetI false
set_option linter.deprecated false

open MeasureTheory ProbabilityTheory Function Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace HRS.MS.R2Chaos

open HRS.Whole

variable {d : ℕ}

section Moments

variable {s T b p K M L : ℝ} {ρ : Euc d → ℝ} {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)]
  {P : ∀ N, Measure (Ω N)} [∀ N, IsProbabilityMeasure (P N)] {X : ∀ N, ℝ≥0 → Ω N → EucConfig d N}
  {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {ξ : (Euc d → ℝ) → Ω' → C(Set.Icc (0 : ℝ) T, ℝ)}

theorem s94_empFluct_measurable_config {μ : Measure (Euc d)} {N : ℕ} (a : Euc d → ℝ) (ha : Measurable a) :
    Measurable fun Y : EucConfig d N => Real.sqrt N * (Whole.pair (Whole.empirical Y) a - Whole.pair μ a) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    simp only [Nat.cast_zero, Real.sqrt_zero, zero_mul]
    exact measurable_const
  · simp_rw [Whole.pair_empirical hN]
    refine measurable_const.mul ((measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_)).sub measurable_const)
    exact ha.comp (measurable_pi_apply i)

/-- Uniform `L^r` bound for the empirical fluctuations along the time marginals. -/
theorem s94_linear_moment (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (hb : 0 < b) (hp : 1 < p)
    (hρ : IsRound2Density d s M L ρ)
    (hset : IsRound2PathSetting d s T b p K (Whole.withDensityReal ρ) P X P' ξ) {r : ℝ} (hr : 1 ≤ r) :
    ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (a : Euc d → ℝ) (A : ℝ), Measurable a →
      (∀ x, |a x| ≤ A) →
      eLpNorm (fun ζ => r2EmpFluct (Whole.withDensityReal ρ) a (X N) ζ t) (ENNReal.ofReal r) (P N) ≤
        ENNReal.ofReal (C * A) := by
  obtain ⟨C, hC⟩ := HRS.MS.R2Mt.round2_moment_transfer_proof hd s hs0 hs M L b p K 0 hb hp r hr
  refine ⟨C, fun N hN t ht a A ha hA => ?_⟩
  have hmeas : ∀ N' : ℕ, ∀ t' : ℝ≥0, Measurable (X N' t') := fun N' t' =>
    (hset.measX N').comp measurable_prodMk_left
  have hden := hset.density N hN t ht
  have hL := (hC ρ hρ (fun N' => (P N').map (X N' t.toNNReal)) (fun N' hN' => hset.density N' hN' t ht)).2.1
    0 N hN a A ha hA
  have hmX : Measurable (X N t.toNNReal) := hmeas N _
  have hgm := s94_empFluct_measurable_config (μ := Whole.withDensityReal ρ) (N := N) a ha
  have e : eLpNorm (fun X' : EucConfig d N => Real.sqrt N * (Whole.pair (Whole.empirical X') a -
      Whole.pair (Whole.withDensityReal ρ) a)) (ENNReal.ofReal r) ((P N).map (X N t.toNNReal)) =
      eLpNorm (fun ζ => r2EmpFluct (Whole.withDensityReal ρ) a (X N) ζ t) (ENNReal.ofReal r) (P N) := by
    rw [eLpNorm_map_measure hgm.aestronglyMeasurable hmX.aemeasurable]
    rfl
  rw [← e]
  exact hL

end Moments

end HRS.MS.R2Chaos
