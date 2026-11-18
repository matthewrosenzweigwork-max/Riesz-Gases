import HRS.MC.S7PIF5A

/-!
# Packet piF5, part B: progressive measurability of the centred field `(r, ω) ↦ ℬ_N^r(ω)` and of the drift `b`

`S7PIF5_Q r ω = Ψ(r, X_r ω) - ∫ Ψ(r, X_r ω') dP` (the form of `quadFieldAt` for `r ≥ 0`, `S7PIM_B_eq`) is progressive for
the filtration of a progressive `X` (`Ψ` is jointly Borel, `S7PIM_Psi_meas`; the mean is a Borel function of `r`, as a pointwise
limit of integrals of the jointly measurable `Ψ(r, X_{r ∧ n})`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIF5

open HRS HRS.PDE HRS.A33 HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIF4 HRS.MC.Sec7.S7PIM

variable {d : ℕ}

/-- the centred field in its jointly measurable form -/
def S7PIF5_Q (R : Regime d) (m : ℝ) {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → Config d N) (r : ℝ) (ω : Ω) : NegSobolev d m :=
  S7PIM_Psi R m r (X r.toNNReal ω) - ∫ ω', S7PIM_Psi R m r (X r.toNNReal ω') ∂P

theorem S7PIF5_Q_eq (R : Regime d) (m : ℝ) {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → Config d N) {r : ℝ} (hr : 0 ≤ r) (ω : Ω) :
    quadFieldAt m R.D.s (fun t => withDensityReal (R.ρ t)) P X r ω = S7PIF5_Q R m P X r ω :=
  S7PIM_B_eq R m P X hr ω

section Prog

variable (R : Regime d) (m : ℝ) {N : ℕ} {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  {X : ℝ≥0 → Ω → Config d N} {ℱ : Filtration ℝ mΩ}

/-- the mean `r ↦ ∫ Ψ(r, X_r ω') dP` is Borel -/
theorem S7PIF5_mean_meas (hX : IsProgressive ℱ (ofNNRealTime X)) :
    Measurable fun r : ℝ => ∫ ω', S7PIM_Psi R m r (X r.toNNReal ω') ∂P := by
  have hn : ∀ n : ℕ, Measurable fun r : ℝ => ∫ ω', S7PIM_Psi R m r (X (min r n).toNNReal ω') ∂P := by
    intro n
    have h1 := measurable_progressive_min_gen hX (n : ℝ)
    have h2 : Measurable fun q : ℝ × Ω => ((q.1, ofNNRealTime X (min q.1 n) q.2) : ℝ × Config d N) :=
      measurable_fst.prodMk h1
    have h3 : Measurable fun q : ℝ × Ω => S7PIM_Psi R m q.1 (X (min q.1 n).toNNReal q.2) :=
      Measurable.comp (g := fun q : ℝ × Config d N => S7PIM_Psi R m q.1 q.2)
        (f := fun q : ℝ × Ω => ((q.1, ofNNRealTime X (min q.1 n) q.2) : ℝ × Config d N))
        (S7PIM_Psi_meas R m) h2
    exact (h3.stronglyMeasurable.integral_prod_right' (ν := P)).measurable
  refine measurable_of_tendsto_metrizable hn (tendsto_pi_nhds.2 fun r => ?_)
  refine tendsto_nhds_of_eventually_eq ?_
  filter_upwards [eventually_ge_atTop ⌈r⌉₊] with n hn'
  have : min r (n : ℝ) = r := min_eq_left ((Nat.le_ceil r).trans (by exact_mod_cast hn'))
  simp only [this]

theorem S7PIF5_Q_prog (hX : IsProgressive ℱ (ofNNRealTime X)) : IsProgressive ℱ (S7PIF5_Q R m P X) := by
  intro s
  have hm := S7PIF5_mean_meas R m P hX
  have h1 : Measurable[Subtype.instMeasurableSpace.prod (ℱ s)]
      fun p : Set.Iic s × Ω => S7PIM_Psi R m (p.1 : ℝ) (X (p.1 : ℝ).toNNReal p.2) := by
    have hp : Measurable[Subtype.instMeasurableSpace.prod (ℱ s)]
        fun p : Set.Iic s × Ω => ((p.1 : ℝ), ofNNRealTime X (p.1 : ℝ) p.2) :=
      Measurable.prodMk (measurable_subtype_coe.comp (@measurable_fst _ _ Subtype.instMeasurableSpace (ℱ s))) (hX s)
    exact Measurable.comp (g := fun q : ℝ × Config d N => S7PIM_Psi R m q.1 q.2)
      (f := fun p : Set.Iic s × Ω => ((p.1 : ℝ), ofNNRealTime X (p.1 : ℝ) p.2)) (S7PIM_Psi_meas R m) hp
  have h2 : Measurable[Subtype.instMeasurableSpace.prod (ℱ s)]
      fun p : Set.Iic s × Ω => ∫ ω', S7PIM_Psi R m (p.1 : ℝ) (X (p.1 : ℝ).toNNReal ω') ∂P :=
    hm.comp (measurable_subtype_coe.comp (@measurable_fst _ _ Subtype.instMeasurableSpace (ℱ s)))
  exact h1.sub h2

end Prog

end HRS.MC.Sec7.S7PIF5

end
