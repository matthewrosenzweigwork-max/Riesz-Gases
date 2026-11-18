import HRS.MC.S7PIF5B

/-!
# Packet piF5, part C: the drift `b` is progressive and pathwise locally integrable

`S7PIF5_b` is the explicit drift of the statement; it equals `-(√N)⁻¹ g_i(r, Q_r ω)` (parts A, B), hence is progressive,
and a.s. locally integrable by the `L¹(0,T; E_m)` bound of `ℬ_N` (M1) together with `|g| ≤ C ‖F‖`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIF5

open HRS HRS.PDE HRS.A33 HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIF4 HRS.MC.Sec7.S7PIM

variable {d : ℕ}

/-- sections of a progressive process are measurable (clamped at `T'`) -/
theorem S7PIF5_sec_meas {Ω : Type} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ mΩ} {β : Type*} [MeasurableSpace β]
    {u : ℝ → Ω → β} (hu : IsProgressive ℱ u) (ω : Ω) (T' : ℝ) :
    Measurable fun s : ℝ => u (min s T') ω :=
  (measurable_progressive_min_gen hu T').comp (measurable_id.prodMk measurable_const)

theorem S7PIF5_sec_aemeas {Ω : Type} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ mΩ} {β : Type*} [MeasurableSpace β]
    {u : ℝ → Ω → β} (hu : IsProgressive ℱ u) (ω : Ω) (T' : ℝ) :
    AEMeasurable (fun s : ℝ => u s ω) (volume.restrict (Set.Icc 0 T')) := by
  refine (S7PIF5_sec_meas hu ω T').aemeasurable.congr ?_
  exact (ae_restrict_iff' measurableSet_Icc).2 (ae_of_all _ fun s hs => by
    show u (min s T') ω = u s ω
    rw [min_eq_left hs.2])

/-- the drift of the observation vector -/
def S7PIF5_b (R : Regime d) (m : ℝ) {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → Config d N) {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ) :
    ℝ → Ω → EuclideanSpace ℝ (Fin q) :=
  fun r ω => WithLp.toLp 2 fun i => if 0 ≤ r then -(Real.sqrt N)⁻¹ * NegSobolev.eval
    (quadFieldAt m R.D.s (fun s => withDensityReal (R.ρ s)) P X r ω) (obsTest R.D R.ρ t φ i r) else 0

theorem S7PIF5_b_apply (R : Regime d) (m : ℝ) {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → Config d N) {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ) (r : ℝ) (ω : Ω) (i : Fin q) :
    S7PIF5_b R m P X t φ r ω i = -(Real.sqrt N)⁻¹ * S7PIF5_g R.D R.ρ t φ i (r, S7PIF5_Q R m P X r ω) := by
  show (if 0 ≤ r then -(Real.sqrt N)⁻¹ * NegSobolev.eval
    (quadFieldAt m R.D.s (fun s => withDensityReal (R.ρ s)) P X r ω) (obsTest R.D R.ρ t φ i r) else 0) = _
  by_cases hr : 0 ≤ r
  · rw [if_pos hr, S7PIF5_g_pos _ _ _ _ _ hr, S7PIF5_Q_eq R m P X hr]
  · rw [if_neg hr, S7PIF5_g_neg _ _ _ _ _ hr, mul_zero]

section Prob

variable (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) (N : ℕ) (hN : 1 ≤ N)
  {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
  (hreal : PreparedRealization R.D P
    (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) X₀ W X)

include hm hT hN hreal

theorem S7PIF5_b_prog {ℱ : Filtration ℝ mΩ} (hX : IsProgressive ℱ (ofNNRealTime X)) {q : ℕ} (t : Fin q → ℝ)
    (φ : Fin q → Torus d → ℝ) (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T) (hφ : ∀ i, Torus.IsSmooth (φ i)) :
    IsProgressive ℱ (S7PIF5_b R m P X t φ) := by
  intro s
  have hQ := S7PIF5_Q_prog R m P hX s
  have hpr : Measurable[Subtype.instMeasurableSpace.prod (ℱ s)]
      fun p : Set.Iic s × Ω => (((p.1 : ℝ), S7PIF5_Q R m P X (p.1 : ℝ) p.2) : ℝ × NegSobolev d m) :=
    Measurable.prodMk (measurable_subtype_coe.comp (@measurable_fst _ _ Subtype.instMeasurableSpace (ℱ s))) hQ
  have hco : Measurable[Subtype.instMeasurableSpace.prod (ℱ s)]
      fun p : Set.Iic s × Ω => (WithLp.toLp 2 (fun i => -(Real.sqrt N)⁻¹ *
        S7PIF5_g R.D R.ρ t φ i (((p.1 : ℝ), S7PIF5_Q R m P X (p.1 : ℝ) p.2))) :
        EuclideanSpace ℝ (Fin q)) := by
    refine @Measurable.comp _ _ _ (Subtype.instMeasurableSpace.prod (ℱ s)) _ _ _ _
      (MeasurableEquiv.toLp 2 (Fin q → ℝ)).measurable
      (@measurable_pi_iff _ _ _ (Subtype.instMeasurableSpace.prod (ℱ s)) _ _ |>.2 fun i => ?_)
    exact ((S7PIF5_g_meas R m hm T hT N hN P X₀ W X hreal t φ ht hφ i).comp hpr).const_mul _
  convert hco using 1
  funext p
  ext i
  exact S7PIF5_b_apply R m P X t φ p.1 p.2 i

theorem S7PIF5_b_int {ℱ : Filtration ℝ mΩ} (hX : IsProgressive ℱ (ofNNRealTime X)) {q : ℕ} (t : Fin q → ℝ)
    (φ : Fin q → Torus d → ℝ) (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T) (hφ : ∀ i, Torus.IsSmooth (φ i)) (T' : ℝ) :
    ∀ᵐ ω ∂P, IntegrableOn (fun s => S7PIF5_b R m P X t φ s ω) (Set.Icc 0 T') := by
  have hM1 := (HRS.MC.Sec7.S7PIM.s7_PIM_B_integrable_proof R m hm T hT N hN P X₀ W X hreal).1
  have hprog := S7PIF5_b_prog R m hm T hT N hN P X₀ W X hreal hX t φ ht hφ
  filter_upwards [hM1] with ω hω
  have hint : Integrable (fun u => quadFieldAt m R.D.s (fun t => withDensityReal (R.ρ t)) P X u ω)
      (volume.restrict (Set.Icc (0 : ℝ) T)) := hω.integrable le_rfl
  have hcoord : ∀ i, Integrable (fun s => S7PIF5_b R m P X t φ s ω i) (volume.restrict (Set.Icc 0 T')) := by
    intro i
    obtain ⟨C, hC0, hC⟩ := S7PIF5_g_bound R m hm T hT N hN P X₀ W X hreal t φ ht hφ i
    set c : ℝ := (Real.sqrt N)⁻¹ * C with hc
    have hh : Integrable (Set.indicator (Set.Icc (0 : ℝ) T)
        (fun u => c * ‖quadFieldAt m R.D.s (fun t => withDensityReal (R.ρ t)) P X u ω‖)) volume :=
      (integrable_indicator_iff measurableSet_Icc).2 (by
        rw [IntegrableOn]; exact hint.norm.const_mul c)
    have hmeas : AEStronglyMeasurable (fun s => S7PIF5_b R m P X t φ s ω i)
        (volume.restrict (Set.Icc 0 T')) := by
      have h1 : AEMeasurable (fun s => S7PIF5_b R m P X t φ s ω) (volume.restrict (Set.Icc 0 T')) :=
        S7PIF5_sec_aemeas hprog ω T'
      exact ((EuclideanSpace.proj i : EuclideanSpace ℝ (Fin q) →L[ℝ] ℝ).continuous.measurable.comp_aemeasurable
        h1).aestronglyMeasurable
    refine Integrable.mono' hh.restrict hmeas ?_
    have h0 : ∀ᵐ s ∂(volume : Measure ℝ), s ∉ ({0} : Set ℝ) := (Set.countable_singleton (0 : ℝ)).ae_notMem _
    filter_upwards [ae_restrict_of_ae h0, ae_restrict_mem measurableSet_Icc] with s hs0 hs
    have hspos : 0 < s := lt_of_le_of_ne hs.1 (fun h => hs0 (by simp [h]))
    rw [S7PIF5_b_apply, Real.norm_eq_abs, abs_mul, abs_neg]
    by_cases hsT : s ≤ T
    · rw [Set.indicator_of_mem (show s ∈ Set.Icc (0 : ℝ) T from ⟨hs.1, hsT⟩)]
      have hQeq : ‖S7PIF5_Q R m P X s ω‖ =
          ‖quadFieldAt m R.D.s (fun t => withDensityReal (R.ρ t)) P X s ω‖ := by
        rw [S7PIF5_Q_eq R m P X hs.1 ω]
      have hb := hC s (S7PIF5_Q R m P X s ω) hspos
      rw [abs_inv, abs_of_nonneg (Real.sqrt_nonneg _)]
      calc (Real.sqrt N)⁻¹ * |S7PIF5_g R.D R.ρ t φ i (s, S7PIF5_Q R m P X s ω)|
          ≤ (Real.sqrt N)⁻¹ * (C * ‖S7PIF5_Q R m P X s ω‖) :=
            mul_le_mul_of_nonneg_left hb (inv_nonneg.2 (Real.sqrt_nonneg _))
        _ = c * ‖quadFieldAt m R.D.s (fun t => withDensityReal (R.ρ t)) P X s ω‖ := by
            rw [hQeq, hc]; ring
    · rw [Set.indicator_of_notMem (show s ∉ Set.Icc (0 : ℝ) T from fun h => hsT h.2)]
      have : S7PIF5_g R.D R.ρ t φ i (s, S7PIF5_Q R m P X s ω) = 0 :=
        S7PIF5_g_gt R.D R.ρ t φ i (lt_of_le_of_lt (ht i).2 (not_le.1 hsT)) _
      rw [this]; simp
  have := (integrable_pi_iff (f := fun s => (S7PIF5_b R m P X t φ s ω).ofLp)).2 hcoord
  exact (EuclideanSpace.equiv (Fin q) ℝ).symm.integrable_comp_iff.2 this

end Prob

end HRS.MC.Sec7.S7PIF5

end
