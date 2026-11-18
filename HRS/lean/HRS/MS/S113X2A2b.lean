import HRS.MS.S113X2A2a

/-!
# S11.3 X2 part A2b: continuity in time of the pairing of the killed law with a test function supported in `D`
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S113X2

open HRS HRS.Whole

variable {d N : ℕ}

/-- Pathwise: a continuous path stopped (killed) at the exit time `T0`, paired with a function vanishing off `D`. -/
theorem s113a_killed_path_continuous {E : Type*} [TopologicalSpace E] (T0 : WithTop ℝ) (g : ℝ → E)
    (hg : Continuous g) (ψ : E → ℝ) (hψ : Continuous ψ) (c0 : ℝ)
    (hT0 : ∀ c : ℝ, T0 = (c : WithTop ℝ) → ψ (g c) = 0) :
    Continuous fun t : ℝ => if ((t : ℝ) : WithTop ℝ) < T0 then c0 * ψ (g t) else 0 := by
  have hh : Continuous fun t => c0 * ψ (g t) := continuous_const.mul (hψ.comp hg)
  cases T0 with
  | top => simpa using hh
  | coe c =>
    have hc := hT0 c rfl
    have e : (fun t : ℝ => if ((t : ℝ) : WithTop ℝ) < (c : WithTop ℝ) then c0 * ψ (g t) else 0) =
        fun t => if t < c then c0 * ψ (g t) else 0 := by
      funext t; simp
    rw [e]
    refine continuous_iff_continuousAt.2 fun t0 => ?_
    rcases lt_trichotomy t0 c with h | h | h
    · have : (fun t : ℝ => if t < c then c0 * ψ (g t) else 0) =ᶠ[𝓝 t0] fun t => c0 * ψ (g t) := by
        filter_upwards [Iio_mem_nhds h] with t ht
        simp only [Set.mem_Iio] at ht
        simp [ht]
      exact hh.continuousAt.congr this.symm
    · subst h
      have ht : Tendsto (fun t : ℝ => c0 * ψ (g t)) (𝓝 t0) (𝓝 0) := by
        have := hh.continuousAt (x := t0)
        rw [ContinuousAt, hc, mul_zero] at this
        exact this
      rw [ContinuousAt]
      have h0 : (if t0 < t0 then c0 * ψ (g t0) else 0) = 0 := by simp
      rw [h0]
      refine tendsto_zero_iff_norm_tendsto_zero.2 (squeeze_zero_norm' ?_ (tendsto_zero_iff_norm_tendsto_zero.1 ht))
      exact Eventually.of_forall fun t => by
        by_cases hlt : t < t0
        · simp [hlt]
        · simp [hlt]; positivity
    · have : (fun t : ℝ => if t < c then c0 * ψ (g t) else 0) =ᶠ[𝓝 t0] fun _ => 0 := by
        filter_upwards [Ioi_mem_nhds h] with t ht
        simp only [Set.mem_Ioi] at ht
        simp [not_lt.2 ht.le]
      exact continuousAt_const.congr this.symm

/-- Real-time form of the killed-law integral. -/
theorem s113a_killedLaw_integral_real {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {s q β : ℝ}
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hX : MovParticleSetup P d s q β N X₀ W X) {ℱ : Filtration ℝ mΩ}
    (D : Set (EucConfig d N)) (chi : EucConfig d N → ℝ) (hchi : Measurable chi)
    (hchi0 : ∀ z, 0 ≤ chi z) {τ : Ω → WithTop ℝ} (hτ : IsStoppingTime ℱ τ)
    (hτg : ∀ᵐ ζ ∂P, ∀ t : ℝ≥0, ζ ∈ s113a_survives D X t ↔ ((t : ℝ) : WithTop ℝ) < τ ζ)
    (g : EucConfig d N → ℝ) (hg : Measurable g) {u : ℝ} (hu : 0 ≤ u) :
    ∫ x, g x ∂(s113a_killedLaw P D X₀ X chi u.toNNReal) =
      ∫ ζ, (if ((u : ℝ) : WithTop ℝ) < τ ζ then chi (X 0 ζ) * g (X u.toNNReal ζ) else 0) ∂P := by
  have hsol := hX.sol 0
  have h := s113a_killedLaw_integral P X₀ X (hsol.adapted 0) hsol.init D chi hchi hchi0 u.toNNReal
    (hsol.adapted _) τ
    ((s113a_measurableSet_lt_stopping hτ).preimage (measurable_prodMk_left (x := ((u.toNNReal : ℝ≥0) : ℝ))))
    (hτg.mono fun ζ h => h u.toNNReal) g hg
  rw [h]
  simp only [Real.coe_toNNReal _ hu]

/-- Continuity in time of `t ↦ ∫ ψ d(killed law at t)` for `ψ` continuous, bounded and vanishing off `D`. -/
theorem s113a_killed_pairing_continuousOn {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {s q β : ℝ}
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hX : MovParticleSetup P d s q β N X₀ W X) {ℱ : Filtration ℝ mΩ}
    (D : Set (EucConfig d N)) (chi : EucConfig d N → ℝ) (hchi : Measurable chi)
    (hchi0 : ∀ z, 0 ≤ chi z) (hchi1 : ∀ z, chi z ≤ 1) {τ : Ω → WithTop ℝ} (hτ : IsStoppingTime ℱ τ)
    (hτg : ∀ᵐ ζ ∂P, (∀ t : ℝ≥0, ζ ∈ s113a_survives D X t ↔ ((t : ℝ) : WithTop ℝ) < τ ζ) ∧
      ∀ c : ℝ, τ ζ = (c : WithTop ℝ) → 0 ≤ c ∧ X c.toNNReal ζ ∉ D)
    (ψ : EucConfig d N → ℝ) (hψ : Continuous ψ) (hψ0 : ∀ x, x ∉ D → ψ x = 0) {C0 : ℝ}
    (hψb : ∀ x, |ψ x| ≤ C0) :
    ContinuousOn (fun t : ℝ => ∫ x, ψ x ∂(s113a_killedLaw P D X₀ X chi t.toNNReal)) (Set.Ici 0) := by
  classical
  have hsol := hX.sol 0
  have hcongr : Set.EqOn (fun t : ℝ => ∫ x, ψ x ∂(s113a_killedLaw P D X₀ X chi t.toNNReal))
      (fun t : ℝ => ∫ ζ, (if ((t : ℝ) : WithTop ℝ) < τ ζ then chi (X 0 ζ) * ψ (X t.toNNReal ζ) else 0) ∂P)
      (Set.Ici 0) := fun t ht =>
    s113a_killedLaw_integral_real hX D chi hchi hchi0 hτ (hτg.mono fun ζ h => h.1) ψ hψ.measurable ht
  refine ContinuousOn.congr ?_ hcongr
  refine continuousOn_of_dominated (bound := fun _ => C0) (fun t _ => ?_) (fun t _ => ?_) (integrable_const _)
    ?_
  · have hXu : Measurable (X t.toNNReal) := (hX.sol 0).adapted _
    refine (Measurable.ite ?_ ((hchi.comp ((hX.sol 0).adapted 0)).mul (hψ.measurable.comp hXu))
      measurable_const).aestronglyMeasurable
    exact (s113a_measurableSet_lt_stopping hτ).preimage (measurable_prodMk_left (x := t))
  · refine ae_of_all _ fun ζ => ?_
    split_ifs
    · rw [norm_mul, Real.norm_of_nonneg (hchi0 _), Real.norm_eq_abs]
      calc chi (X 0 ζ) * |ψ (X t.toNNReal ζ)| ≤ 1 * C0 :=
            mul_le_mul (hchi1 _) (hψb _) (abs_nonneg _) zero_le_one
        _ = C0 := one_mul C0
    · simpa using (abs_nonneg _).trans (hψb (X 0 ζ))
  · filter_upwards [hτg, (hX.sol 0).cont] with ζ hg hc
    refine (s113a_killed_path_continuous (τ ζ) (fun t : ℝ => X t.toNNReal ζ)
      ((continuous_pi hc).comp continuous_real_toNNReal) ψ hψ (chi (X 0 ζ)) ?_).continuousOn
    intro c hcτ
    exact hψ0 _ (hg.2 c hcτ).2

end HRS.MS.S113X2

end
