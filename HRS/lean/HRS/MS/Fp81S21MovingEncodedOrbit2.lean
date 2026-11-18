import HRS.MS.Fp81S21MovingEncodedOrbit

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6
open HRS.MS.ProClosureS111 HRS.MS.S111K4J01 HRS.MS.S111K4AT HRS.MS.FixEq

/-- Moving clamped oscillator orbits and their gradient pairs are encoded,
measurable, and uniformly bounded for every fixed preparation horizon. -/
theorem fp81s21_moving_encoded_clamped_orbits (p : Parameters) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
      ∀ E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2),
      ∀ (a : ℝ) (ha : 0 ≤ a)
        (τ : Fin 3 → Icc (0 : ℝ) p.T) (φ : Fin 3 → Euc p.d → ℝ),
      (∀ i, IsOscTest (wholeSpaceIndex p.d : ℝ) (φ i)) →
      let F := fun (i : Fin 3) (r : ℝ) =>
        propagatorW (r26t3_coeff R)
          (projIcc 0 (a + (τ i : ℝ)) (add_nonneg ha (τ i).property.1) r)
          (a + (τ i : ℝ)) (φ i)
      let Good := fun h : ℝ → Euc p.d → ℝ =>
        StronglyMeasurable (fun r => E.encode (h r)) ∧
        (∀ r, IsR2WeightedTest (2 * p.d + 8) ((p.d : ℝ) + 2) (h r)) ∧
        ∃ B : ℝ, 0 ≤ B ∧ ∀ r, ‖E.encode (h r)‖ ≤ B
      (∀ i, Good (F i)) ∧
      (∀ i j, Good (fun r x =>
        inner ℝ (gradient (F i r) x) (gradient (F j r) x))) := by
  obtain ⟨δ₀, hδ₀, hδhalf, hstd⟩ := fp81s21_moving_std p
  refine ⟨δ₀, hδ₀, hδhalf, fun δ hδ hδle R E a ha τ φ hφ => ?_⟩
  have hH : 0 < a + p.T := by linarith [p.hT]
  obtain ⟨c, hc⟩ := hstd δ hδ hδle R a ha
  let F : Fin 3 → ℝ → Euc p.d → ℝ := fun i r =>
    propagatorW (r26t3_coeff R)
      (projIcc 0 (a + (τ i : ℝ)) (add_nonneg ha (τ i).property.1) r)
      (a + (τ i : ℝ)) (φ i)
  let B : Fin 3 → ℝ := fun i => oscNorm (wholeSpaceIndex p.d : ℝ) (φ i) *
    Real.sqrt (∑' α, c α ^ 2)
  have hB : ∀ i, 0 ≤ B i := fun i => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hreg : ∀ i r, MemCb (2 * p.d + 9) (F i r) ∧
      ∀ j ≤ 2 * p.d + 9, ∀ x, ‖iteratedFDeriv ℝ j (F i r) x‖ ≤ B i := by
    intro i r
    have ht : a + (τ i : ℝ) ≤ a + p.T := by linarith [(τ i).property.2]
    have hu : (projIcc 0 (a + (τ i : ℝ)) (add_nonneg ha (τ i).property.1) r : ℝ) ∈
        Icc (0 : ℝ) (a + p.T) :=
      ⟨(projIcc 0 _ _ r).property.1, (projIcc 0 _ _ r).property.2.trans ht⟩
    have hut : a + (τ i : ℝ) ∈ Icc
        (projIcc 0 (a + (τ i : ℝ)) (add_nonneg ha (τ i).property.1) r : ℝ) (a + p.T) :=
      ⟨(projIcc 0 _ _ r).property.2, ht⟩
    exact fp81s21_moving_orbit_jet_bound p R hH hc (hφ i) hu hut
  have hmeas : ∀ i, StronglyMeasurable (fun q : ℝ × Euc p.d => F i q.1 q.2) := by
    intro i
    have ht : 0 ≤ a + (τ i : ℝ) := add_nonneg ha (τ i).property.1
    have hcl := fp81s21_U_osc_test_classical p R (hφ i) ht
    exact ((chart_classical_value_continuous hcl).comp
      (((continuous_projIcc (h := ht)).comp continuous_fst).prodMk continuous_snd)).stronglyMeasurable
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by
    have : (0 : ℝ) ≤ (p.d : ℝ) := Nat.cast_nonneg _
    linarith
  constructor
  · intro i
    have hr : ∀ r, MemCb (2 * p.d + 8) (F i r) := fun r =>
      chart_memCb_mono (by omega) (hreg i r).1
    refine ⟨chart_encode_stronglyMeasurable (nativeChartOfFrozen E) hP (F i) (hmeas i) hr,
      fun r => chart_weighted_of_memCb hP (hr r),
      s57pC p.d (2 * p.d + 8) ((p.d : ℝ) + 2) * B i,
      mul_nonneg (s57pC_nonneg _ _ _) (hB i), ?_⟩
    intro r
    exact frozen_encode_le_jet_bound E hP _ (hr r) (B i) (hB i)
      (fun j hj x => (hreg i r).2 j (by omega) x)
  · intro i j
    let A : ℝ → Euc p.d → ℝ := fun r x =>
      inner ℝ (gradient (F i r) x) (gradient (F j r) x)
    have hm : StronglyMeasurable (fun q : ℝ × Euc p.d => A q.1 q.2) := by
      have hi := chart_joint_gradient (F i) (hmeas i)
        (fun r => (hreg i r).1.1.differentiable (by positivity))
      have hj := chart_joint_gradient (F j) (hmeas j)
        (fun r => (hreg j r).1.1.differentiable (by positivity))
      exact (hi.measurable.inner hj.measurable).stronglyMeasurable
    have hr : ∀ r, MemCb (2 * p.d + 8) (A r) := fun r =>
      chart_memCb_gradient_inner (hreg i r).1 (hreg j r).1
    let C : ℝ := (p.d : ℝ) * (2 ^ (2 * p.d + 8) * (B i * B j))
    have hC : 0 ≤ C :=
      mul_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (pow_nonneg (by norm_num) _) (mul_nonneg (hB i) (hB j)))
    have hb : ∀ r, ∀ k ≤ 2 * p.d + 8, ∀ x, ‖iteratedFDeriv ℝ k (A r) x‖ ≤ C := by
      intro r k hk x
      have he : A r = k4Gf (F i r) (F j r) := funext (k4_inner_grad_eq _ _)
      rw [he]
      exact k4Gf_bound (hreg i r).1.1 (hreg j r).1.1 (hreg i r).2 (hreg j r).2 k hk x
    refine ⟨chart_encode_stronglyMeasurable (nativeChartOfFrozen E) hP A hm hr,
      fun r => chart_weighted_of_memCb hP (hr r),
      s57pC p.d (2 * p.d + 8) ((p.d : ℝ) + 2) * C,
      mul_nonneg (s57pC_nonneg _ _ _) hC, ?_⟩
    exact fun r => frozen_encode_le_jet_bound E hP _ (hr r) C hC (hb r)

#print axioms fp81s21_moving_encoded_clamped_orbits
end HRS.Fp81.S21
end
