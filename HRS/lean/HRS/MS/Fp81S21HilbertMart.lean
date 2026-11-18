import HRS.MS.Fp81S21GradFeature
import HRS.MS.Fp81S21WeightTrace
import HRS.MS.S21F_P00
import HRS.Prob.HilbertMartingale

/-!
# HRS S2.1(iii), B6-i: Hilbert martingale and its bracket

This file records the exact B6-i contract and proves the gradient-noise
normalization and progressivity stages.  The stochastic square-integrability
estimate needed to construct the Itô integral is a subsequent stage.

The selected weighted chart is an input before the common small-radius
prefix, as required by the packet-32 design contract.  Its coefficient
feature is the one supplied by `fp81s21_gradient_feature`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open Classical MeasureTheory
open scoped ENNReal RealInnerProductSpace BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

/-- The empirical-gradient noise scale. -/
def fp81s21_b6i_scale (N : ℕ) (β : ℝ) : ℝ :=
  Real.sqrt (N : ℝ) * Real.sqrt (2 * β⁻¹) / (N : ℝ)

/-- The scale in B6-i is exactly the particle Brownian coefficient
`√(2 β⁻¹ / N)`. -/
theorem fp81s21_b6i_scale_normalization
    {N : ℕ} (hN : 2 ≤ N) {β : ℝ} (hβ : 0 < β) :
    fp81s21_b6i_scale N β = Real.sqrt (2 * β⁻¹ / (N : ℝ)) := by
  have hNpos : 0 < (N : ℝ) := by
    exact_mod_cast (show 0 < N by omega)
  have hβinv : 0 < β⁻¹ := inv_pos.mpr hβ
  have hb : 0 ≤ 2 * β⁻¹ := by positivity
  unfold fp81s21_b6i_scale
  rw [Real.sqrt_div hb (N : ℝ)]
  calc
    Real.sqrt (N : ℝ) * Real.sqrt (2 * β⁻¹) / (N : ℝ) =
        Real.sqrt (2 * β⁻¹) * (Real.sqrt (N : ℝ) / (N : ℝ)) := by ring
    _ = Real.sqrt (2 * β⁻¹) * (Real.sqrt (N : ℝ))⁻¹ := by
      rw [Real.sqrt_div_self]
    _ = Real.sqrt (2 * β⁻¹) / Real.sqrt (N : ℝ) := by
      rw [div_eq_mul_inv]

/-- The coefficient feature selected by the proved weighted-gradient
representation. -/
noncomputable def fp81s21_b6iGradientFeature
    {d : ℕ} (hd : 1 ≤ d)
    (E : r26t6_WeightedChart d (2 * d + 8) ((d : ℝ) + 2)) :
    Euc d → Fin d → r26t6_Coeff :=
  Classical.choose ((Classical.choose_spec (fp81s21_gradient_feature hd E)).2)

theorem fp81s21_b6iGradientFeature_measurable
    {d : ℕ} (hd : 1 ≤ d)
    (E : r26t6_WeightedChart d (2 * d + 8) ((d : ℝ) + 2)) :
    Measurable (Function.uncurry (fp81s21_b6iGradientFeature hd E)) := by
  exact (Classical.choose_spec
    ((Classical.choose_spec (fp81s21_gradient_feature hd E)).2)).1

/-- The exact B6-i proposition, including the common small-radius prefix
specified in the packet-32 design.  The chart is fixed before that prefix.
This is a contract definition; the Itô construction is not proved in this
partial unit. -/
def fp81s21_b6iHilbertMartingaleBracketContract
    (p : Parameters)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)) : Prop :=
  ∃ δstar : ℝ, 0 < δstar ∧ δstar ≤ 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δstar → ∀ R : Trajectory p δ,
      ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
        ∀ (Fp : FilteredParticle A), ∀ H : ℝ, 0 < H →
          ∃ m : ℝ → A.Ω → r26t6_Coeff,
          ∃ Z : ℝ → A.Ω → (Fin N × Fin p.d) → r26t6_Coeff,
            Measurable (Function.uncurry m) ∧
            IsHilbertMartingaleWithCovariation A.P Fp.ℱ H m
              (fun u ω => hsCovForm (Z u ω)) ∧
            (∀ᵐ ω ∂A.P, m 0 ω = 0) ∧
            ∀ u ω i k, Z u ω (i, k) =
              fp81s21_b6i_scale N p.β •
                fp81s21_b6iGradientFeature (Nat.le_trans (by decide : 1 ≤ 2) p.hd) E
                  (Fp.X (Real.toNNReal u) ω i) k

/-- Every particle has a filtered version available to instantiate the
filtered-process binder in the B6-i contract. -/
theorem fp81s21_b6i_filtered_particle_nonempty
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ} {N : ℕ}
    (A : Particle R N) : Nonempty (FilteredParticle A) :=
  HRS.MS.R26T3.r26t3_filtered_particle A

/-- The empirical gradient noise family is progressive in the supplied
filtered realization.  This establishes the measurability component of the
Itô-integrand construction; its square-integrability is separate. -/
theorem fp81s21_b6i_gradient_noise_progressive
    (p : Parameters) {δ : ℝ} {R : Trajectory p δ}
    {N : ℕ} (A : Particle R N) (Fp : FilteredParticle A)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)) :
    ∀ ia : Fin N × Fin p.d,
      IsProgressive Fp.ℱ
        (fun u ω => fp81s21_b6i_scale N p.β •
          fp81s21_b6iGradientFeature (Nat.le_trans (by decide : 1 ≤ 2) p.hd) E
            (Fp.X (Real.toNNReal u) ω ia.1) ia.2) := by
  classical
  intro ia
  let D := fp81s21_b6iGradientFeature (Nat.le_trans (by decide : 1 ≤ 2) p.hd) E
  have hD : Measurable (Function.uncurry D) := by
    change Measurable (Function.uncurry
      (fp81s21_b6iGradientFeature (Nat.le_trans (by decide : 1 ≤ 2) p.hd) E))
    exact fp81s21_b6iGradientFeature_measurable (Nat.le_trans (by decide : 1 ≤ 2) p.hd) E
  have harg : Measurable (fun q : ℝ × EucConfig p.d N =>
      ((q.2 ia.1, ia.2) : Euc p.d × Fin p.d)) := by
    exact ((measurable_pi_apply ia.1).comp measurable_snd).prodMk measurable_const
  have hV : Measurable (fun q : ℝ × EucConfig p.d N =>
      fp81s21_b6i_scale N p.β • D (q.2 ia.1) ia.2) := by
    exact (hD.comp harg).const_smul (fp81s21_b6i_scale N p.β)
  have hprog := HRS.MS.R2Interp.s102_prog_comp hV Fp.filtered.progressive
  simpa [D, HRS.ofNNRealTime] using hprog

/-- The generic higher-marginal theorem supplies the precise polynomial
weight that controls the squared gradient-feature trace. -/
theorem fp81s21_b6i_uniform_gradient_weight_moment (p : Parameters) :
    ∃ δstar : ℝ, 0 < δstar ∧ δstar ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δstar → ∀ R : Trajectory p δ,
        ∃ C : ℝ, 0 ≤ C ∧
          ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N, ∀ u : ℝ, 0 ≤ u →
            Integrable (fun x : Euc p.d =>
              jbracket x ^ (2 * ((p.d : ℝ) + 2)))
              (HRS.Whole.meanEmpirical (law A.P (A.X u.toNNReal))) ∧
            (∫ x : Euc p.d,
              jbracket x ^ (2 * ((p.d : ℝ) + 2))
              ∂(HRS.Whole.meanEmpirical (law A.P (A.X u.toNNReal)))) ≤ C := by
  obtain ⟨δstar, hδstar, hδhalf, hweights⟩ :=
    fp81s21_uniform_higher_marginal_weights p
  refine ⟨δstar, hδstar, hδhalf, ?_⟩
  intro δ hδ hδle R
  exact hweights δ hδ hδle R
    (2 * ((p.d : ℝ) + 2)) (by positivity)

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_b6i_scale_normalization
#print axioms HRS.Fp81.S21.fp81s21_b6iGradientFeature_measurable
#print axioms HRS.Fp81.S21.fp81s21_b6iHilbertMartingaleBracketContract
#print axioms HRS.Fp81.S21.fp81s21_b6i_filtered_particle_nonempty
#print axioms HRS.Fp81.S21.fp81s21_b6i_gradient_noise_progressive
#print axioms HRS.Fp81.S21.fp81s21_b6i_uniform_gradient_weight_moment

namespace HRS.Fp81.S21

open HRS.MS.R26T3 HRS.MS.R26T6

/-- The filtered realization and the observed particle path agree at every
real time on one event, by the all-times field of `FilteredParticle`. -/
theorem fp81s21_b6i_filtered_path_agreement
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ} {N : ℕ}
    (A : Particle R N) (Fp : FilteredParticle A) :
    ∀ᵐ ω ∂A.P, ∀ u : ℝ,
      Fp.X (Real.toNNReal u) ω = A.X (Real.toNNReal u) ω := by
  filter_upwards [Fp.indist] with ω hω
  intro u
  exact hω (Real.toNNReal u)

/-- The gradient-noise coefficient is unchanged a.e. when the filtered
trajectory `Fp.X` is transferred to the observed trajectory `A.X`. -/
theorem fp81s21_b6i_gradient_noise_path_transfer
    (p : Parameters) {δ : ℝ} {R : Trajectory p δ} {N : ℕ}
    (A : Particle R N) (Fp : FilteredParticle A)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)) :
    ∀ᵐ ω ∂A.P, ∀ u : ℝ, ∀ ia : Fin N × Fin p.d,
      fp81s21_b6i_scale N p.β •
          fp81s21_b6iGradientFeature (Nat.le_trans (by decide : 1 ≤ 2) p.hd) E
            (Fp.X (Real.toNNReal u) ω ia.1) ia.2 =
        fp81s21_b6i_scale N p.β •
          fp81s21_b6iGradientFeature (Nat.le_trans (by decide : 1 ≤ 2) p.hd) E
            (A.X (Real.toNNReal u) ω ia.1) ia.2 := by
  filter_upwards [Fp.indist] with ω hω
  intro u ia
  rw [hω (Real.toNNReal u)]

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_b6i_scale_normalization
#print axioms HRS.Fp81.S21.fp81s21_b6iGradientFeature_measurable
#print axioms HRS.Fp81.S21.fp81s21_b6iHilbertMartingaleBracketContract
#print axioms HRS.Fp81.S21.fp81s21_b6i_filtered_particle_nonempty
#print axioms HRS.Fp81.S21.fp81s21_b6i_gradient_noise_progressive
#print axioms HRS.Fp81.S21.fp81s21_b6i_uniform_gradient_weight_moment
#print axioms HRS.Fp81.S21.fp81s21_b6i_filtered_path_agreement
#print axioms HRS.Fp81.S21.fp81s21_b6i_gradient_noise_path_transfer

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

/-- Pointwise Hilbert--Schmidt trace estimate for the empirical gradient
noise, with the particle Brownian normalization made explicit. -/
theorem fp81s21_b6i_gradient_noise_trace_bound
    (p : Parameters) {N : ℕ} (hN : 2 ≤ N)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (x : EucConfig p.d N) :
    (∑ ia : Fin N × Fin p.d,
      ‖fp81s21_b6i_scale N p.β •
        fp81s21_b6iGradientFeature (Nat.le_trans (by decide : 1 ≤ 2) p.hd) E
          (x ia.1) ia.2‖ ^ 2) ≤
      (2 * p.β⁻¹ / (N : ℝ)) * (Classical.choose
        (fp81s21_gradient_feature (Nat.le_trans (by decide : 1 ≤ 2) p.hd) E)) *
        ∑ i : Fin N, jbracket (x i) ^ (2 * ((p.d : ℝ) + 2)) := by
  classical
  let hFeat := fp81s21_gradient_feature
    (Nat.le_trans (by decide : 1 ≤ 2) p.hd) E
  let C := Classical.choose hFeat
  let D := fp81s21_b6iGradientFeature (Nat.le_trans (by decide : 1 ≤ 2) p.hd) E
  have hC : 0 ≤ C := (Classical.choose_spec hFeat).1
  have htrace : ∀ y : Euc p.d,
      ∑ k : Fin p.d, ‖D y k‖ ^ 2 ≤
        C * jbracket y ^ (2 * ((p.d : ℝ) + 2)) := by
    have hh := (Classical.choose_spec ((Classical.choose_spec hFeat).2)).2.2
    simpa [C, D, fp81s21_b6iGradientFeature] using hh
  have hfac : 0 ≤ 2 * p.β⁻¹ / (N : ℝ) := by
    have hNr : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    exact div_nonneg (mul_nonneg (by norm_num) (le_of_lt (inv_pos.mpr p.hβ))) hNr.le
  have hc0 : 0 ≤ fp81s21_b6i_scale N p.β := by
    rw [fp81s21_b6i_scale_normalization hN p.hβ]
    positivity
  have hcSq : (fp81s21_b6i_scale N p.β) ^ 2 = 2 * p.β⁻¹ / (N : ℝ) := by
    rw [fp81s21_b6i_scale_normalization hN p.hβ]
    exact Real.sq_sqrt (by positivity)
  have hcoord (i : Fin N) (k : Fin p.d) :
      ‖fp81s21_b6i_scale N p.β • D (x i) k‖ ^ 2 =
        (fp81s21_b6i_scale N p.β) ^ 2 * ‖D (x i) k‖ ^ 2 := by
    rw [norm_smul, Real.norm_of_nonneg hc0]
    ring
  have hsum :
      (∑ ia : Fin N × Fin p.d,
        ‖fp81s21_b6i_scale N p.β • D (x ia.1) ia.2‖ ^ 2) =
        (fp81s21_b6i_scale N p.β) ^ 2 *
          ∑ i : Fin N, ∑ k : Fin p.d, ‖D (x i) k‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
    simp_rw [hcoord]
    simp only [Finset.mul_sum]
  rw [show fp81s21_b6iGradientFeature
      (Nat.le_trans (by decide : 1 ≤ 2) p.hd) E = D by rfl, hsum, hcSq]
  calc
    (2 * p.β⁻¹ / (N : ℝ)) * ∑ i : Fin N, ∑ k : Fin p.d, ‖D (x i) k‖ ^ 2
      ≤ (2 * p.β⁻¹ / (N : ℝ)) *
          ∑ i : Fin N, C * jbracket (x i) ^ (2 * ((p.d : ℝ) + 2)) := by
        apply mul_le_mul_of_nonneg_left _ hfac
        exact Finset.sum_le_sum fun i _ => htrace (x i)
    _ = (2 * p.β⁻¹ / (N : ℝ)) * C *
          ∑ i : Fin N, jbracket (x i) ^ (2 * ((p.d : ℝ) + 2)) := by
        rw [← Finset.mul_sum]
        ring

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_b6i_gradient_noise_trace_bound
