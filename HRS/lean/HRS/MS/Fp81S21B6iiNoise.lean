import HRS.MS.Fp81S21HilbertMart5

/-!
# HRS S2.1(iii), B6-ii: physical noise coordinates

Pair the all-horizon Hilbert-valued Itô integral with each chart test.  The
feature identity identifies the resulting scalar integrand with the physical
gradient-noise integrand, and continuity gives one event for all times and
countably many chart coordinates.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open Classical MeasureTheory
open scoped RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

/-- Scalar physical gradient-noise integrand paired with a chart test. -/
abbrev fp81s21_b6ii_noiseIntegrand
    (p : Parameters) {δ : ℝ} {R : Trajectory p δ} {N : ℕ}
    (_E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (A : Particle R N) (Fp : FilteredParticle A) (f : Euc p.d → ℝ) :
    ℝ → A.Ω → (Fin N × Fin p.d) → ℝ :=
  fun u ω ia => fp81s21_b6i_scale N p.β *
    gradient f (Fp.X (Real.toNNReal u) ω ia.1) ia.2

/-- The scalar Itô integral of the physical gradient-noise integrand. -/
abbrev fp81s21_b6ii_scalarNoise
    (p : Parameters) {δ : ℝ} {R : Trajectory p δ} {N : ℕ}
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (A : Particle R N) (Fp : FilteredParticle A) (f : Euc p.d → ℝ) :
    ℝ → A.Ω → ℝ :=
  itoIntegral A.P Fp.ℱ Fp.Wc (fp81s21_b6ii_noiseIntegrand p E A Fp f)

private theorem fp81s21_b6ii_pair_integrand
    (p : Parameters) {δ : ℝ} {R : Trajectory p δ} {N : ℕ}
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (A : Particle R N) (Fp : FilteredParticle A) (j : ℕ) :
    (fun u ω ia => inner ℝ
      (fp81s21_b6i_gradientNoise p E A Fp u ω ia) (E.encode (E.test j))) =
      fp81s21_b6ii_noiseIntegrand p E A Fp (E.test j) := by
  funext u ω ia
  rcases ia with ⟨i, k⟩
  have htest : E.encode (E.test j) =
      (lp.single 2 j (1 : ℝ) : r26t6_Coeff) := by
    ext n
    change E.encode (E.test j) n = _
    rw [E.test_coord]
    simp [lp.single_apply, Pi.single_apply, eq_comm]
  have hfeature :
      fp81s21_b6iGradientFeature
        (Nat.le_trans (by decide : 1 ≤ 2) p.hd) E
        (Fp.X (Real.toNNReal u) ω i) k j =
          gradient (E.test j) (Fp.X (Real.toNNReal u) ω i) k :=
    (Classical.choose_spec
      ((Classical.choose_spec (fp81s21_gradient_feature
        (Nat.le_trans (by decide : 1 ≤ 2) p.hd) E)).2)).2.1
      (Fp.X (Real.toNNReal u) ω i) k j
  change inner ℝ
      (fp81s21_b6i_scale N p.β •
        fp81s21_b6iGradientFeature
          (Nat.le_trans (by decide : 1 ≤ 2) p.hd) E
          (Fp.X (Real.toNNReal u) ω i) k)
      (E.encode (E.test j)) = _
  calc
    _ = fp81s21_b6i_scale N p.β *
          inner ℝ
            (fp81s21_b6iGradientFeature
              (Nat.le_trans (by decide : 1 ≤ 2) p.hd) E
              (Fp.X (Real.toNNReal u) ω i) k)
            (E.encode (E.test j)) := by
          simp only [real_inner_smul_left]
    _ = fp81s21_b6i_scale N p.β *
          fp81s21_b6iGradientFeature
            (Nat.le_trans (by decide : 1 ≤ 2) p.hd) E
            (Fp.X (Real.toNNReal u) ω i) k j := by
          simp [htest, lp.inner_single_right]
    _ = fp81s21_b6ii_noiseIntegrand p E A Fp (E.test j) u ω (i, k) := by
          rw [hfeature]

/-- The physical gradient-noise integral is the chart-coordinate process of
B6-i, simultaneously for all nonnegative times and all chart tests. -/
theorem fp81s21_b6ii_noise_coordinates
    (p : Parameters) {δ : ℝ} {R : Trajectory p δ} {N : ℕ}
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (A : Particle R N) (Fp : FilteredParticle A)
    {m : ℝ → A.Ω → r26t6_Coeff}
    (hIto : IsHilbertItoIntegral A.P Fp.ℱ Fp.Wc
      (fp81s21_b6i_gradientNoise p E A Fp) m)
    (hZ : ∀ T, IsHSIntegrand A.P Fp.ℱ T
      (fp81s21_b6i_gradientNoise p E A Fp)) :
    ∀ᵐ ω ∂A.P, ∀ j : ℕ, ∀ t : ℝ, 0 ≤ t →
      fp81s21_chartAction E (m t ω) (E.test j) =
        fp81s21_b6ii_scalarNoise p E A Fp (E.test j) t ω := by
  letI : TopologicalSpace.SeparableSpace r26t6_Coeff :=
    HRS.StaticLimitAux.separable_lp (ι := ℕ)
  letI : SecondCountableTopology r26t6_Coeff :=
    UniformSpace.secondCountable_of_separable r26t6_Coeff
  have hW : IsBrownianFiltration A.P Fp.ℱ Fp.Wc := Fp.filtered.brownian
  have hfixed (j : ℕ) (t : ℝ) (ht : 0 ≤ t) :
      (fun ω => inner ℝ (m t ω) (E.encode (E.test j))) =ᵐ[A.P]
        itoIntegral A.P Fp.ℱ Fp.Wc
          (fun u ω ia => inner ℝ
            (fp81s21_b6i_gradientNoise p E A Fp u ω ia)
            (E.encode (E.test j))) t := by
    exact HRS.GF.gfb3_pair_ito hW hIto (E.encode (E.test j))
      (HRS.pc_isProgressiveL2_inner hZ (E.encode (E.test j)) Finset.univ) ht
  have hpath (j : ℕ) :
      ∀ᵐ ω ∂A.P, ∀ t : ℝ,
        inner ℝ (m t ω) (E.encode (E.test j)) =
          itoIntegral A.P Fp.ℱ Fp.Wc
            (fun u ω ia => inner ℝ
              (fp81s21_b6i_gradientNoise p E A Fp u ω ia)
              (E.encode (E.test j))) t ω := by
    apply ae_forall_eq_of_continuous A.P _ _
    · intro ω
      exact (hIto.cont ω).inner continuous_const
    · intro ω
      exact continuous_itoIntegral A.P Fp.ℱ Fp.Wc _ ω
    · intro t
      by_cases ht : 0 ≤ t
      · exact hfixed j t ht
      · have ht' : t ≤ 0 := le_of_not_ge ht
        exact Filter.Eventually.of_forall fun ω => by
          change inner ℝ (m t ω) (E.encode (E.test j)) =
            itoIntegral A.P Fp.ℱ Fp.Wc
              (fun u ω ia => inner ℝ
                (fp81s21_b6i_gradientNoise p E A Fp u ω ia)
                (E.encode (E.test j))) t ω
          rw [hIto.zero t ht' ω,
            itoIntegral_of_nonpos A.P Fp.ℱ Fp.Wc _ ht' ω]
          simp
  apply ae_all_iff.2
  intro j
  have hpair := fp81s21_b6ii_pair_integrand p E A Fp j
  filter_upwards [hpath j] with ω hω
  intro t ht
  change inner ℝ (m t ω) (E.encode (E.test j)) =
    itoIntegral A.P Fp.ℱ Fp.Wc
      (fp81s21_b6ii_noiseIntegrand p E A Fp (E.test j)) t ω
  rw [← hpair]
  exact hω t

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_b6ii_noise_coordinates
