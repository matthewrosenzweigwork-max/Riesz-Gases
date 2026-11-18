import HRS.MS.Fp81S21HilbertMart3
import HRS.MP.RdMartingale

/-!
# HRS S2.1(iii), B6-i: the particle gradient Hilbert martingale

The uniform filtered marginal moment controls the expected Hilbert--Schmidt
trace.  This gives one all-horizon integrand, to which the existing Hilbert
Itô constructor applies.  The export retains both its Hilbert-Itô identity
and its coordinate identities, in addition to the bracket.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open Classical MeasureTheory
open scoped ENNReal RealInnerProductSpace BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

/-- The normalized gradient-noise Hilbert--Schmidt integrand for a filtered
particle realization. -/
noncomputable def fp81s21_b6i_gradientNoise
    (p : Parameters) {δ : ℝ} {R : Trajectory p δ} {N : ℕ}
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (A : Particle R N) (Fp : FilteredParticle A) :
    ℝ → A.Ω → (Fin N × Fin p.d) → r26t6_Coeff :=
  fun u ω ia => fp81s21_b6i_scale N p.β •
    fp81s21_b6iGradientFeature (Nat.le_trans (by decide : 1 ≤ 2) p.hd) E
      (Fp.X (Real.toNNReal u) ω ia.1) ia.2

/-- The marginal weight controls the expected trace of the normalized
particle-gradient integrand at every nonnegative time. -/
theorem fp81s21_b6i_gradient_noise_trace_moment
    (p : Parameters)
    {δ : ℝ} {R : Trajectory p δ} {N : ℕ} (hN : 2 ≤ N)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (A : Particle R N) (Fp : FilteredParticle A)
    (Cweight : ℝ) (hCweight : 0 ≤ Cweight)
    (hweight : ∀ H : ℝ, 0 < H → ∀ u : ℝ, u ∈ Set.Icc 0 H →
      Integrable (fun ω => (N : ℝ)⁻¹ *
        ∑ i : Fin N, jbracket (Fp.X (Real.toNNReal u) ω i) ^
          (2 * ((p.d : ℝ) + 2))) A.P ∧
      (∫ ω, (N : ℝ)⁻¹ *
        ∑ i : Fin N, jbracket (Fp.X (Real.toNNReal u) ω i) ^
          (2 * ((p.d : ℝ) + 2)) ∂A.P) ≤ Cweight) :
    ∀ u : ℝ, 0 ≤ u →
      Integrable (fun ω => ∑ ia : Fin N × Fin p.d,
        ‖fp81s21_b6i_gradientNoise p E A Fp u ω ia‖ ^ 2) A.P ∧
      (∫ ω, ∑ ia : Fin N × Fin p.d,
        ‖fp81s21_b6i_gradientNoise p E A Fp u ω ia‖ ^ 2 ∂A.P) ≤
        (2 * p.β⁻¹ * Classical.choose
          (fp81s21_gradient_feature (Nat.le_trans (by decide : 1 ≤ 2) p.hd) E)) * Cweight := by
  let Cgrad := Classical.choose
    (fp81s21_gradient_feature (Nat.le_trans (by decide : 1 ≤ 2) p.hd) E)
  let K := 2 * p.β⁻¹ * Cgrad
  let Z := fp81s21_b6i_gradientNoise p E A Fp
  let q : ℝ → A.Ω → ℝ := fun u ω => (N : ℝ)⁻¹ *
    ∑ i : Fin N, jbracket (Fp.X (Real.toNNReal u) ω i) ^
      (2 * ((p.d : ℝ) + 2))
  have hCgrad : 0 ≤ Cgrad := (Classical.choose_spec
    (fp81s21_gradient_feature (Nat.le_trans (by decide : 1 ≤ 2) p.hd) E)).1
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr p.hβ.le)) hCgrad
  have hprog : ∀ ia : Fin N × Fin p.d,
      IsProgressive Fp.ℱ (fun u ω => Z u ω ia) := by
    intro ia
    simpa [Z, fp81s21_b6i_gradientNoise] using
      fp81s21_b6i_gradient_noise_progressive p A Fp E ia
  have htraceMoment : ∀ u : ℝ, 0 ≤ u →
      Integrable (fun ω => ∑ ia : Fin N × Fin p.d, ‖Z u ω ia‖ ^ 2) A.P ∧
        (∫ ω, ∑ ia : Fin N × Fin p.d, ‖Z u ω ia‖ ^ 2 ∂A.P) ≤ K * Cweight := by
    intro u hu
    have huH : u ∈ Set.Icc (0 : ℝ) (max 1 u) := ⟨hu, le_max_right 1 u⟩
    have hHpos : 0 < max 1 u := lt_of_lt_of_le one_pos (le_max_left 1 u)
    obtain ⟨hqInt, hqBound⟩ := hweight (max 1 u) hHpos u huH
    have hqInt' : Integrable (q u) A.P := by simpa [q] using hqInt
    have hqBound' : (∫ ω, q u ω ∂A.P) ≤ Cweight := by simpa [q] using hqBound
    have htraceMeas : Measurable (fun ω =>
        ∑ ia : Fin N × Fin p.d, ‖Z u ω ia‖ ^ 2) := by
      refine Finset.measurable_sum _ fun ia _ => ?_
      have hcoord : Measurable (fun ω : A.Ω => Z u ω ia) :=
        (HRS.MRep.isProgressive_measurable_uncurry (hprog ia)).comp
          (measurable_const.prodMk measurable_id)
      exact (measurable_norm.comp hcoord).pow_const 2
    have htraceNonneg (ω : A.Ω) :
        0 ≤ ∑ ia : Fin N × Fin p.d, ‖Z u ω ia‖ ^ 2 :=
      Finset.sum_nonneg fun ia _ => sq_nonneg _
    have htraceBound (ω : A.Ω) :
        (∑ ia : Fin N × Fin p.d, ‖Z u ω ia‖ ^ 2) ≤ K * q u ω := by
      have hraw := fp81s21_b6i_gradient_noise_trace_bound p hN E
        (Fp.X (Real.toNNReal u) ω)
      have hraw' : (∑ ia : Fin N × Fin p.d, ‖Z u ω ia‖ ^ 2) ≤
          (2 * p.β⁻¹ / (N : ℝ)) * Cgrad *
            ∑ i : Fin N, jbracket (Fp.X (Real.toNNReal u) ω i) ^
              (2 * ((p.d : ℝ) + 2)) := by
        change (∑ ia : Fin N × Fin p.d,
          ‖fp81s21_b6i_scale N p.β •
            fp81s21_b6iGradientFeature
              (Nat.le_trans (by decide : 1 ≤ 2) p.hd) E
              (Fp.X (Real.toNNReal u) ω ia.1) ia.2‖ ^ 2) ≤ _
        exact hraw
      calc
        (∑ ia : Fin N × Fin p.d, ‖Z u ω ia‖ ^ 2) ≤
            (2 * p.β⁻¹ / (N : ℝ)) * Cgrad *
              ∑ i : Fin N, jbracket (Fp.X (Real.toNNReal u) ω i) ^
                (2 * ((p.d : ℝ) + 2)) := hraw'
        _ = K * q u ω := by dsimp [K, q]; ring
    have hmajorant : Integrable (fun ω => K * q u ω) A.P := hqInt'.const_mul K
    have htraceInt : Integrable
        (fun ω => ∑ ia : Fin N × Fin p.d, ‖Z u ω ia‖ ^ 2) A.P :=
      Integrable.mono' hmajorant htraceMeas.aestronglyMeasurable
        (Filter.Eventually.of_forall fun ω => by
          rw [Real.norm_of_nonneg (htraceNonneg ω)]
          exact htraceBound ω)
    refine ⟨htraceInt, ?_⟩
    calc
      (∫ ω, ∑ ia : Fin N × Fin p.d, ‖Z u ω ia‖ ^ 2 ∂A.P) ≤
          ∫ ω, K * q u ω ∂A.P :=
        integral_mono_ae htraceInt hmajorant
          (Filter.Eventually.of_forall htraceBound)
      _ = K * (∫ ω, q u ω ∂A.P) := by rw [integral_const_mul]
      _ ≤ K * Cweight := mul_le_mul_of_nonneg_left hqBound' hK
  intro u hu
  simpa [Z, Cgrad, K] using htraceMoment u hu

/-- The normalized gradient noise is a Hilbert--Schmidt integrand on every
real horizon, including negative horizons where the defining interval is
empty. -/
theorem fp81s21_b6i_gradient_noise_isHSIntegrand
    (p : Parameters)
    {δ : ℝ} {R : Trajectory p δ} {N : ℕ} (hN : 2 ≤ N)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (A : Particle R N) (Fp : FilteredParticle A)
    (Cweight : ℝ) (hCweight : 0 ≤ Cweight)
    (hweight : ∀ H : ℝ, 0 < H → ∀ u : ℝ, u ∈ Set.Icc 0 H →
      Integrable (fun ω => (N : ℝ)⁻¹ *
        ∑ i : Fin N, jbracket (Fp.X (Real.toNNReal u) ω i) ^
          (2 * ((p.d : ℝ) + 2))) A.P ∧
      (∫ ω, (N : ℝ)⁻¹ *
        ∑ i : Fin N, jbracket (Fp.X (Real.toNNReal u) ω i) ^
          (2 * ((p.d : ℝ) + 2)) ∂A.P) ≤ Cweight) :
    ∀ T : ℝ, IsHSIntegrand A.P Fp.ℱ T
      (fp81s21_b6i_gradientNoise p E A Fp) := by
  let Z := fp81s21_b6i_gradientNoise p E A Fp
  have hprog : ∀ ia : Fin N × Fin p.d,
      IsProgressive Fp.ℱ (fun u ω => Z u ω ia) := by
    intro ia
    simpa [Z, fp81s21_b6i_gradientNoise] using
      fp81s21_b6i_gradient_noise_progressive p A Fp E ia
  have htrace := fp81s21_b6i_gradient_noise_trace_moment p hN E A Fp Cweight
    hCweight hweight
  intro T
  refine ⟨hprog, (fun u ω => Summable.of_finite), ?_⟩
  by_cases hT : 0 ≤ T
  · have hbound := fp81s21_hsSqIntegralOn_le_of_uniform_moment
      (P := A.P) (ℱ := Fp.ℱ) Z T
      ((2 * p.β⁻¹ * Classical.choose
        (fp81s21_gradient_feature (Nat.le_trans (by decide : 1 ≤ 2) p.hd) E)) * Cweight)
      hT
      (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (inv_nonneg.mpr p.hβ.le))
        (Classical.choose_spec
          (fp81s21_gradient_feature (Nat.le_trans (by decide : 1 ≤ 2) p.hd) E)).1)
        hCweight)
      hprog
      (fun u hu => by
        have hh := htrace u hu.1
        simpa [Z] using hh)
    exact lt_of_le_of_lt hbound ENNReal.ofReal_lt_top
  · have hempty : Set.Icc (0 : ℝ) T = ∅ := Set.Icc_eq_empty hT
    simp [hsSqIntegralOn, hempty]

/-- Construct the normalized empirical-gradient Hilbert martingale once for
all horizons, retaining its bracket, stochastic-integral, and coordinate
identities. -/
theorem fp81s21_b6i_hilbertMartingaleIto
    (p : Parameters)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)) :
    ∃ δstar : ℝ, 0 < δstar ∧ δstar ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δstar → ∀ R : Trajectory p δ,
        ∃ Cweight : ℝ, 0 ≤ Cweight ∧
          ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N, ∀ Fp : FilteredParticle A,
            ∃ m : ℝ → A.Ω → r26t6_Coeff,
              Measurable (Function.uncurry m) ∧
              (∀ T : ℝ, IsHSIntegrand A.P Fp.ℱ T
                (fp81s21_b6i_gradientNoise p E A Fp)) ∧
              IsHilbertItoIntegral A.P Fp.ℱ Fp.Wc
                (fp81s21_b6i_gradientNoise p E A Fp) m ∧
              (∀ H : ℝ, IsHilbertMartingaleWithCovariation A.P Fp.ℱ H m
                (fun u ω => hsCovForm (fp81s21_b6i_gradientNoise p E A Fp u ω))) ∧
              (∀ᵐ ω ∂A.P, m 0 ω = 0) ∧
              (∀ u ω i k,
                fp81s21_b6i_gradientNoise p E A Fp u ω (i, k) =
                  fp81s21_b6i_scale N p.β •
                    fp81s21_b6iGradientFeature
                      (Nat.le_trans (by decide : 1 ≤ 2) p.hd) E
                      (Fp.X (Real.toNNReal u) ω i) k) ∧
              ∀ x t, 0 ≤ t →
                (fun ω => inner ℝ (m t ω) x) =ᵐ[A.P]
                  itoIntegral A.P Fp.ℱ Fp.Wc
                    (fun u ω ia => inner ℝ
                      (fp81s21_b6i_gradientNoise p E A Fp u ω ia) x) t := by
  obtain ⟨δstar, hδstar, hδhalf, hweightAll⟩ :=
    fp81s21_b6i_filtered_gradient_weight_moment p
  refine ⟨δstar, hδstar, hδhalf, ?_⟩
  intro δ hδ hδle R
  obtain ⟨Cweight, hCweight, hweight⟩ := hweightAll δ hδ hδle R
  refine ⟨Cweight, hCweight, ?_⟩
  intro N hN A Fp
  let Z := fp81s21_b6i_gradientNoise p E A Fp
  have hweightNA : ∀ H : ℝ, 0 < H → ∀ u : ℝ, u ∈ Set.Icc 0 H →
      Integrable (fun ω => (N : ℝ)⁻¹ *
        ∑ i : Fin N, jbracket (Fp.X (Real.toNNReal u) ω i) ^
          (2 * ((p.d : ℝ) + 2))) A.P ∧
      (∫ ω, (N : ℝ)⁻¹ *
        ∑ i : Fin N, jbracket (Fp.X (Real.toNNReal u) ω i) ^
          (2 * ((p.d : ℝ) + 2)) ∂A.P) ≤ Cweight := hweight N hN A Fp
  have hZ : ∀ T : ℝ, IsHSIntegrand A.P Fp.ℱ T Z := by
    intro T
    simpa [Z, fp81s21_b6i_gradientNoise] using
      (fp81s21_b6i_gradient_noise_isHSIntegrand p hN E A Fp Cweight hCweight hweightNA T)
  letI : TopologicalSpace.SeparableSpace r26t6_Coeff :=
    HRS.StaticLimitAux.separable_lp (ι := ℕ)
  letI : SecondCountableTopology r26t6_Coeff :=
    UniformSpace.secondCountable_of_separable r26t6_Coeff
  have hWc : IsCylindricalBrownian A.P Fp.ℱ Fp.Wc :=
    HRS.GF.gfb3_isCylindricalBrownian_of_filtration Fp.filtered.brownian
  obtain ⟨m, hc, ha, hz, hJ⟩ :=
    HRS.GF.gfb3_exists_hilbert_version hWc hZ
  have hIto : IsHilbertItoIntegral A.P Fp.ℱ Fp.Wc Z m := by
    refine ⟨hc, ha, hz, ?_⟩
    intro t ht x
    obtain ⟨Jx, hJx, hcoord⟩ := hJ x
    refine (hJx.approx t ht).congr fun s => ?_
    refine lintegral_congr_ae ?_
    filter_upwards [hcoord t ht] with ω hω
    rw [hω]
    rfl
  have hHM : ∀ H : ℝ,
      IsHilbertMartingaleWithCovariation A.P Fp.ℱ H m
        (fun u ω => hsCovForm (Z u ω)) := by
    intro H
    exact HRS.Uniform.Q07c.isHM_of_ito hWc hZ hc ha hz hJ H
  have hmeas : Measurable (Function.uncurry m) :=
    measurable_uncurry_of_continuous_of_measurable hc
      (fun t => (ha t).mono (Fp.ℱ.le t) le_rfl)
  have hcoord : ∀ x t, 0 ≤ t →
      (fun ω => inner ℝ (m t ω) x) =ᵐ[A.P]
        itoIntegral A.P Fp.ℱ Fp.Wc
          (fun u ω ia => inner ℝ (Z u ω ia) x) t := by
    intro x t ht
    exact HRS.GF.gfb3_pair_ito Fp.filtered.brownian hIto x
      (HRS.pc_isProgressiveL2_inner hZ x Finset.univ) ht
  refine ⟨m, hmeas, hZ, hIto, hHM, ?_, ?_, hcoord⟩
  · exact Filter.Eventually.of_forall fun ω => hz 0 le_rfl ω
  · intro u ω i k
    rfl

end HRS.Fp81.S21

#print axioms HRS.Fp81.S21.fp81s21_b6i_gradient_noise_trace_moment
#print axioms HRS.Fp81.S21.fp81s21_b6i_gradient_noise_isHSIntegrand
#print axioms HRS.Fp81.S21.fp81s21_b6i_hilbertMartingaleIto
