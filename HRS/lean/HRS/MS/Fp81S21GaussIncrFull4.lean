import HRS.MS.Fp81S21GaussIncrFull3

/-!
# HRS S2.1(iii), SOL71 G2: combined Gaussian-feature increments

The direct-sum feature increment is bounded by adding the initial and noise
contributions.  Its modewise coefficient is square-summable and is selected
before the shift, realization, and mode.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole HRS.MS.R26T3 HRS.MS.R2WinErr HRS.MS.S111X2

/-- Deterministic increment estimate for the combined initial-plus-noise
feature, with a summable modewise coefficient fixed before `a`, `s`, `t`, and
`α`. -/
theorem fp81s21_gaussian_combined_feature_increment_bound (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 →
        ∀ (R : Trajectory p δ) [IsProbabilityMeasure (r26t3_mu R 0)],
        ∃ Mg : ℝ, ∃ K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ]
          Lp ℝ 2 (r26t3_mu R 0),
        ∃ hK : KRep (rieszKernel p.d p.s) (r26t3_mu R 0) K Mg,
          ∃ B g g' c gN cN : ℝ,
            0 ≤ B ∧ 0 ≤ g ∧ 0 ≤ g' ∧ 0 < c ∧ 0 ≤ gN ∧ 0 < cN ∧
            ∀ H : ℝ, 0 < H →
              ∃ L : MultiIndex p.d → ℝ,
                (∀ α, 0 ≤ L α) ∧ Summable L ∧
                ∀ a : ℝ, 0 ≤ a →
                  ∀ s ∈ Icc (0 : ℝ) H, ∀ t ∈ Icc (0 : ℝ) H,
                    ∀ α : MultiIndex p.d,
                      ‖fp81s21_combinedFeature p R hK (a + t)
                          (oscTestFun (wholeSpaceIndex p.d : ℝ) α) -
                        fp81s21_combinedFeature p R hK (a + s)
                          (oscTestFun (wholeSpaceIndex p.d : ℝ) α)‖ ^ 2 ≤
                        L α * |t - s| := by
  obtain ⟨δI, hδI, hδIhalf, hinitial⟩ :=
    fp81s21_gaussian_initial_feature_increment_bound p
  obtain ⟨δN, hδN, _, hnoise⟩ :=
    fp81s21_gaussian_noise_feature_increment_bound p
  obtain ⟨δS, hδS, _, hdecay⟩ :=
    fp81s21_moving_orbit_gradient_decay p
  let δ0 := min δI (min δN δS)
  have hδ0 : 0 < δ0 := lt_min hδI (lt_min hδN hδS)
  have hδ0half : δ0 ≤ 1 / 2 :=
    (min_le_left _ _).trans hδIhalf
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R hμ
  have hδI_R : δ ≤ δI := le_trans hδle (min_le_left _ _)
  have hδN_R : δ ≤ δN := le_trans hδle
    ((min_le_right _ _).trans (min_le_left _ _))
  have hδS_R : δ ≤ δS := le_trans hδle
    ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨_, _, _, _, hsumB, _⟩ := hdecay δ hδ hδS_R R
  letI : IsProbabilityMeasure (r26t3_mu R 0) := hμ
  obtain ⟨B, hB, Mg, K, hK, hInitial⟩ :=
    hinitial δ hδ hδI_R R
  obtain ⟨g, g', c, gN, cN, hg, hg', hc, hgN, hcN, hNoise⟩ :=
    hnoise δ hδ hδN_R R
  refine ⟨Mg, K, hK, B, g, g', c, gN, cN,
    hB, hg, hg', hc, hgN, hcN, ?_⟩
  intro H hH
  let C : ℝ := B ^ 2 * H +
    2 * p.β⁻¹ * (gN ^ 2 + 2 * g * g' / c)
  let L : MultiIndex p.d → ℝ := fun α =>
    C * (s104_b p.d α) ^ 2
  have hC0 : 0 ≤ C := by
    dsimp [C]
    have hβ : 0 ≤ p.β⁻¹ := inv_nonneg.mpr p.hβ.le
    have hOld : 0 ≤ 2 * g * g' / c :=
      div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hg) hg') hc.le
    exact add_nonneg (mul_nonneg (sq_nonneg B) hH.le)
      (mul_nonneg (mul_nonneg (by norm_num) hβ)
        (add_nonneg (sq_nonneg gN) hOld))
  have hL0 : ∀ α, 0 ≤ L α := by
    intro α
    dsimp [L]
    positivity
  have hsumSq : Summable (fun α : MultiIndex p.d => (s104_b p.d α) ^ 2) :=
    HRS.MS.R2GenInit.s105_b_sq_summable hsumB
  have hsumL : Summable L := by
    exact (hsumSq.mul_left C).congr fun α => by
      simp [L]
  refine ⟨L, hL0, hsumL, ?_⟩
  intro a ha s hs t ht α
  let u := a + s
  let w₀ := a + t
  let v := min u w₀
  let w := max u w₀
  let φ : Euc p.d → ℝ := oscTestFun (wholeSpaceIndex p.d : ℝ) α
  have hu0 : 0 ≤ u := by dsimp [u]; linarith [hs.1]
  have hw00 : 0 ≤ w₀ := by dsimp [w₀]; linarith [ht.1]
  have hv0 : 0 ≤ v := by dsimp [v]; exact le_min hu0 hw00
  have hvw : v ≤ w := by
    dsimp [v, w]
    exact (min_le_left u w₀).trans (le_max_left u w₀)
  have hwv : w - v = |t - s| := by
    by_cases hts : u ≤ w₀
    · have hnonneg : 0 ≤ t - s := by dsimp [u, w₀] at hts; linarith
      simp [w, v, max_eq_right hts, min_eq_left hts, abs_of_nonneg hnonneg]
      dsimp [u, w₀]
      ring
    · have hst : w₀ ≤ u := le_of_not_ge hts
      have hnonpos : t - s ≤ 0 := by dsimp [u, w₀] at hst; linarith
      simp [w, v, max_eq_left hst, min_eq_right hst, abs_of_nonpos hnonpos]
      dsimp [u, w₀]
      ring
  have htime : |t - s| ≤ H := by
    apply (abs_le).2
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  have hinit := hInitial H hH a ha s hs t ht α
  have hnoise := hNoise v w hv0 hvw α
  rw [hwv] at hnoise
  have hpair :
      ‖fp81s21_combinedFeature p R hK (a + t) φ -
        fp81s21_combinedFeature p R hK (a + s) φ‖ ^ 2 =
      ‖fp81s21_initialGaussianFeature p R hK (a + t) φ -
          fp81s21_initialGaussianFeature p R hK (a + s) φ‖ ^ 2 +
        ‖movingNoiseFeature R 0 (a + t) φ -
            movingNoiseFeature R 0 (a + s) φ‖ ^ 2 := by
    change ‖WithLp.toLp 2
          (fp81s21_initialGaussianFeature p R hK (a + t) φ,
            movingNoiseFeature R 0 (a + t) φ) -
        WithLp.toLp 2
          (fp81s21_initialGaussianFeature p R hK (a + s) φ,
            movingNoiseFeature R 0 (a + s) φ)‖ ^ 2 = _
    rw [show WithLp.toLp 2
          (fp81s21_initialGaussianFeature p R hK (a + t) φ,
            movingNoiseFeature R 0 (a + t) φ) -
        WithLp.toLp 2
          (fp81s21_initialGaussianFeature p R hK (a + s) φ,
            movingNoiseFeature R 0 (a + s) φ) =
        WithLp.toLp 2
          (fp81s21_initialGaussianFeature p R hK (a + t) φ -
              fp81s21_initialGaussianFeature p R hK (a + s) φ,
            movingNoiseFeature R 0 (a + t) φ -
              movingNoiseFeature R 0 (a + s) φ) by
          rw [← WithLp.toLp_sub]
          rfl]
    rw [WithLp.prod_norm_sq_eq_of_L2]
    simp
  have hnoiseSymm :
      ‖movingNoiseFeature R 0 (a + t) φ -
          movingNoiseFeature R 0 (a + s) φ‖ ^ 2 ≤
        2 * p.β⁻¹ * (gN ^ 2 + 2 * g * g' / c) *
          (s104_b p.d α) ^ 2 * |t - s| := by
    by_cases hts : u ≤ w₀
    · simpa [v, w, max_eq_right hts, min_eq_left hts] using hnoise
    · have hst : a + t ≤ a + s := le_of_not_ge hts
      have hflip := hNoise w₀ u hw00 hst α
      have hstTime : t - s ≤ 0 := by dsimp [u, w₀] at hts; linarith
      simpa [norm_sub_rev, u, w₀, abs_of_nonpos hstTime] using hflip
  have htimeSq : |t - s| ^ 2 ≤ H * |t - s| := by
    nlinarith [abs_nonneg (t - s), htime]
  calc
    _ = ‖fp81s21_initialGaussianFeature p R hK (a + t) φ -
          fp81s21_initialGaussianFeature p R hK (a + s) φ‖ ^ 2 +
        ‖movingNoiseFeature R 0 (a + t) φ -
          movingNoiseFeature R 0 (a + s) φ‖ ^ 2 := hpair
    _ ≤ (B * s104_b p.d α) ^ 2 * |t - s| ^ 2 +
          2 * p.β⁻¹ * (gN ^ 2 + 2 * g * g' / c) *
            (s104_b p.d α) ^ 2 * |t - s| :=
          add_le_add hinit hnoiseSymm
    _ ≤ L α * |t - s| := by
      dsimp [L, C]
      have hb0 : 0 ≤ s104_b p.d α := s104_b_nonneg α
      have hcoef : 0 ≤ (B * s104_b p.d α) ^ 2 := sq_nonneg _
      calc
        _ ≤ (B * s104_b p.d α) ^ 2 * (H * |t - s|) +
              2 * p.β⁻¹ * (gN ^ 2 + 2 * g * g' / c) *
                (s104_b p.d α) ^ 2 * |t - s| := by
          exact add_le_add (mul_le_mul_of_nonneg_left htimeSq hcoef) le_rfl
        _ = (B ^ 2 * H +
              2 * p.β⁻¹ * (gN ^ 2 + 2 * g * g' / c)) *
              (s104_b p.d α) ^ 2 * |t - s| := by ring
        _ = _ := by ring

#print axioms fp81s21_gaussian_combined_feature_increment_bound

end HRS.Fp81.S21

end
