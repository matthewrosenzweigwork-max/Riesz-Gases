import HRS.MS.Fp81S21ShiftedMild4

/-!
# HRS S2.1(iii), packet 9c: shifted-window covariation trace

The finite-particle `hsCovForm` has a trace equal to the sum of squared
feature coordinates. A uniform feature bound cancels the particle
normalization `1/N`; integration is over the local window `[0,H]`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R2GenInit HRS.MS.R26T3
open HRS.MP.RdRem

/-- Pointwise trace bound for the shifted Hilbert covariation. The constant is
independent of `N` and of the shift `b`, provided `B` bounds the feature
uniformly over the translated interval. -/
theorem fp81s21_shiftedNoise_trace_pointwise
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A)
    {H b : ℝ} (hH : 0 < H) (hb : 0 ≤ b)
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ a r, r ∈ Icc (0 : ℝ) (b + H) → ∀ x,
      ‖fp81s21_shiftedNoiseFeatureFamily p R H b a r x‖ ≤ B)
    (u : ℝ) (hu : u ∈ Icc (0 : ℝ) H) (ζ : A.Ω) :
    traceNormForm (hsCovForm
      (s105Phi (fp81s21_shiftedNoiseLocalFeatureFamily p R H b) H p.β⁻¹
        (HRS.Whole.S79.s79p_shiftX b.toNNReal F.X) u ζ)) ≤
      2 * p.β⁻¹ * (p.d : ℝ) * B ^ 2 := by
  let Γ := fp81s21_shiftedNoiseLocalFeatureFamily p R H b
  let Xb := HRS.Whole.S79.s79p_shiftX b.toNNReal F.X
  let Φ := s105Phi Γ H p.β⁻¹ Xb
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hq : 0 ≤ p.β⁻¹ := le_of_lt (inv_pos.mpr p.hβ)
  have hrat : 0 ≤ 2 * p.β⁻¹ / (N : ℝ) := div_nonneg (by positivity) hNpos.le
  have hs : 0 ≤ Real.sqrt (2 * p.β⁻¹ / (N : ℝ)) := Real.sqrt_nonneg _
  have hnorm : ∀ ia : Fin N × Fin p.d,
      ‖Φ u ζ ia‖ ≤ Real.sqrt (2 * p.β⁻¹ / (N : ℝ)) * B := by
    intro ia
    have hu' : mrrClamp H u ∈ Icc (0 : ℝ) H := mrrClamp_mem hH.le u
    have hphys : b + mrrClamp H u ∈ Icc (0 : ℝ) (b + H) := by
      constructor <;> linarith [hu'.1, hu'.2]
    have hfeat : ‖Γ ia.2 (mrrClamp H u) (Xb (Real.toNNReal u) ζ ia.1)‖ ≤ B := by
      change ‖fp81s21_shiftedNoiseFeatureFamily p R H b ia.2
        (b + mrrClamp H u) (Xb (Real.toNNReal u) ζ ia.1)‖ ≤ B
      exact hbound ia.2 (b + mrrClamp H u) hphys _
    change ‖Real.sqrt (2 * p.β⁻¹ / (N : ℝ)) •
      Γ ia.2 (mrrClamp H u) (Xb (Real.toNNReal u) ζ ia.1)‖ ≤ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs]
    exact mul_le_mul_of_nonneg_left hfeat hs
  have hratio : ((N * p.d : ℕ) : ℝ) *
      (Real.sqrt (2 * p.β⁻¹ / (N : ℝ)) * B) ^ 2 =
      2 * p.β⁻¹ * (p.d : ℝ) * B ^ 2 := by
    push_cast
    rw [mul_pow, Real.sq_sqrt hrat]
    field_simp [ne_of_gt hNpos]
  calc
    traceNormForm (hsCovForm (Φ u ζ)) = ∑' ia : Fin N × Fin p.d, ‖Φ u ζ ia‖ ^ 2 :=
      HRS.Uniform.Q07c.traceNormForm_hsCovForm_eq Summable.of_finite
    _ = ∑ ia : Fin N × Fin p.d, ‖Φ u ζ ia‖ ^ 2 := by rw [tsum_fintype]
    _ ≤ ∑ _ia : Fin N × Fin p.d,
        (Real.sqrt (2 * p.β⁻¹ / (N : ℝ)) * B) ^ 2 := by
      refine Finset.sum_le_sum fun ia _ => ?_
      have hh := hnorm ia
      have hsB : 0 ≤ Real.sqrt (2 * p.β⁻¹ / (N : ℝ)) * B := mul_nonneg hs hB
      nlinarith [norm_nonneg (Φ u ζ ia)]
    _ = ((N * p.d : ℕ) : ℝ) *
        (Real.sqrt (2 * p.β⁻¹ / (N : ℝ)) * B) ^ 2 := by
      simp [Finset.sum_const, Finset.card_univ]
    _ = 2 * p.β⁻¹ * (p.d : ℝ) * B ^ 2 := hratio

/-- The local bracket integral is bounded by `H` times the pointwise trace
constant, almost surely. The feature bound `B` is uniform over `b`; the
formula contains neither `N` nor `b`. -/
theorem fp81s21_shiftedNoise_trace_integral
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A)
    {H b : ℝ} (hH : 0 < H) (hb : 0 ≤ b)
    (hphysical : S105Feat p.d ((wholeSpaceIndex p.d : ℕ) : ℝ) H (b + H)
      (fp81s21_shiftedNoiseFeatureFamily p R H b))
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ a r, r ∈ Icc (0 : ℝ) (b + H) → ∀ x,
      ‖fp81s21_shiftedNoiseFeatureFamily p R H b a r x‖ ≤ B) :
    ∀ᵐ ζ ∂A.P,
      ∫ u in Icc (0 : ℝ) H, traceNormForm (hsCovForm
        (s105Phi (fp81s21_shiftedNoiseLocalFeatureFamily p R H b) H p.β⁻¹
          (HRS.Whole.S79.s79p_shiftX b.toNNReal F.X) u ζ)) ≤
        H * (2 * p.β⁻¹ * (p.d : ℝ) * B ^ 2) := by
  obtain ⟨M, -, hHM⟩ := fp81s21_shiftedNoise_feature_martingale
    p R hN A F hH hb hphysical
  have hconst : IntegrableOn (fun _ : ℝ => 2 * p.β⁻¹ * (p.d : ℝ) * B ^ 2)
      (Icc (0 : ℝ) H) := integrableOn_const (by simp [Real.volume_Icc])
  filter_upwards [hHM.sigma_pathint] with ζ hInt
  calc
    ∫ u in Icc (0 : ℝ) H, traceNormForm (hsCovForm
        (s105Phi (fp81s21_shiftedNoiseLocalFeatureFamily p R H b) H p.β⁻¹
          (HRS.Whole.S79.s79p_shiftX b.toNNReal F.X) u ζ))
      ≤ ∫ u in Icc (0 : ℝ) H, 2 * p.β⁻¹ * (p.d : ℝ) * B ^ 2 :=
        setIntegral_mono_on hInt (by simpa using hconst) measurableSet_Icc fun u hu =>
          fp81s21_shiftedNoise_trace_pointwise p R hN A F hH hb B hB hbound u hu ζ
    _ = H * (2 * p.β⁻¹ * (p.d : ℝ) * B ^ 2) := by
      rw [setIntegral_const]
      simp [hH.le, mul_comm]

#print axioms HRS.Fp81.S21.fp81s21_shiftedNoise_trace_pointwise
#print axioms HRS.Fp81.S21.fp81s21_shiftedNoise_trace_integral

end HRS.Fp81.S21

end
