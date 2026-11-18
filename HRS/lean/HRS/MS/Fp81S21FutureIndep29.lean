import HRS.MS.Fp81S21FutureIndep28
import HRS.MS.Fp81S21FutureIndep11

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory ProbabilityTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.ProClosureS111

/-- Propagated tests need not themselves be oscillator tests: their noise
kernel is nevertheless the past restriction of the original test's kernel. -/
theorem fp81s21_propagated_noise_feature
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδhalf : δ ≤ 1 / 2) (hH : 0 < H)
    {r t : ℝ} (hr : r ∈ Icc (0 : ℝ) H) (ht : t ∈ Icc (0 : ℝ) H)
    (hrt : r ≤ t) {φ : Euc p.d → ℝ}
    (hφ : IsOscTest (wholeSpaceIndex p.d : ℝ) φ) :
    MemLp (movingNoiseKernel R 0 r (propagatorW (r26t3_coeff R) r t φ)) 2
      ((volume : Measure ℝ).prod (volume : Measure (Euc p.d))) ∧
    movingNoiseFeature R 0 r (propagatorW (r26t3_coeff R) r t φ) =
      movingNoiseFeature R 0 t φ - movingNoiseFeature R r t φ := by
  let μ : Measure (ℝ × Euc p.d) :=
    (volume : Measure ℝ).prod (volume : Measure (Euc p.d))
  let F : MovingNoiseHilbert p.d := movingNoiseFeature R 0 t φ - movingNoiseFeature R r t φ
  have hp : (F : ℝ × Euc p.d → Euc p.d) =ᵐ[μ]
      fun q => if q.1 ≤ r then movingNoiseKernel R 0 t φ q else 0 :=
    fp81s21_movingNoise_past_feature_ae p R hδ hδhalf hH hr ht hφ
  have hk : ∀ q : ℝ × Euc p.d,
      (if q.1 ≤ r then movingNoiseKernel R 0 t φ q else 0) =
        movingNoiseKernel R 0 r (propagatorW (r26t3_coeff R) r t φ) q := by
    intro q
    by_cases hq : q.1 ∈ Icc (0 : ℝ) r
    · have hqt : q.1 ∈ Icc (0 : ℝ) t := ⟨hq.1, hq.2.trans hrt⟩
      have hc := fp81s21_moving_propagator_comp p R hq.1 hq.2 hrt hφ
      have hc' : r26t3_U R q.1 r (propagatorW (r26t3_coeff R) r t φ) =
          r26t3_U R q.1 t φ := by simpa only [r26t3_U] using hc
      simp [movingNoiseKernel, hq.2, hq, hqt, hc']
    · by_cases hqr : q.1 ≤ r
      · have hn : q.1 ∉ Icc (0 : ℝ) t := by
          intro hm
          exact hq ⟨hm.1, hqr⟩
        simp [movingNoiseKernel, hqr, hq, hn]
      · simp [movingNoiseKernel, hqr, hq]
  have hae : (F : ℝ × Euc p.d → Euc p.d) =ᵐ[μ]
      movingNoiseKernel R 0 r (propagatorW (r26t3_coeff R) r t φ) :=
    hp.trans (Filter.Eventually.of_forall hk)
  have hmem : MemLp (movingNoiseKernel R 0 r (propagatorW (r26t3_coeff R) r t φ)) 2 μ :=
    (memLp_congr_ae hae).1 (Lp.memLp F)
  refine ⟨hmem, ?_⟩
  change movingNoiseFeature R 0 r (propagatorW (r26t3_coeff R) r t φ) = F
  rw [movingNoiseFeature, dif_pos hmem]
  apply Lp.ext
  exact hmem.coeFn_toLp.trans hae.symm

#print axioms fp81s21_propagated_noise_feature
end HRS.Fp81.S21
end
