import HRS.MH.AdjRdE3R3
import HRS.MS.SA12X2R34A

/-!
# S.A.12 R36 (SA12X2), part W0: kernel-side integration by parts (Fubini)

For a `C^1` kernel `Kf`, a `C^1_c` test function `φ` and a continuous compactly supported `G`:
`∫ ∂_eφ(x) (∫ Kf(x-y) G(y) dy) dx = -∫ φ(x) (∫ ∂_eKf(x-y) G(y) dy) dx`.
This moves the derivative of the weak pairing onto the test function (R36 weak route, W2/W3).
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12

variable {d : ℕ}

theorem sa12x2_fderiv_sub {Kf : Euc d → ℝ} (hK : ContDiff ℝ 1 Kf) (x y e : Euc d) :
    fderiv ℝ (fun x => Kf (x - y)) x e = fderiv ℝ Kf (x - y) e := by
  have h1 : HasFDerivAt (fun x : Euc d => Kf (x - y)) ((fderiv ℝ Kf (x - y)).comp
      (ContinuousLinearMap.id ℝ (Euc d))) x :=
    ((hK.differentiable one_ne_zero) (x - y)).hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const y)
  rw [h1.fderiv]
  simp

theorem sa12x2_ibp_kernel {Kf : Euc d → ℝ} (hK : ContDiff ℝ 1 Kf) {φ G : Euc d → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (hG : Continuous G)
    (hGc : HasCompactSupport G) (e : Euc d) :
    ∫ x, fderiv ℝ φ x e * ∫ y, Kf (x - y) * G y =
      -∫ x, φ x * ∫ y, fderiv ℝ Kf (x - y) e * G y := by
  have hdφ : Continuous (fun x => fderiv ℝ φ x e) :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hKc : Continuous Kf := hK.continuous
  have hdφc : HasCompactSupport (fun x => fderiv ℝ φ x e) := hφc.fderiv_apply ℝ e
  have hdK : Continuous (fun z => fderiv ℝ Kf z e) :=
    (hK.continuous_fderiv one_ne_zero).clm_apply continuous_const
  -- integrability on the product, for the swaps
  have hint1 : Integrable (fun p : Euc d × Euc d =>
      fderiv ℝ φ p.1 e * (Kf (p.1 - p.2) * G p.2)) (volume.prod volume) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (hdφ.comp continuous_fst).mul ((hKc.comp (continuous_fst.sub continuous_snd)).mul
        (hG.comp continuous_snd))
    · refine HasCompactSupport.intro ((hdφc.isCompact).prod hGc.isCompact) fun p hp => ?_
      by_cases h1 : p.1 ∈ tsupport (fun x => fderiv ℝ φ x e)
      · have h2 : p.2 ∉ tsupport G := fun h2 => hp (mk_mem_prod h1 h2)
        simp [image_eq_zero_of_notMem_tsupport h2]
      · simp [image_eq_zero_of_notMem_tsupport h1]
  have hint2 : Integrable (fun p : Euc d × Euc d =>
      φ p.1 * (fderiv ℝ Kf (p.1 - p.2) e * G p.2)) (volume.prod volume) := by
    refine Continuous.integrable_of_hasCompactSupport ?_ ?_
    · exact (hφ.continuous.comp continuous_fst).mul ((hdK.comp (continuous_fst.sub continuous_snd)).mul
        (hG.comp continuous_snd))
    · refine HasCompactSupport.intro (hφc.isCompact.prod hGc.isCompact) fun p hp => ?_
      by_cases h1 : p.1 ∈ tsupport φ
      · have h2 : p.2 ∉ tsupport G := fun h2 => hp (mk_mem_prod h1 h2)
        simp [image_eq_zero_of_notMem_tsupport h2]
      · simp [image_eq_zero_of_notMem_tsupport h1]
  -- the one-dimensional integration by parts in x, for each y
  have hib : ∀ y : Euc d, ∫ x, fderiv ℝ φ x e * Kf (x - y) =
      -∫ x, φ x * fderiv ℝ Kf (x - y) e := by
    intro y
    have hg : ContDiff ℝ 1 (fun x => Kf (x - y)) := hK.comp (contDiff_id.sub contDiff_const)
    have := HRS.MH.AdjointRdP.r3_ibp_cs e hφ hg hφc
    simp only [sa12x2_fderiv_sub hK] at this
    linarith
  calc ∫ x, fderiv ℝ φ x e * ∫ y, Kf (x - y) * G y
      = ∫ x, ∫ y, fderiv ℝ φ x e * (Kf (x - y) * G y) := by
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        exact (integral_const_mul _ _).symm
    _ = ∫ y, ∫ x, fderiv ℝ φ x e * (Kf (x - y) * G y) :=
        integral_integral_swap hint1
    _ = ∫ y, -(G y * ∫ x, φ x * fderiv ℝ Kf (x - y) e) := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        dsimp only
        have h := hib y
        calc ∫ x, fderiv ℝ φ x e * (Kf (x - y) * G y)
            = G y * ∫ x, fderiv ℝ φ x e * Kf (x - y) := by
              rw [← integral_const_mul]
              exact integral_congr_ae (Eventually.of_forall fun x => by ring)
          _ = G y * -∫ x, φ x * fderiv ℝ Kf (x - y) e := by rw [h]
          _ = -(G y * ∫ x, φ x * fderiv ℝ Kf (x - y) e) := by ring
    _ = -∫ y, ∫ x, φ x * (fderiv ℝ Kf (x - y) e * G y) := by
        rw [← integral_neg]
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        dsimp only
        rw [← integral_const_mul]
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        ring
    _ = -∫ x, ∫ y, φ x * (fderiv ℝ Kf (x - y) e * G y) := by
        congr 1
        exact (integral_integral_swap hint2).symm
    _ = -∫ x, φ x * ∫ y, fderiv ℝ Kf (x - y) e * G y := by
        congr 1
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        exact (integral_const_mul _ _)

end HRS.MH.AdjointRd.Phase2SA12
