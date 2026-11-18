import HRS.MS.Fp81S21CovClose

/-!
# S2.1(iii), packet 16-close: assembled public covariance contract

This theorem collects the interval-value, field-linearity, continuity,
coordinate, symmetry, and cumulative-variation facts at the shared
`WindowLocalInput` interface.  The `D`/block hypotheses have exactly the
shape returned by the one-input physical wrapper; field inputs use the same
localization constants, with dual-norm measurability stated separately for
all four fields.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set Classical Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45 HRS.MS.CovMeas HRS.MS.FixEq
open HRS.MS.R2Interp

theorem fp81s21_window_covariance_measure_spec
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z z' : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec c : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    (D' : fp81s21_WindowLocalInput C m H a r P z' Cmix cdec)
    (Dsum : fp81s21_WindowLocalInput C m H a r P (z + z') Cmix cdec)
    (Dsmul : fp81s21_WindowLocalInput C m H a r P (c • z) Cmix cdec)
    (hlin : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ a + H →
      ∀ φ ψ : Euc d → ℝ, ∀ b : ℝ,
        IsR2DualCombo m φ → IsR2DualCombo m ψ →
        propagatorW C u t (φ + b • ψ) =
          propagatorW C u t φ + b • propagatorW C u t ψ)
    (hblocks : ∀ I : Set ℝ, MeasurableSet I → ∀ k,
      fp81s21_WindowCovarianceBlockContract D hlin I k)
    (hblocks' : ∀ I : Set ℝ, MeasurableSet I → ∀ k,
      fp81s21_WindowCovarianceBlockContract D' hlin I k)
    (hblocksSum : ∀ I : Set ℝ, MeasurableSet I → ∀ k,
      fp81s21_WindowCovarianceBlockContract Dsum hlin I k)
    (hblocksSmul : ∀ I : Set ℝ, MeasurableSet I → ∀ k,
      fp81s21_WindowCovarianceBlockContract Dsmul hlin I k)
    (hdual : AEMeasurable (fun v => dualNormE r P (z v))
      (volume.restrict (Icc (0 : ℝ) (a + H))))
    (hdual' : AEMeasurable (fun v => dualNormE r P (z' v))
      (volume.restrict (Icc (0 : ℝ) (a + H))))
    (hdualSum : AEMeasurable (fun v => dualNormE r P ((z + z') v))
      (volume.restrict (Icc (0 : ℝ) (a + H))))
    (hdualSmul : AEMeasurable (fun v => dualNormE r P ((c • z) v))
      (volume.restrict (Icc (0 : ℝ) (a + H))))
    {q s : ℝ} (hq : 0 ≤ q) (hqs : q ≤ s) (hs : s ≤ a + H) :
    let K : ℝ :=
      ((3 + Real.sqrt H) ^ 2 * fp81s21_blockC0) * |2 * C.ν| *
        (s57pC d r P * ((d : ℝ) * 2 ^ r *
          (fp81s21_windowCovBlockAmp d r H Cmix) ^ 2))
    0 ≤ K ∧
      ENNReal.ofReal K < ∞ ∧
      (∀ t, s ≤ t →
        fp81s21_window_covariance_measure D q t =
          fp81s21_window_covariance_measure D q s +
            fp81s21_window_covariance_measure D s t) ∧
      fp81s21_window_covariance_measure D q q = 0 ∧
      fp81s21_window_covariance_measure Dsum q s =
        fp81s21_window_covariance_measure D q s +
          fp81s21_window_covariance_measure D' q s ∧
      fp81s21_window_covariance_measure Dsmul q s =
        c • fp81s21_window_covariance_measure D q s ∧
      ContinuousOn (fun t => fp81s21_window_covariance_measure D q t) (Icc q s) ∧
      fp81s21_IsWindowJValue C m H a z (Ioc q s)
        ((fp81s21_window_covariance_measure D q s : projTensor (OscPath d m H) 2) :
          TensorDual (OscPath d m H) 2) ∧
      (∀ M : OscPath d m H [×2]→L[ℝ] ℝ,
        Summable (fun k : ℕ =>
          ((fp81s21_blockValue D (Ioc q s) k : projTensor (OscPath d m H) 2) :
            TensorDual (OscPath d m H) 2) M) ∧
        ((fp81s21_window_covariance_cumulative D q s : projTensor (OscPath d m H) 2) :
          TensorDual (OscPath d m H) 2) M =
          ∑' k : ℕ,
            ((fp81s21_blockValue D (Ioc q s) k : projTensor (OscPath d m H) 2) :
              TensorDual (OscPath d m H) 2) M) ∧
      (((fp81s21_window_covariance_cumulative D q s : projTensor (OscPath d m H) 2) :
          TensorDual (OscPath d m H) 2) ∈ projTensor (OscPath d m H) 2 ∧
      Tendsto (fun L => HRS.Sec7.tensorPow 2 (s102_Pj H D.fp81s21_hH L)
        ((fp81s21_window_covariance_cumulative D q s : projTensor (OscPath d m H) 2) :
          TensorDual (OscPath d m H) 2)) atTop
        (𝓝 ((fp81s21_window_covariance_cumulative D q s : projTensor (OscPath d m H) 2) :
          TensorDual (OscPath d m H) 2)) ∧
      (∀ M : OscPath d m H [×2]→L[ℝ] ℝ,
        ((fp81s21_window_covariance_cumulative D q s : projTensor (OscPath d m H) 2) :
          TensorDual (OscPath d m H) 2) M =
        ((fp81s21_window_covariance_cumulative D q s : projTensor (OscPath d m H) 2) :
          TensorDual (OscPath d m H) 2) (M.domDomCongr (Equiv.swap 0 1)))) ∧
      (eVariationOn (fp81s21_window_covariance_cumulative D q) (Icc q s) ≤
          ENNReal.ofReal (K * (∫⁻ v in Ioc q s,
            dualNormE r P (z v) * ENNReal.ofReal
              (Real.exp (-2 * cdec * max (a - v) 0))).toReal) ∧
        (eVariationOn (fp81s21_window_covariance_cumulative D q) (Icc q s)).toReal ≤
          K * (∫⁻ v in Ioc q s,
            dualNormE r P (z v) * ENNReal.ofReal
              (Real.exp (-2 * cdec * max (a - v) 0))).toReal) := by
  dsimp only
  let A : ℝ := (3 + Real.sqrt H) ^ 2 * fp81s21_blockC0
  let B : ℝ := |2 * C.ν|
  let C0 : ℝ := s57pC d r P * ((d : ℝ) * 2 ^ r *
    (fp81s21_windowCovBlockAmp d r H Cmix) ^ 2)
  let K : ℝ := A * B * C0
  have hA : 0 ≤ A := by
    dsimp [A]
    apply mul_nonneg
    · positivity
    · exact fp81s21_blockC0_nonneg
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC0 : 0 ≤ C0 := by
    dsimp [C0]
    exact mul_nonneg (s57pC_nonneg d r P) (by positivity)
  have hK : 0 ≤ K := by
    dsimp [K]
    exact mul_nonneg (mul_nonneg hA hB) hC0
  refine ⟨hK, ENNReal.ofReal_lt_top, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t hst
    exact fp81s21_window_covariance_measure_add D hlin hblocks hdual hqs hst
  · exact fp81s21_window_covariance_measure_diagonal D q
  · exact fp81s21_window_covariance_measure_add_field D D' Dsum hlin
      hblocks hblocks' hblocksSum hdual hdual' hdualSum q s
  · exact fp81s21_window_covariance_measure_smul_field D Dsmul hlin
      hblocks hblocksSmul hdual hdualSmul q s
  · exact fp81s21_window_covariance_measure_cumulative_continuousOn
      D hlin hblocks hdual hq hqs hs
  · exact fp81s21_window_covariance_measure_isWindowJValue
      D hlin hblocks hdual hq hqs
  · intro M
    exact fp81s21_window_covariance_cumulative_coordinate_tsum
      D hlin hblocks hdual (q0 := q) (u := s) M
  · exact fp81s21_window_covariance_cumulative_projective_symmetric
      D hlin hblocks hdual (q0 := q) (u := s)
  · exact fp81s21_window_covariance_cumulative_eVariationOn_le
      D hlin hblocks hdual hq hqs hs

#print axioms fp81s21_window_covariance_measure_spec

end HRS.Fp81.S21

end
