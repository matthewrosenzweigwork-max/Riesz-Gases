import HRS.MS.Fp81S21CovMeasure

/-!
# S2.1(iii), packet 16d: linearity of interval covariance sums

Linearity is stated for localized inputs of the original, transformed, and
combined fields.  AEMeasurability of each dual-norm density, including the
combined field, is explicit because it is needed for the block-sum theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45 HRS.MS.CovMeas

/-- The interval covariance sum is additive in the source field. -/
theorem fp81s21_window_covariance_measure_add_field
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z z' : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    (D' : fp81s21_WindowLocalInput C m H a r P z' Cmix cdec)
    (Dsum : fp81s21_WindowLocalInput C m H a r P (z + z') Cmix cdec)
    (hlin : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ a + H →
      ∀ φ ψ : Euc d → ℝ, ∀ c : ℝ,
        IsR2DualCombo m φ → IsR2DualCombo m ψ →
        propagatorW C u t (φ + c • ψ) =
          propagatorW C u t φ + c • propagatorW C u t ψ)
    (hblocks : ∀ I : Set ℝ, MeasurableSet I → ∀ k,
      fp81s21_WindowCovarianceBlockContract D hlin I k)
    (hblocks' : ∀ I : Set ℝ, MeasurableSet I → ∀ k,
      fp81s21_WindowCovarianceBlockContract D' hlin I k)
    (hblocksSum : ∀ I : Set ℝ, MeasurableSet I → ∀ k,
      fp81s21_WindowCovarianceBlockContract Dsum hlin I k)
    (hdual : AEMeasurable (fun v => dualNormE r P (z v))
      (volume.restrict (Icc (0 : ℝ) (a + H))))
    (hdual' : AEMeasurable (fun v => dualNormE r P (z' v))
      (volume.restrict (Icc (0 : ℝ) (a + H))))
    (hdualSum : AEMeasurable (fun v => dualNormE r P ((z + z') v))
      (volume.restrict (Icc (0 : ℝ) (a + H))))
    (q s : ℝ) :
    fp81s21_window_covariance_measure Dsum q s =
      fp81s21_window_covariance_measure D q s +
        fp81s21_window_covariance_measure D' q s := by
  let f : ℕ → projTensor (OscPath d m H) 2 :=
    fun k => fp81s21_blockValue D (Ioc q s) k
  let f' : ℕ → projTensor (OscPath d m H) 2 :=
    fun k => fp81s21_blockValue D' (Ioc q s) k
  let fsum : ℕ → projTensor (OscPath d m H) 2 :=
    fun k => fp81s21_blockValue Dsum (Ioc q s) k
  have hsum := fp81s21_window_covariance_blocks_tsum_weighted D hlin
    (Ioc q s) measurableSet_Ioc (fun k => hblocks (Ioc q s) measurableSet_Ioc k) hdual
  have hsum' := fp81s21_window_covariance_blocks_tsum_weighted D' hlin
    (Ioc q s) measurableSet_Ioc (fun k => hblocks' (Ioc q s) measurableSet_Ioc k) hdual'
  have hsumSum := fp81s21_window_covariance_blocks_tsum_weighted Dsum hlin
    (Ioc q s) measurableSet_Ioc
    (fun k => hblocksSum (Ioc q s) measurableSet_Ioc k) hdualSum
  have hs : Summable f := Summable.of_enorm (ne_top_of_lt hsum.2.1)
  have hs' : Summable f' := Summable.of_enorm (ne_top_of_lt hsum'.2.1)
  have hssum : Summable fsum := Summable.of_enorm (ne_top_of_lt hsumSum.2.1)
  have hblock : ∀ k, fsum k = f k + f' k := by
    intro k
    exact fp81s21_blockValue_add D D' Dsum measurableSet_Ioc k
  change (∑' k, fsum k) = (∑' k, f k) + ∑' k, f' k
  calc
    (∑' k, fsum k) = ∑' k, (f k + f' k) := tsum_congr hblock
    _ = (∑' k, f k) + ∑' k, f' k := hs.tsum_add hs'

/-- The interval covariance sum scales with the source field. -/
theorem fp81s21_window_covariance_measure_smul_field
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P c : ℝ}
    {z : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    (Dsmul : fp81s21_WindowLocalInput C m H a r P (c • z) Cmix cdec)
    (hlin : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ a + H →
      ∀ φ ψ : Euc d → ℝ, ∀ c' : ℝ,
        IsR2DualCombo m φ → IsR2DualCombo m ψ →
        propagatorW C u t (φ + c' • ψ) =
          propagatorW C u t φ + c' • propagatorW C u t ψ)
    (hblocks : ∀ I : Set ℝ, MeasurableSet I → ∀ k,
      fp81s21_WindowCovarianceBlockContract D hlin I k)
    (hblocksSmul : ∀ I : Set ℝ, MeasurableSet I → ∀ k,
      fp81s21_WindowCovarianceBlockContract Dsmul hlin I k)
    (hdual : AEMeasurable (fun v => dualNormE r P (z v))
      (volume.restrict (Icc (0 : ℝ) (a + H))))
    (hdualSmul : AEMeasurable (fun v => dualNormE r P ((c • z) v))
      (volume.restrict (Icc (0 : ℝ) (a + H))))
    (q s : ℝ) :
    fp81s21_window_covariance_measure Dsmul q s =
      c • fp81s21_window_covariance_measure D q s := by
  let f : ℕ → projTensor (OscPath d m H) 2 :=
    fun k => fp81s21_blockValue D (Ioc q s) k
  let fsmul : ℕ → projTensor (OscPath d m H) 2 :=
    fun k => fp81s21_blockValue Dsmul (Ioc q s) k
  have hsum := fp81s21_window_covariance_blocks_tsum_weighted D hlin
    (Ioc q s) measurableSet_Ioc (fun k => hblocks (Ioc q s) measurableSet_Ioc k) hdual
  have hsumSmul := fp81s21_window_covariance_blocks_tsum_weighted Dsmul hlin
    (Ioc q s) measurableSet_Ioc
    (fun k => hblocksSmul (Ioc q s) measurableSet_Ioc k) hdualSmul
  have hs : Summable f := Summable.of_enorm (ne_top_of_lt hsum.2.1)
  have hssmul : Summable fsmul := Summable.of_enorm (ne_top_of_lt hsumSmul.2.1)
  have hblock : ∀ k, fsmul k = c • f k := by
    intro k
    exact fp81s21_blockValue_smul D Dsmul measurableSet_Ioc k
  change (∑' k, fsmul k) = c • ∑' k, f k
  calc
    (∑' k, fsmul k) = ∑' k, c • f k := tsum_congr hblock
    _ = c • ∑' k, f k := hs.tsum_const_smul c

#print axioms fp81s21_window_covariance_measure_add_field
#print axioms fp81s21_window_covariance_measure_smul_field

end HRS.Fp81.S21

end
