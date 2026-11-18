import HRS.MS.Fp81S21CovClose2

/-! The full interval contract, with its variation constant explicit. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set Classical Filter Topology
open scoped ENNReal NNReal BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.Uniform HRS.Uniform.Q45 HRS.MS.CovMeas HRS.MS.FixEq
open HRS.MS.R2Interp

def fp81s21_covariance_interval_contract
    {d : ℕ} {C : WholeCoeff d} {m H a : ℝ} {r : ℕ} {P : ℝ}
    {z z' : ℝ → (Euc d → ℝ) → ℝ} {Cmix cdec c : ℝ}
    (D : fp81s21_WindowLocalInput C m H a r P z Cmix cdec)
    (D' : fp81s21_WindowLocalInput C m H a r P z' Cmix cdec)
    (Dsum : fp81s21_WindowLocalInput C m H a r P (z + z') Cmix cdec)
    (Dsmul : fp81s21_WindowLocalInput C m H a r P (c • z) Cmix cdec)
    (K q s : ℝ) : Prop :=
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
              (Real.exp (-2 * cdec * max (a - v) 0))).toReal)

#print axioms fp81s21_covariance_interval_contract
end HRS.Fp81.S21
end
