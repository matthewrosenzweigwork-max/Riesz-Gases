import HRS.MS.S111K3E4

/-!
# S11.1 continuation (S11K3), B03: `window_covariance_BV` (shifted quantitative signed covariance map)

`s111k3_window_covariance_BV` is the Pro contract `window_covariance_BV` (S11.1-BV, B03) with the local copies
`S111k2WindowOrbitInput` (identical fields to the Pro `WindowOrbitInput`), `s111k2_age` (Pro `age`) and `K3ShiftedJValue`
(Pro `ShiftedJValue`).  The constant `K = (3+√T)² C0 KB`, where `C0` is the abstract covariance-measure constant at horizon `2T`
(depends on `T` only), `KB = s57pC · d 2^r K1²` and `K1` the window-feature constant of B02, does not depend on `u`, `C`, `b`.
Route: the past `[0,u]` of the forcing history is compressed linearly onto `[0,T]` and the window `[u,u+T]` is translated onto
`[T,2T]`; the abstract covariance measure of `HRS.Uniform.covariance_measure_proof` at horizon `2T` is pushed forward by the shifted
reconstruction `A_{2T} + ∫ B_{2T} - C_{2T} + C_{T+t}` (norm `≤ 3 + √T`).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K3

open HRS HRS.Whole HRS.MS.CovMeas HRS.MS.S111K2 HRS.MS.S111K HRS.MS.FixEq

theorem s111k3_window_covariance_BV (d r : ℕ) (hd : 2 ≤ d)
    (m T Pw S c0 : ℝ) (hT : 0 < T) (hPw : (d : ℝ) / 2 < Pw)
    (hS : 0 ≤ S) (hc0 : 0 < c0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ C : WholeCoeff d,
      ∀ b : MultiIndex d → ℝ, Summable (fun alpha => b alpha ^ 2) →
      (∑' alpha, b alpha ^ 2) ≤ S → S111k2WindowOrbitInput C m c0 r b →
      ∀ u : ℝ, 0 ≤ u →
        ∃ J : (ℝ → (Euc d → ℝ) → ℝ) → ℝ → ℝ → projTensor (OscPath d m T) 2,
          (∀ z z', IsR2L1F r Pw (u + T) z → IsR2L1F r Pw (u + T) z' →
            R2JIntegrandMeas C m (u + T) z → R2JIntegrandMeas C m (u + T) z' →
            ∀ a b, J (z + z') a b = J z a b + J z' a b) ∧
          (∀ (c : ℝ) z, IsR2L1F r Pw (u + T) z →
            R2JIntegrandMeas C m (u + T) z →
            ∀ a b, J (c • z) a b = c • J z a b) ∧
          ∀ z, IsR2L1F r Pw (u + T) z → R2JIntegrandMeas C m (u + T) z →
            (∀ a, J z a a = 0) ∧
            (∀ a b c, 0 ≤ a → a ≤ b → b ≤ c → c ≤ u + T → J z a c = J z a b + J z b c) ∧
            ContinuousOn (fun v => J z 0 v) (Set.Icc 0 (u + T)) ∧
            eVariationOn (fun v => J z 0 v) (Set.Icc 0 (u + T)) ≤
              ENNReal.ofReal (K * |2 * C.ν|) *
                ∫⁻ v in Set.Icc 0 (u + T),
                  ENNReal.ofReal (s111k2_age c0 u v ^ 2) * dualNormE r Pw (z v) ∧
            ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ u + T →
              K3ShiftedJValue C m T u z a b (J z a b) ∧
              ‖J z a b‖ₑ ≤ ENNReal.ofReal (K * |2 * C.ν|) *
                ∫⁻ v in Set.Ioc a b, ENNReal.ofReal (s111k2_age c0 u v ^ 2) * dualNormE r Pw (z v) := by
  obtain ⟨C0, hC0, Jabs, hJ⟩ := k3_J_exists (d := d) (m := m) hT
  obtain ⟨K1, hK1, hB⟩ := s111k2_window_feature_bounds d r m T S c0 hT hS hc0
  refine ⟨(3 + Real.sqrt T) ^ 2 * C0 * k3KB d r Pw K1,
    mul_nonneg (mul_nonneg (by positivity) hC0) (k3KB_nonneg d r Pw K1), ?_⟩
  intro C b hbS hbSS hW u hu
  have hd1 : 1 ≤ d := by omega
  have c : K3Ctx C m T u c0 r b Pw K1 :=
    ⟨hd1, by linarith, hW, hbS, hc0.le, hu, hT.le, hK1, fun v hv i => hB C b hbS hbSS hW u hu v hv i⟩
  refine ⟨k3Jm hT.le Jabs C u r Pw, ?_, ?_, ?_⟩
  · intro z z' hz hz' hm hm' a a'
    exact k3Jm_add hT c hJ (k3_admP_of_L1F c hz hm) (k3_admP_of_L1F c hz' hm') a a'
  · intro cc z hz hm a a'
    exact k3Jm_smul hT c hJ cc (k3_admP_of_L1F c hz hm) a a'
  · intro z hz hm
    have h := k3_admP_of_L1F c hz hm
    refine ⟨fun a => k3Jm_self hT c h a, fun a a' a'' ha haa haa' _ => k3Jm_add_interval hT c h ha haa haa',
      k3Jm_cont hT c hJ h, k3Jm_var hT c hJ hC0 h, fun a a' ha haa haH => ⟨?_, ?_⟩⟩
    · exact k3Jm_value hT c hJ h ha haa haH
    · exact k3Jm_interval_bound hT c hJ hC0 h ha haa haH

end HRS.MS.S111K3
