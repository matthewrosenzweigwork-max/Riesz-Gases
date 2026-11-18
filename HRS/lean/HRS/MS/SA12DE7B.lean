import HRS.MS.SA12DE7A
import HRS.MS.SA12V3S
import HRS.MS.SA12V3G
import HRS.MS.SA12V3N

/-!
# S.A.12(c), packet E7.07 (worker S82Z2), part B: mollification converges in `H^m` for `C_c^∞` data

`sa12de7_mollify_unif`: `mollify η ε f → f` uniformly for continuous compactly supported `f`.
`sa12de7_mollify_H`: for `ψ ∈ C_c^∞`, `sobolevNormSq m (mollify η ε ψ - ψ) → 0` as `ε → 0+` (jets commute with
mollification, `sa12v3_H_partial`; the difference is `C_c^∞`, so part A applies).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.SA12DE7

open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MH.AdjointRd
  HRS.MH.AdjointRd.Phase2SA12Limit HRS.MH.AdjointRd.Phase2SA12Construction HRS.MH.AdjointRd.Phase2SA12V3

variable {d : ℕ}

theorem sa12de7_mollify_eq_H (η : Euc d → ℝ) (ε : ℝ) (f : Euc d → ℝ) :
    mollify η ε f = sa12vH (sa12v3_G η ε) f := by
  rw [sa12v3_mollify_eq]; rfl

theorem sa12de7_G_supp {η : Euc d → ℝ} (hη : IsMollifier η) {ε : ℝ} (hε : 0 < ε) {y : Euc d}
    (hy : sa12v3_G η ε y ≠ 0) : ‖y‖ ≤ ε := by
  have h1 : η (ε⁻¹ • y) ≠ 0 := fun h => hy (by simp [sa12v3_G, h])
  have h2 : ε⁻¹ • y ∈ Metric.closedBall (0 : Euc d) 1 := hη.2.2.1 (subset_tsupport _ h1)
  rw [Metric.mem_closedBall, dist_zero_right, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hε] at h2
  have := (inv_mul_le_iff₀ hε).1 h2
  linarith

theorem sa12de7_mollify_unif {η : Euc d → ℝ} (hη : IsMollifier η) {f : Euc d → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ x, |mollify η ε f x - f x| ≤ δ := by
  obtain ⟨ρ, hρ, hρf⟩ := Metric.uniformContinuous_iff.mp (hc.uniformContinuous_of_continuous hf) δ hδ
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hc
  have : Ioo (0 : ℝ) ρ ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT hρ
  filter_upwards [this] with ε hε x
  have hε0 : 0 < ε := hε.1
  have hint : Integrable (sa12v3_G η ε) volume := sa12v3_G_integrable hη hε0
  have hm : AEStronglyMeasurable (fun y => f (x - y)) volume :=
    (hf.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hI1 : Integrable (fun y => sa12v3_G η ε y * f (x - y)) volume :=
    hint.mul_bdd hm (Eventually.of_forall fun y => hC (x - y))
  have hI2 : Integrable (fun y => sa12v3_G η ε y * f x) volume := hint.mul_const _
  have h1 : mollify η ε f x = ∫ y, sa12v3_G η ε y * f (x - y) := rfl
  have e1 : mollify η ε f x - f x = ∫ y, sa12v3_G η ε y * (f (x - y) - f x) := by
    simp_rw [mul_sub]
    rw [integral_sub hI1 hI2, integral_mul_const, sa12v3_G_integral hη hε0, one_mul, h1]
  rw [e1, ← Real.norm_eq_abs]
  have hb := norm_integral_le_of_norm_le (hint.const_mul δ)
    (Eventually.of_forall fun y => ?_) (f := fun y => sa12v3_G η ε y * (f (x - y) - f x))
  · refine hb.trans (le_of_eq ?_)
    rw [integral_const_mul, sa12v3_G_integral hη hε0, mul_one]
  · by_cases hy : sa12v3_G η ε y = 0
    · simp [hy]
    · have hyε := sa12de7_G_supp hη hε0 hy
      have hd : dist (x - y) x < ρ := by
        rw [dist_eq_norm, sub_sub_cancel_left, norm_neg]; linarith [hε.2]
      have h2 := hρf hd
      rw [Real.dist_eq] at h2
      rw [norm_mul, Real.norm_eq_abs (sa12v3_G η ε y), abs_of_nonneg (sa12v3_G_nonneg hη hε0 y),
        Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right h2.le (sa12v3_G_nonneg hη hε0 y)

theorem sa12de7_mollify_supp {η : Euc d → ℝ} (hη : IsMollifier η) {f : Euc d → ℝ} {R ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) (hf : ∀ x, R < ‖x‖ → f x = 0) {x : Euc d} (hx : R + 1 < ‖x‖) : mollify η ε f x = 0 := by
  have : mollify η ε f x = ∫ y, sa12v3_G η ε y * f (x - y) := rfl
  rw [this]
  refine integral_eq_zero_of_ae (Eventually.of_forall fun y => ?_)
  by_cases hy : sa12v3_G η ε y = 0
  · simp [hy]
  · have hyε := sa12de7_G_supp hη hε0 hy
    have h3 := norm_sub_norm_le x y
    have : f (x - y) = 0 := hf _ (by linarith)
    simp [this]

theorem sa12de7_pd_sub {a b : Euc d → ℝ} (ha : ContDiff ℝ ∞ a) (hb : ContDiff ℝ ∞ b) {j : ℕ}
    (idx : Fin j → Fin d) (x : Euc d) :
    partialDeriv idx (fun y => a y - b y) x = partialDeriv idx a x - partialDeriv idx b x := by
  unfold partialDeriv
  have h := iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := j) (x := x)
    (ha.of_le (by exact_mod_cast le_top)).contDiffAt (hb.of_le (by exact_mod_cast le_top)).contDiffAt
  have e : (fun y => a y - b y) = a - b := rfl
  rw [e, h]
  rfl

end HRS.MS.SA12DE7
