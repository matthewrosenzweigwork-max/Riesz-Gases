import HRS.MS.SA12X5D4B

/-!
# S.A.12 X5 D4C: the difference of two mollified periodized normalized densities

`sa12x5_adiff η ζ r₁ r₂ L = η * μ₀(r₁) - η * μ₀(r₂)` (`μ₀ = sa12k_mu0`).  If `r₁ - r₂` has weighted jets `≤ δ`, then `adiff` is
periodic, smooth, with jets (order `≤ n`), nearest-lattice decay and cube integrals all bounded by `δ` times a constant.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12X5

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MS.ToriCoefA HRS.MS.ToriCoefB HRS.MS.ToriConv HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

def sa12x5_adiff (η ζ r₁ r₂ : Euc d → ℝ) (L : ℝ) : Euc d → ℝ := fun x =>
  sa12k_moll η (sa12k_mu0 ζ r₁ L) x - sa12k_moll η (sa12k_mu0 ζ r₂ L) x

def sa12x5_Bfac (d : ℕ) (Kz : ℕ → ℝ) (n : ℕ) (W : ℝ) : ℝ :=
  (∑ j ∈ Finset.range (n + 1), 2 * tca_S d Kz 1 j) * (1 + 4 * (∫ w : Euc d, tca_g w) * W)

theorem sa12x5_cutoff_int {ζ : Euc d → ℝ} (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ) {L : ℝ} (hL : 0 < L)
    {r : Euc d → ℝ} (hr : Continuous r) : Integrable (fun y => ζ (L⁻¹ • y) * r y) := by
  refine Continuous.integrable_of_hasCompactSupport ?_ ?_
  · exact (hζ.1.continuous.comp (continuous_id.const_smul L⁻¹ : Continuous fun y : Euc d => L⁻¹ • y)).mul hr
  · refine HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Euc d) (L / 3)) ?_
    intro y hy
    by_contra hn
    simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hn
    apply hy
    show ζ (L⁻¹ • y) * r y = 0
    rw [tca_zeta_far_val hζ L hL y hn.le, zero_mul]

theorem sa12x5_Z_diff {ζ : Euc d → ℝ} (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ) {L : ℝ} (hL : 0 < L)
    {r₁ r₂ : Euc d → ℝ} (hr₁ : Continuous r₁) (hr₂ : Continuous r₂) {δ : ℝ} (hδ : 0 ≤ δ)
    (hu0 : ∀ y, |r₁ y - r₂ y| ≤ δ * tca_g y) :
    |(∫ y, ζ (L⁻¹ • y) * r₁ y) - ∫ y, ζ (L⁻¹ • y) * r₂ y| ≤ δ * ∫ w : Euc d, tca_g w := by
  rw [← integral_sub (sa12x5_cutoff_int hζ hL hr₁) (sa12x5_cutoff_int hζ hL hr₂), ← integral_const_mul]
  have := norm_integral_le_of_norm_le (tca_g_integrable.const_mul δ)
    (f := fun y => ζ (L⁻¹ • y) * r₁ y - ζ (L⁻¹ • y) * r₂ y) (Filter.Eventually.of_forall fun y => ?_)
  · rwa [Real.norm_eq_abs] at this
  · have hz := hζ.2.2.2.1 (L⁻¹ • y)
    rw [Real.norm_eq_abs, ← mul_sub, abs_mul, abs_of_nonneg hz.1]
    calc ζ (L⁻¹ • y) * |r₁ y - r₂ y| ≤ 1 * (δ * tca_g y) :=
          mul_le_mul hz.2 (hu0 y) (abs_nonneg _) zero_le_one
      _ = _ := one_mul _

theorem sa12x5_inv_diff {Z₁ Z₂ : ℝ} (h1 : 1 / 2 ≤ Z₁) (h2 : 1 / 2 ≤ Z₂) : |Z₁⁻¹ - Z₂⁻¹| ≤ 4 * |Z₁ - Z₂| := by
  have p1 : 0 < Z₁ := by linarith
  have p2 : 0 < Z₂ := by linarith
  have hab : 1 / 4 ≤ Z₁ * Z₂ := by nlinarith
  rw [inv_sub_inv p1.ne' p2.ne', abs_div, abs_of_pos (mul_pos p1 p2), div_le_iff₀ (mul_pos p1 p2),
    abs_sub_comm Z₂ Z₁]
  nlinarith [abs_nonneg (Z₁ - Z₂)]

set_option maxHeartbeats 1600000 in
theorem sa12x5_density_diff {ζ : Euc d → ℝ} (hζ : IsCutoffRad (1 / 4) (1 / 3) ζ) (L : ℝ) (hL : 7 ≤ L)
    {δη : ℝ} {η : Euc d → ℝ} (hη : SA12KMoll δη η) (hδη : δη ≤ 1) (n : ℕ)
    (Kz : ℕ → ℝ) (hKz : ∀ (i : ℕ) (y : Euc d), ‖iteratedFDeriv ℝ i ζ y‖ ≤ Kz i) (hKz0 : ∀ i, 0 ≤ Kz i)
    (r₁ r₂ : Euc d → ℝ) (hr₁ : ContDiff ℝ (n : WithTop ℕ∞) r₁) (hr₂ : ContDiff ℝ (n : WithTop ℕ∞) r₂)
    (W δ : ℝ) (hW0 : 0 ≤ W) (hδ0 : 0 ≤ δ)
    (hW₂ : ∀ k : ℕ, k ≤ n → ∀ w : Euc d,
      jbracket w ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ k r₂ w‖ ≤ (d : ℝ) ^ k * W)
    (hu : ∀ k : ℕ, k ≤ n → ∀ w : Euc d,
      jbracket w ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ k (fun x => r₁ x - r₂ x) w‖ ≤ (d : ℝ) ^ k * δ)
    (hZ₁ : 1 / 2 ≤ ∫ y, ζ (L⁻¹ • y) * r₁ y) (hZ₂ : 1 / 2 ≤ ∫ y, ζ (L⁻¹ • y) * r₂ y) :
    (∀ (x : Euc d) (k : Fin d → ℤ),
        sa12x5_adiff η ζ r₁ r₂ L (x + L • latticePt k) = sa12x5_adiff η ζ r₁ r₂ L x) ∧
      ContDiff ℝ ∞ (sa12x5_adiff η ζ r₁ r₂ L) ∧
      (∀ j ≤ n, ∀ y : Euc d,
        ‖iteratedFDeriv ℝ j (sa12x5_adiff η ζ r₁ r₂ L) y‖ ≤ δ * sa12x5_Bfac d Kz n W) ∧
      (∀ j ≤ n, ∀ x : Euc d, ∃ k : Fin d → ℤ,
        jbracket (x - L • latticePt k) ^ ((d : ℝ) + 3) *
          ‖iteratedFDeriv ℝ j (sa12x5_adiff η ζ r₁ r₂ L) x‖ ≤
            (2 : ℝ) ^ ((d : ℝ) + 3) * (δ * sa12x5_Bfac d Kz n W)) ∧
      (∀ j ≤ n, ∀ x : Euc d,
        ∫ z in tcb_Q d L, ‖iteratedFDeriv ℝ j (sa12x5_adiff η ζ r₁ r₂ L) (x - z)‖ ≤
          2 ^ d * (δ * sa12x5_Bfac d Kz n W) * ∫ w : Euc d, tca_g w) := by
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  set Ig : ℝ := ∫ w : Euc d, tca_g w with hIg
  have hIg0 : 0 ≤ Ig := integral_nonneg fun w => tca_g_nonneg w
  set u : Euc d → ℝ := fun x => r₁ x - r₂ x with hudef
  have hru : ContDiff ℝ (n : WithTop ℕ∞) u := hr₁.sub hr₂
  have hu0 : ∀ y, |u y| ≤ δ * tca_g y := fun y =>
    tca_abs_le_weight u δ (fun y' => by
      have := hu 0 (Nat.zero_le _) y'
      rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs, pow_zero, one_mul] at this) y
  set Z₁ : ℝ := ∫ y, ζ (L⁻¹ • y) * r₁ y with hZ₁def
  set Z₂ : ℝ := ∫ y, ζ (L⁻¹ • y) * r₂ y with hZ₂def
  set c₁ : ℝ := Z₁⁻¹ with hc₁
  set c₂ : ℝ := Z₂⁻¹ with hc₂
  have hc₁0 : 0 < c₁ := inv_pos.2 (by linarith)
  have hc₁2 : c₁ ≤ 2 := by
    rw [hc₁, inv_eq_one_div, div_le_iff₀ (by linarith)]; linarith
  have hκ : |c₁ - c₂| ≤ 4 * (δ * Ig) := by
    refine (sa12x5_inv_diff hZ₁ hZ₂).trans ?_
    exact mul_le_mul_of_nonneg_left (sa12x5_Z_diff hζ hL0 hr₁.continuous hr₂.continuous hδ0 hu0)
      (by norm_num)
  have hS0 : ∀ j, 0 ≤ tca_S d Kz 1 j := fun j => tca_S_nonneg d Kz hKz0 1 zero_le_one j
  have hBf0 : 0 ≤ sa12x5_Bfac d Kz n W := by
    unfold sa12x5_Bfac
    have : 0 ≤ ∑ j ∈ Finset.range (n + 1), 2 * tca_S d Kz 1 j :=
      Finset.sum_nonneg fun j _ => by linarith [hS0 j]
    positivity
  have hB0 : 0 ≤ δ * sa12x5_Bfac d Kz n W := mul_nonneg hδ0 hBf0
  -- the function `f`
  have hzv : ∀ y : Euc d, L / 3 ≤ ‖y‖ → ζ (L⁻¹ • y) = 0 := fun y hy => tca_zeta_far_val hζ L hL0 y hy
  set f : Euc d → ℝ := fun x => sa12k_f0 ζ r₁ L x - sa12k_f0 ζ r₂ L x with hfdef
  have hf0v : ∀ (r : Euc d → ℝ) (y : Euc d), L / 3 ≤ ‖y‖ → sa12k_f0 ζ r L y = 0 := by
    intro r y hy
    show (∫ y, ζ (L⁻¹ • y) * r y)⁻¹ * (ζ (L⁻¹ • y) * r y) = 0
    rw [hzv y hy, zero_mul, mul_zero]
  have hv : ∀ y : Euc d, L / 3 ≤ ‖y‖ → f y = 0 := fun y hy => by
    simp only [hfdef, hf0v r₁ y hy, hf0v r₂ y hy, sub_zero]
  have hζL : ContDiff ℝ (n : WithTop ℕ∞) (fun x : Euc d => ζ (L⁻¹ • x)) := tca_zetaL_contDiff hζ L n
  have hF : ContDiff ℝ (n : WithTop ℕ∞) (fun x => ζ (L⁻¹ • x) * r₂ x) := hζL.mul hr₂
  have hfA : ContDiff ℝ (n : WithTop ℕ∞) (fun x => c₁ * (ζ (L⁻¹ • x) * u x)) :=
    contDiff_const.mul (hζL.mul hru)
  have hfB : ContDiff ℝ (n : WithTop ℕ∞) (fun x => (c₁ - c₂) * (ζ (L⁻¹ • x) * r₂ x)) :=
    contDiff_const.mul hF
  have hfeq : f = fun x => c₁ * (ζ (L⁻¹ • x) * u x) + (c₁ - c₂) * (ζ (L⁻¹ • x) * r₂ x) := by
    funext x
    simp only [hfdef, sa12k_f0, hudef, hc₁, hc₂, hZ₁def, hZ₂def]
    ring
  have hfc : ContDiff ℝ (n : WithTop ℕ∞) f := by rw [hfeq]; exact hfA.add hfB
  have hfW : ∀ j ≤ n, ∀ w : Euc d,
      ‖iteratedFDeriv ℝ j f w‖ ≤ (δ * sa12x5_Bfac d Kz n W) * tca_g w := by
    intro j hj w
    have hg0 := tca_g_nonneg w
    have e1 : iteratedFDeriv ℝ j f w =
        iteratedFDeriv ℝ j (fun x => c₁ * (ζ (L⁻¹ • x) * u x)) w +
          iteratedFDeriv ℝ j (fun x => (c₁ - c₂) * (ζ (L⁻¹ • x) * r₂ x)) w := by
      rw [hfeq]
      exact iteratedFDeriv_add_apply (hfA.of_le (by exact_mod_cast hj)).contDiffAt
        (hfB.of_le (by exact_mod_cast hj)).contDiffAt
    have hA := tcb_f_weighted hζ L hL1 n u hru Kz hKz hKz0 δ hδ0 hu c₁ hc₁0 hc₁2 j hj w
    have hB1 := tcb_f_weighted hζ L hL1 n r₂ hr₂ Kz hKz hKz0 W hW0 hW₂ 1 one_pos (by norm_num) j hj w
    simp only [one_mul] at hB1
    have hBn := tca_const_mul_norm (fun x => ζ (L⁻¹ • x) * r₂ x) n hF (c₁ - c₂) j hj w
    rw [sa12x5_S_mul Kz δ j] at hA
    rw [sa12x5_S_mul Kz W j] at hB1
    set S1 := tca_S d Kz 1 j with hS1
    have hS1n : 0 ≤ S1 := hS0 j
    have hSle : 2 * S1 ≤ ∑ i ∈ Finset.range (n + 1), 2 * tca_S d Kz 1 i :=
      Finset.single_le_sum (f := fun i => 2 * tca_S d Kz 1 i) (fun i _ => by linarith [hS0 i])
        (Finset.mem_range.2 (by omega))
    calc ‖iteratedFDeriv ℝ j f w‖
        ≤ ‖iteratedFDeriv ℝ j (fun x => c₁ * (ζ (L⁻¹ • x) * u x)) w‖ +
          ‖iteratedFDeriv ℝ j (fun x => (c₁ - c₂) * (ζ (L⁻¹ • x) * r₂ x)) w‖ := by
          rw [e1]; exact norm_add_le _ _
      _ ≤ 2 * (δ * S1) * tca_g w + |c₁ - c₂| * (2 * (W * S1) * tca_g w) := by
          rw [hBn]
          exact add_le_add hA (mul_le_mul_of_nonneg_left hB1 (abs_nonneg _))
      _ ≤ 2 * (δ * S1) * tca_g w + (4 * (δ * Ig)) * (2 * (W * S1) * tca_g w) := by
          gcongr
      _ = δ * ((2 * S1) * (1 + 4 * Ig * W)) * tca_g w := by ring
      _ ≤ (δ * sa12x5_Bfac d Kz n W) * tca_g w := by
          have hle : (2 * S1) * (1 + 4 * Ig * W) ≤ sa12x5_Bfac d Kz n W := by
            unfold sa12x5_Bfac
            exact mul_le_mul hSle le_rfl (by nlinarith [mul_nonneg hIg0 hW0]) (Finset.sum_nonneg fun i _ => by linarith [hS0 i])
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hδ0) hg0
  have hg1 : ∀ w : Euc d, tca_g w ≤ 1 := fun w => sa12k_tca_g_le_one w
  have hpc : ContDiff ℝ (n : WithTop ℕ∞) (perL L f) := tca_perL_contDiff _ L hL0 f hfc hv
  have hpb : ∀ j ≤ n, ∀ y : Euc d, ‖iteratedFDeriv ℝ j (perL L f) y‖ ≤ δ * sa12x5_Bfac d Kz n W := by
    intro j hj y
    refine tca_perL_norm_le L hL0 f hv j _ (fun w => (hfW j hj w).trans ?_) y
    calc (δ * sa12x5_Bfac d Kz n W) * tca_g w ≤ (δ * sa12x5_Bfac d Kz n W) * 1 :=
          mul_le_mul_of_nonneg_left (hg1 w) hB0
      _ = _ := mul_one _
  have hadiff : sa12x5_adiff η ζ r₁ r₂ L = sa12k_moll η (perL L f) := by
    have hc : ∀ r : Euc d → ℝ, ContDiff ℝ (n : WithTop ℕ∞) r → Continuous (perL L (sa12k_f0 ζ r L)) := by
      intro r hr
      refine (tca_perL_contDiff (n : WithTop ℕ∞) L hL0 _ ?_ (hf0v r)).continuous
      exact contDiff_const.mul (hζL.mul hr)
    have hperf : perL L f = fun y => sa12k_mu0 ζ r₁ L y - sa12k_mu0 ζ r₂ L y := by
      funext y
      exact sa12x5_perL_sub L hL0 (hf0v r₁) (hf0v r₂) y
    rw [hperf]
    funext x
    exact (sa12k_moll_sub hη (hc r₁ hr₁) (hc r₂ hr₂) x).symm
  rw [hadiff]
  exact sa12x5_moll_linear_facts L hL hη hδη hv hpc hfW hpb

end HRS.MH.AdjointRd.Phase2SA12X5
