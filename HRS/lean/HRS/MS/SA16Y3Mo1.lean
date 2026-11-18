import HRS.MS.SA16Y3Yg2
import HRS.MS.SA16QApp1

/-!
# S.A.16 (SA16Y3) Mo1: mollification of `C_c^∞` data in `L^p` (SA16S item (iii), cc core)

With the tree's normalised bump `sa16y_rho d n` (`sa16q_mol n μ = ∫ ρ_n(z) μ(· - z)`):
`sa16y3_mol_jet_le`: `‖∂^κ (ρ_n ⋆ ψ)‖_{L^p} ≤ ‖∂^κ ψ‖_{L^p}` (uniform in `n`), by `sa16y3_conv_jet_le_one`.
`sa16y3_mol_tendsto_Lp`: `‖∂^κ (ρ_n ⋆ ψ) - ∂^κ ψ‖_{L^p} → 0` as `n → ∞` for `ψ ∈ C_c^∞`.
Proof of the second: the difference is supported in the fixed compact `tsupport g + closedBall 0 1` (`g = ∂^κ ψ`),
bounded uniformly in `n`, and tends to zero pointwise (`sa16y_mollify_tendsto`); dominated convergence.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal ContDiff Pointwise

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Q

variable {d : ℕ}

lemma sa16y3_rho_lintegral (n : ℕ) : ∫⁻ y, ‖sa16y_rho d n y‖ₑ ≤ 1 := by
  rw [← ofReal_integral_norm_eq_lintegral_enorm (sa16y_rho_integrable n)]
  have h1 : ∫ z, ‖sa16y_rho d n z‖ = 1 := by
    simp_rw [Real.norm_eq_abs, abs_of_nonneg (sa16y_rho_nonneg n _)]
    exact sa16y_rho_int n
  rw [h1, ENNReal.ofReal_one]

lemma sa16y3_mol_jet_le {p : ℝ} (hp : 1 ≤ p) (n : ℕ) {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ)
    {j : ℕ} (κ : Fin j → Fin d) :
    eLpNorm (partialDeriv κ (sa16q_mol n ψ)) (ENNReal.ofReal p) volume ≤
      eLpNorm (partialDeriv κ ψ) (ENNReal.ofReal p) volume := by
  have hc : Continuous (sa16y_rho d n) := (sa16y_rho_smooth n).continuous
  exact sa16y3_conv_jet_le_one hp (sa16y_rho_integrable n) hc.measurable (sa16y3_rho_lintegral n) hψ κ

lemma sa16y3_mol_supp {g : EuclideanSpace ℝ (Fin d) → ℝ} (n : ℕ) {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∉ tsupport g + closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) : sa16q_mol n g x = 0 := by
  unfold sa16q_mol sa16j_conv
  have hz : ∀ z : EuclideanSpace ℝ (Fin d), sa16y_rho d n z * g (x - z) = 0 := by
    intro z
    by_cases hzb : ‖z‖ ≤ 1
    · have hxz : x - z ∉ tsupport g := fun h =>
        hx (Set.mem_add.2 ⟨x - z, h, z, by simpa [mem_closedBall, dist_zero_right] using hzb, sub_add_cancel x z⟩)
      rw [image_eq_zero_of_notMem_tsupport hxz, mul_zero]
    · have h1 : 1 / ((n : ℝ) + 1) ≤ 1 :=
        div_le_one_of_le₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) (by positivity)
      rw [sa16y_rho_supp n z (h1.trans_lt (not_le.1 hzb)), zero_mul]
  simp [hz]

lemma sa16y3_mol_zero_of_notMem {g : EuclideanSpace ℝ (Fin d) → ℝ} {x : EuclideanSpace ℝ (Fin d)}
    (hx : x ∉ tsupport g + closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) : g x = 0 :=
  image_eq_zero_of_notMem_tsupport fun h =>
    hx (Set.mem_add.2 ⟨x, h, 0, mem_closedBall_self zero_le_one, add_zero x⟩)

theorem sa16y3_mol_tendsto_Lp {p : ℝ} (hp : 1 ≤ p) {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ)
    {j : ℕ} (κ : Fin j → Fin d) :
    Tendsto (fun n : ℕ => eLpNorm (partialDeriv κ (sa16q_mol n ψ) - partialDeriv κ ψ) (ENNReal.ofReal p) volume)
      atTop (𝓝 0) := by
  have hg : IsCcInfty (partialDeriv κ ψ) := sa16s_cc_partialDeriv hψ κ
  have hpd : ∀ n, partialDeriv κ (sa16q_mol n ψ) = sa16q_mol n (partialDeriv κ ψ) :=
    fun n => sa16q_mol_pd n (hψ.1.of_le (by simp)) κ
  simp only [hpd]
  set g := partialDeriv κ ψ with hgdef
  obtain ⟨C, hC⟩ := hg.1.continuous.bounded_above_of_compact_support hg.2
  set K := tsupport g + closedBall (0 : EuclideanSpace ℝ (Fin d)) 1 with hKdef
  have hK : IsCompact K := hg.2.isCompact.add (isCompact_closedBall _ _)
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hcont : ∀ n, Continuous (sa16q_mol n g) := fun n =>
    (sa16y3_conv_contDiff (sa16y_rho_integrable n).locallyIntegrable hg).continuous
  have hC' : ∀ y, |g y| ≤ C := fun y => by simpa [Real.norm_eq_abs] using hC y
  have hbound : ∀ n x, ‖sa16q_mol n g x - g x‖ₑ ^ p ≤ K.indicator (fun _ => ENNReal.ofReal (2 * C) ^ p) x := by
    intro n x
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx]
      have h1 : |sa16q_mol n g x| ≤ C := sa16y_mollify_bound n hg.1.continuous hC' x
      have h2 : ‖sa16q_mol n g x - g x‖ ≤ 2 * C := by
        rw [Real.norm_eq_abs] at *
        have := abs_sub (sa16q_mol n g x) (g x)
        linarith [hC' x]
      have h3 : ‖sa16q_mol n g x - g x‖ₑ ≤ ENNReal.ofReal (2 * C) := by
        rw [← ofReal_norm]
        exact ENNReal.ofReal_le_ofReal h2
      exact ENNReal.rpow_le_rpow h3 (by linarith)
    · rw [Set.indicator_of_notMem hx, sa16y3_mol_supp n hx, sa16y3_mol_zero_of_notMem hx]
      simp only [sub_self, enorm_zero]
      exact le_of_eq (ENNReal.zero_rpow_of_pos (by linarith))
  have hmeas : ∀ n, Measurable (fun x => ‖sa16q_mol n g x - g x‖ₑ ^ p) := fun n =>
    (((hcont n).sub hg.1.continuous).enorm.measurable).pow_const p
  have hpt0 : ∀ x, Tendsto (fun n => ‖sa16q_mol n g x - g x‖ₑ ^ p) atTop (𝓝 0) := by
    intro x
    have h1 : Tendsto (fun n => sa16q_mol n g x - g x) atTop (𝓝 0) := by
      have := (sa16y_mollify_tendsto hg.1.continuous x).sub_const (g x)
      rw [sub_self] at this
      exact this
    have h2 := (continuous_enorm.tendsto 0).comp h1
    simp only [enorm_zero] at h2
    have h3 := ((ENNReal.continuous_rpow_const (y := p)).tendsto 0).comp h2
    rwa [ENNReal.zero_rpow_of_pos (by linarith)] at h3
  have hfin : ∫⁻ x, K.indicator (fun _ => ENNReal.ofReal (2 * C) ^ p) x ≠ ⊤ := by
    rw [lintegral_indicator_const hKm]
    exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top)
      hK.measure_lt_top.ne
  have hdct : Tendsto (fun n => ∫⁻ x, ‖sa16q_mol n g x - g x‖ₑ ^ p) atTop (𝓝 0) := by
    have := tendsto_lintegral_of_dominated_convergence (μ := volume) (f := fun _ => (0 : ENNReal))
      (F := fun n x => ‖sa16q_mol n g x - g x‖ₑ ^ p)
      (bound := K.indicator (fun _ => ENNReal.ofReal (2 * C) ^ p))
      (fun n => hmeas n) (fun n => Eventually.of_forall fun x => hbound n x) hfin
      (Eventually.of_forall hpt0)
    simpa using this
  have hpne : ENNReal.ofReal p ≠ 0 := by simpa using (show (0 : ℝ) < p by linarith)
  have hpt : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  have hpr : (ENNReal.ofReal p).toReal = p := ENNReal.toReal_ofReal (by linarith)
  have hform : ∀ n, eLpNorm (sa16q_mol n g - g) (ENNReal.ofReal p) volume =
      (∫⁻ x, ‖sa16q_mol n g x - g x‖ₑ ^ p) ^ (1 / p) := by
    intro n
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hpne hpt ((hcont n).sub hg.1.continuous).aestronglyMeasurable, hpr]
    rfl
  have h4 := ((ENNReal.continuous_rpow_const (y := 1 / p)).tendsto 0).comp hdct
  have hinv : (0 : ℝ) < 1 / p := by
    have : (0 : ℝ) < p := by linarith
    positivity
  rw [ENNReal.zero_rpow_of_pos hinv] at h4
  simp only [hform]
  exact h4

end HRS.Whole.AppendixA.Phase2SA16R
