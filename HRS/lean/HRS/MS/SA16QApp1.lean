import HRS.MS.SA16QPt1
import HRS.MS.SA16StrongApprox

/-!
# S.A.16 (SA16Q), E6 part 13: mollified coefficients

`sa16q_mol n μ = ρ_n ⋆ μ` (`ρ_n` the compactly supported normalized bump of radius `1/(n+1)`).  For continuous bounded `μ`
it is in `sa16q_SB` (all derivatives bounded: they fall on the kernel), and for `μ ∈ C^m` with weighted coordinate
derivatives `|∂^r μ(x)| (1+|x|)^{d+3} ≤ Λ` (`|r| ≤ m`) the mollifications satisfy the same with `2^{d+3} Λ`
(uniformly in `n`); coordinate derivatives converge pointwise.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap Convolution

namespace HRS.Whole.AppendixA.Phase2SA16Q
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixA.Phase2SA16

section App
variable {d : ℕ}

/-- the mollifier as a Schwartz function -/
def sa16q_rhoS (n : ℕ) : 𝓢(Euc d, ℝ) := (sa16y_rho_compact n).toSchwartzMap (sa16y_rho_smooth n)

lemma sa16q_rhoS_apply (n : ℕ) (x : Euc d) : sa16q_rhoS n x = sa16y_rho d n x := rfl

def sa16q_mol (n : ℕ) (μ : Euc d → ℝ) : Euc d → ℝ := sa16j_conv (sa16y_rho d n) μ

lemma sa16q_mol_eq (n : ℕ) (μ : Euc d → ℝ) :
    sa16q_mol n μ = fun x => ∫ y, μ y * sa16q_rhoS n (x - y) := by
  funext x
  have h := HRS.S16Cze.s16cze_conv_swap (sa16y_rho d n) μ x
  calc sa16q_mol n μ x = ∫ z, sa16y_rho d n z * μ (x - z) := rfl
    _ = HRS.Whole.convFun (sa16y_rho d n) μ x := h.symm
    _ = ∫ y, sa16y_rho d n (x - y) * μ y := rfl
    _ = ∫ y, μ y * sa16q_rhoS n (x - y) := by
        refine integral_congr_ae (Eventually.of_forall fun y => ?_)
        simp only [sa16q_rhoS_apply]
        ring

lemma sa16q_WI_of_bdd {μ : Euc d → ℝ} (hm : Measurable μ) {B : ℝ} (hB : ∀ y, |μ y| ≤ B) :
    sa16q_WI μ := by
  unfold sa16q_WI
  have hint : Integrable (fun y : Euc d => (1 + ‖y‖) ^ (-((d + 2 : ℕ) : ℝ))) volume :=
    integrable_one_add_norm (by simp)
  refine (hint.const_mul B).mono' ?_ (Eventually.of_forall fun y => ?_)
  · exact (hm.norm.mul ((measurable_const.add measurable_norm).pow_const _)).aestronglyMeasurable
  · have hw : 0 ≤ (1 + ‖y‖) ^ (-((d + 2 : ℕ) : ℝ)) := Real.rpow_nonneg (by positivity) _
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) hw)]
    exact mul_le_mul_of_nonneg_right (by simpa [Real.norm_eq_abs] using hB y) hw

/-- translation: `∫ |ψ (x - y)| dy = ∫ |ψ|` -/
lemma sa16q_int_abs_sub (ψ : 𝓢(Euc d, ℝ)) (x : Euc d) :
    ∫ y, |ψ (x - y)| = ∫ y, |ψ y| := by
  have := integral_sub_left_eq_self (fun y : Euc d => |ψ y|) (volume : Measure (Euc d)) x
  simpa using this

lemma sa16q_mol_SB (n : ℕ) {μ : Euc d → ℝ} (hc : Continuous μ) {B : ℝ} (hB : ∀ y, |μ y| ≤ B) :
    sa16q_SB (sa16q_mol n μ) := by
  have hWI := sa16q_WI_of_bdd hc.measurable hB
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  rw [sa16q_mol_eq]
  refine ⟨sa16q_gen_contDiff_top hc.measurable hWI (sa16q_rhoS n), fun j => ?_⟩
  have hpd : ∀ (r : Fin j → Fin d) (x : Euc d),
      |partialDeriv r (fun x => ∫ y, μ y * sa16q_rhoS n (x - y)) x| ≤
        B * ∫ y, |sa16q_pdS r (sa16q_rhoS n) y| := by
    intro r x
    rw [sa16q_gen_pd hc.measurable hWI j r (sa16q_rhoS n), ← sa16q_pdS_fun]
    set ψ := sa16q_pdS r (sa16q_rhoS n) with hψ
    obtain ⟨C, hC, hd1, hc1, hD, hD'⟩ := sa16q_schwartz_hyp ψ
    have hint := sa16q_conv_integrable hc.measurable hWI hC ψ.continuous hD x
    have hint2 : Integrable (fun y => |ψ (x - y)|) := by
      have hi : Integrable (⇑ψ) (volume : Measure (Euc d)) := ψ.integrable
      have := hi.norm.comp_sub_left x
      simpa using this
    calc |∫ y, μ y * ψ (x - y)| ≤ ∫ y, |μ y * ψ (x - y)| := abs_integral_le_integral_abs
      _ ≤ ∫ y, B * |ψ (x - y)| := by
          refine integral_mono hint.abs (hint2.const_mul B) fun y => ?_
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right (hB y) (abs_nonneg _)
      _ = B * ∫ y, |ψ y| := by rw [integral_const_mul, sa16q_int_abs_sub]
  refine ⟨∑ r : Fin j → Fin d, B * ∫ y, |sa16q_pdS r (sa16q_rhoS n) y|, fun x => ?_⟩
  refine (sa16j_norm_iter_le _ x j).trans (Finset.sum_le_sum fun r _ => hpd r x)

/-- the weighted bound passes to the mollification, uniformly in `n` -/
lemma sa16q_mol_pt_weight (n : ℕ) {f : Euc d → ℝ} (hf : Continuous f) {Λ : ℝ}
    (hw : ∀ y, |f y| * (1 + ‖y‖) ^ (d + 3) ≤ Λ) (x : Euc d) :
    |sa16j_conv (sa16y_rho d n) f x| * (1 + ‖x‖) ^ (d + 3) ≤ 2 ^ (d + 3) * Λ := by
  have hΛ : 0 ≤ Λ := (mul_nonneg (abs_nonneg _) (by positivity)).trans (hw 0)
  set ρ := sa16y_rho d n with hρ
  have hW : (0 : ℝ) < (1 + ‖x‖) ^ (d + 3) := by positivity
  have hpt : ∀ z, |ρ z * f (x - z)| * (1 + ‖x‖) ^ (d + 3) ≤ ρ z * (2 ^ (d + 3) * Λ) := by
    intro z
    by_cases hz : ρ z = 0
    · simp [hz]
    · have hz1 : ‖z‖ ≤ 1 / ((n : ℝ) + 1) := by
        by_contra h
        exact hz (sa16y_rho_supp n z (not_le.1 h))
      have hz2 : ‖z‖ ≤ 1 := hz1.trans (by
        rw [div_le_one (by positivity)]
        have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        linarith)
      have h1 : 1 + ‖x‖ ≤ 2 * (1 + ‖x - z‖) := by
        have h3 : ‖x‖ ≤ ‖x - z‖ + ‖z‖ := by
          calc ‖x‖ = ‖(x - z) + z‖ := by simp
            _ ≤ ‖x - z‖ + ‖z‖ := norm_add_le _ _
        linarith [norm_nonneg (x - z)]
      have h2 : (1 + ‖x‖) ^ (d + 3) ≤ 2 ^ (d + 3) * (1 + ‖x - z‖) ^ (d + 3) := by
        rw [← mul_pow]
        exact pow_le_pow_left₀ (by positivity) h1 _
      have hρz : 0 ≤ ρ z := sa16y_rho_nonneg n z
      rw [abs_mul, abs_of_nonneg hρz]
      calc ρ z * |f (x - z)| * (1 + ‖x‖) ^ (d + 3)
          ≤ ρ z * |f (x - z)| * (2 ^ (d + 3) * (1 + ‖x - z‖) ^ (d + 3)) := by gcongr
        _ = ρ z * (2 ^ (d + 3) * (|f (x - z)| * (1 + ‖x - z‖) ^ (d + 3))) := by ring
        _ ≤ ρ z * (2 ^ (d + 3) * Λ) := by gcongr; exact hw _
  have hbd : ∀ y, |f y| ≤ Λ := fun y => by
    have h1 : (1 : ℝ) ≤ (1 + ‖y‖) ^ (d + 3) := one_le_pow₀ (by linarith [norm_nonneg y])
    calc |f y| = |f y| * 1 := (mul_one _).symm
      _ ≤ |f y| * (1 + ‖y‖) ^ (d + 3) := by gcongr
      _ ≤ Λ := hw y
  have hρc : Continuous ρ := sa16y_rho_smooth n |>.continuous
  have hintρ : Integrable (fun z => ρ z * f (x - z)) := by
    refine Integrable.mono' ((sa16y_rho_integrable n).mul_const Λ)
      (hρc.aestronglyMeasurable.mul (hf.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (Eventually.of_forall fun z => ?_)
    rw [norm_mul, Real.norm_of_nonneg (sa16y_rho_nonneg n z), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hbd _) (sa16y_rho_nonneg n z)
  have hint2 : Integrable (fun z => ρ z * f (x - z) * (1 + ‖x‖) ^ (d + 3)) := hintρ.mul_const _
  calc |sa16j_conv ρ f x| * (1 + ‖x‖) ^ (d + 3)
      = |∫ z, ρ z * f (x - z) * (1 + ‖x‖) ^ (d + 3)| := by
        rw [integral_mul_const, abs_mul, abs_of_pos hW]; rfl
    _ ≤ ∫ z, |ρ z * f (x - z) * (1 + ‖x‖) ^ (d + 3)| := abs_integral_le_integral_abs
    _ ≤ ∫ z, ρ z * (2 ^ (d + 3) * Λ) := by
        refine integral_mono hint2.abs ((sa16y_rho_integrable n).mul_const _) fun z => ?_
        rw [abs_mul, abs_of_pos hW]
        exact hpt z
    _ = 2 ^ (d + 3) * Λ := by rw [integral_mul_const, sa16y_rho_int, one_mul]

lemma sa16q_mol_pd (n : ℕ) {μ : Euc d → ℝ} {k : ℕ} (hμ : ContDiff ℝ k μ) (r : Fin k → Fin d) :
    partialDeriv r (sa16q_mol n μ) = sa16q_mol n (partialDeriv r μ) :=
  sa16y_conv_pdN (R := 1 / ((n : ℝ) + 1)) (sa16y_rho_supp n) (by positivity)
    (sa16y_rho_integrable n) k 0 r μ (by simpa using hμ)

lemma sa16q_mol_tendsto {μ : Euc d → ℝ} {k : ℕ} (hμ : ContDiff ℝ k μ) (r : Fin k → Fin d) (x : Euc d) :
    Tendsto (fun n => partialDeriv r (sa16q_mol n μ) x) atTop (𝓝 (partialDeriv r μ x)) := by
  have hc : Continuous (partialDeriv r μ) :=
    (sa16y_pd_contDiffN (j := k) (r := 0) (by simpa using hμ) r).continuous
  have := sa16y_mollify_tendsto hc x
  simp only [sa16q_mol_pd _ hμ r]
  exact this

lemma sa16q_mol_bound (n : ℕ) {μ : Euc d → ℝ} (hc : Continuous μ) {B : ℝ} (hB : ∀ y, |μ y| ≤ B) (x : Euc d) :
    |sa16q_mol n μ x| ≤ B := sa16y_mollify_bound n hc hB x

end App

end HRS.Whole.AppendixA.Phase2SA16Q
