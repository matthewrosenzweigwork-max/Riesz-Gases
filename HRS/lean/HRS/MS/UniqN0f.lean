import HRS.MS.UniqN0b
import HRS.MS.UniqN0c

/-!
# N0 of `UniqPlan.md`: the far-region interface for the nonlocal residue

* `n0_far_pairing`: if `f` has uniformly bounded local `L²` mass (`LocMass B f`), `a` satisfies
  `⟨x⟩^{d+3} |a x| ≤ Λ` (the decay of `μ` and `∂μ` in `IsRegularDensityW`), and `|G| ≤ M` on the far region
  `{y | 2R ≤ ‖y - c‖}`, then `∫_{far} |f a G| ≤ C(d) Λ M |B|`.
* `n0_far_pairing_H`, `n0_far_pairing_dH`: the same with `G = H_i = kernelConvDeriv d s i ψ`
  (resp. `G = ∂_j H_i`), where `M = C ‖ψ‖₁` by `n0_far_bound` (resp. `n0_far_grad_bound`);
  `supp ψ ⊆ B̄(c,R)`, `R ≥ 1`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal ContDiff

namespace HRS.MS.UniqN0

open HRS HRS.Whole HRS.Whole.AppendixALemmas HRS.MS.UniqM1

variable {d : ℕ}

theorem n0_far_pairing (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Λ M B : ℝ) (c : Euc d) (R : ℝ) (f a G : Euc d → ℝ), 0 ≤ Λ → 0 ≤ M →
      LocMass B f → (∀ x, jbracket x ^ ((d : ℝ) + 3) * |a x| ≤ Λ) →
      (∀ y, 2 * R ≤ ‖y - c‖ → |G y| ≤ M) →
      ∫⁻ y in {y : Euc d | 2 * R ≤ ‖y - c‖}, ‖f y * (a y * G y)‖ₑ ≤
        ENNReal.ofReal (C * (Λ * M) * |B|) := by
  have hκ : (d : ℝ) < (d : ℝ) + 3 := by linarith
  obtain ⟨C0, hC0, hC⟩ := n0_cell_decay_mul (d := d) hκ
  have hs2 : 0 < Real.sqrt 2 := by positivity
  refine ⟨C0 * Real.sqrt 2 ^ ((d : ℝ) + 3), by positivity, fun Λ M B c R f a G hΛ hM hf ha hG => ?_⟩
  set F : Set (Euc d) := {y : Euc d | 2 * R ≤ ‖y - c‖} with hF
  have hFm : MeasurableSet F :=
    (isClosed_le continuous_const (continuous_norm.comp (continuous_id.sub continuous_const))).measurableSet
  set h : Euc d → ℝ := F.indicator (fun y => a y * G y) with hh
  set A : ℝ := Λ * M * Real.sqrt 2 ^ ((d : ℝ) + 3) with hA
  have hA0 : 0 ≤ A := by positivity
  have hbd : ∀ y, |h y| ≤ A * (1 + ‖y - 0‖) ^ (-((d : ℝ) + 3)) := by
    intro y
    simp only [sub_zero]
    have hnn : 0 ≤ A * (1 + ‖y‖) ^ (-((d : ℝ) + 3)) := by positivity
    by_cases hy : y ∈ F
    · simp only [hh, Set.indicator_of_mem hy]
      have hjb : 0 < jbracket y := by unfold jbracket; positivity
      have h1 : |a y| ≤ Λ * jbracket y ^ (-((d : ℝ) + 3)) := by
        rw [Real.rpow_neg hjb.le, ← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
        exact ha y
      have h2 := n0_jbracket_rpow_le (d := d) (by positivity : (0 : ℝ) ≤ (d : ℝ) + 3) y
      rw [abs_mul]
      calc |a y| * |G y| ≤ (Λ * jbracket y ^ (-((d : ℝ) + 3))) * M :=
            mul_le_mul h1 (hG y hy) (abs_nonneg _) (by positivity)
        _ ≤ (Λ * (Real.sqrt 2 ^ ((d : ℝ) + 3) * (1 + ‖y‖) ^ (-((d : ℝ) + 3)))) * M := by gcongr
        _ = _ := by rw [hA]; ring
    · simp only [hh, Set.indicator_of_notMem hy, abs_zero]
      exact hnn
  have key := (hC 0 A B f h hA0 hf hbd).1
  calc ∫⁻ y in F, ‖f y * (a y * G y)‖ₑ = ∫⁻ y, ‖f y * h y‖ₑ := by
        rw [← lintegral_indicator hFm]
        refine lintegral_congr fun y => ?_
        by_cases hy : y ∈ F
        · simp [hh, hy]
        · simp [hh, hy]
    _ ≤ ENNReal.ofReal (C0 * A * |B|) := key
    _ = _ := by rw [hA]; congr 1; ring

/-- The far-region bound with `G = H_i = g * ∂_iψ`. -/
theorem n0_far_pairing_H (d : ℕ) {s : ℝ} (hs0 : 0 ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Λ B : ℝ) (c : Euc d) (R : ℝ) (f a ψ : Euc d → ℝ) (i : Fin d), 0 ≤ Λ → 1 ≤ R →
      LocMass B f → (∀ x, jbracket x ^ ((d : ℝ) + 3) * |a x| ≤ Λ) →
      ContDiff ℝ 1 ψ → HasCompactSupport ψ → Function.support ψ ⊆ closedBall c R →
      ∫⁻ y in {y : Euc d | 2 * R ≤ ‖y - c‖}, ‖f y * (a y * kernelConvDeriv d s i ψ y)‖ₑ ≤
        ENNReal.ofReal (C * Λ * (∫ x, |ψ x|) * |B|) := by
  obtain ⟨C0, hC0, hC⟩ := n0_far_pairing d
  refine ⟨C0 * (max 1 s * 2 ^ (s + 1)), by positivity,
    fun Λ B c R f a ψ i hΛ hR hf ha hψ hψc hsupp => ?_⟩
  have hI : 0 ≤ ∫ x, |ψ x| := integral_nonneg fun x => abs_nonneg _
  have hK : 0 ≤ max 1 s * 2 ^ (s + 1) := by positivity
  refine (hC Λ ((max 1 s * 2 ^ (s + 1)) * ∫ x, |ψ x|) B c R f a _ hΛ (by positivity) hf ha ?_).trans ?_
  · intro y hy
    refine (n0_far_bound hs0 i hψ hψc hR hsupp hy).trans ?_
    have hyc : 1 ≤ ‖y - c‖ := by linarith
    have : ‖y - c‖ ^ (-s - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hyc (by linarith)
    calc (max 1 s * 2 ^ (s + 1)) * (∫ x, |ψ x|) * ‖y - c‖ ^ (-s - 1)
        ≤ (max 1 s * 2 ^ (s + 1)) * (∫ x, |ψ x|) * 1 := by gcongr
      _ = _ := mul_one _
  · refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    ring

/-- The far-region bound with `G = ∂_j H_i`, for `ψ ∈ C²_c`. -/
theorem n0_far_pairing_dH (d : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (Λ B : ℝ) (c : Euc d) (R : ℝ) (f a ψ : Euc d → ℝ) (i j : Fin d), 0 ≤ Λ → 1 ≤ R →
      LocMass B f → (∀ x, jbracket x ^ ((d : ℝ) + 3) * |a x| ≤ Λ) →
      ContDiff ℝ 2 ψ → HasCompactSupport ψ → Function.support ψ ⊆ closedBall c R →
      ∫⁻ y in {y : Euc d | 2 * R ≤ ‖y - c‖}, ‖f y * (a y *
          fderiv ℝ (kernelConvDeriv d s i ψ) y (EuclideanSpace.single j (1 : ℝ)))‖ₑ ≤
        ENNReal.ofReal (C * Λ * (∫ x, |ψ x|) * |B|) := by
  obtain ⟨C0, hC0, hC⟩ := n0_far_pairing d
  refine ⟨C0 * (max 1 s * (s + 3) * 2 ^ (s + 2)), by positivity,
    fun Λ B c R f a ψ i j hΛ hR hf ha hψ hψc hsupp => ?_⟩
  have hI : 0 ≤ ∫ x, |ψ x| := integral_nonneg fun x => abs_nonneg _
  have hK : 0 ≤ max 1 s * (s + 3) * 2 ^ (s + 2) := by positivity
  refine (hC Λ ((max 1 s * (s + 3) * 2 ^ (s + 2)) * ∫ x, |ψ x|) B c R f a _ hΛ (by positivity) hf ha ?_).trans ?_
  · intro y hy
    refine (n0_far_grad_bound hs0 hsd i j hψ hψc hR hsupp hy).trans ?_
    have hyc : 1 ≤ ‖y - c‖ := by linarith
    have : ‖y - c‖ ^ (-s - 2) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hyc (by linarith)
    calc (max 1 s * (s + 3) * 2 ^ (s + 2)) * (∫ x, |ψ x|) * ‖y - c‖ ^ (-s - 2)
        ≤ (max 1 s * (s + 3) * 2 ^ (s + 2)) * (∫ x, |ψ x|) * 1 := by gcongr
      _ = _ := mul_one _
  · refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    ring

end HRS.MS.UniqN0
