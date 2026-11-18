import HRS.MS.MovEntAux17
import HRS.MS.MovEntAux23

/-!
# S6.6, packet P5 (part 7): the pair term from the modulated energy

* `s66_cm_bdd`: for `s > 0` a density with a Gaussian bound has a bounded potential `g * ρ`.
* `s66_Pp_le_pos`: for `s > 0`, `Pp(Y) ≤ 2|F_N(Y,μ)| + 2B` when `g * μ ≤ B`.
* `s66_Pp_le_zero`: for `s = 0`, `Pp(Y) ≤ 1`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MovEnt

open HRS.Whole

local notation "wd" => Whole.withDensityReal

variable {d : ℕ}

theorem s66_cm_bdd (hd : 1 ≤ d) {s : ℝ} (hs : 0 < s) (hsd : s < d) {A cg : ℝ} (hA : 0 ≤ A) (hcg : 0 < cg) :
    ∃ B : ℝ, ∀ ρ : Euc d → ℝ, Whole.IsProbDensity ρ → (∀ x, ρ x ≤ A * Real.exp (-cg * ‖x‖ ^ 2)) →
      ∀ x, Whole.convMeasure (rieszKernel d s) (wd ρ) x ≤ B := by
  obtain ⟨Bγ, hBγ0, hBγ⟩ := HRS.MS.Thm.convMeasure_bound_of_le hd (s := s) (a := 1) (β := 2 * cg)
    hs hsd one_pos (by positivity)
  set cγ : ℝ := (2 * cg * 1 / (2 * Real.pi)) ^ ((d : ℝ) / 2) with hcγ
  have hcγpos : 0 < cγ := by positivity
  have hγ : ∀ x : Euc d, gaussianComparison d 1 (2 * cg) x = cγ * Real.exp (-cg * ‖x‖ ^ 2) := by
    intro x
    unfold gaussianComparison
    rw [hcγ]
    congr 2
    ring
  refine ⟨A / cγ * Bγ, fun ρ hρ hg x => ?_⟩
  have hM : ∀ x, ρ x ≤ (A / cγ) * gaussianComparison d 1 (2 * cg) x := by
    intro x
    rw [hγ x]
    calc ρ x ≤ A * Real.exp (-cg * ‖x‖ ^ 2) := hg x
      _ = A / cγ * (cγ * Real.exp (-cg * ‖x‖ ^ 2)) := by field_simp
  exact (hBγ (A / cγ) ρ hρ (by positivity) hM x).2.2

theorem s66_Pp_eq_pos {N : ℕ} {s : ℝ} (hs : 0 < s) (Y : EucConfig d N) :
    s66Pp s Y = (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, rieszKernel d s (Y i - Y j) := by
  unfold s66Pp rieszKernel
  simp [hs.ne']

theorem s66_Pp_le_pos {N : ℕ} (hN : 0 < N) {s : ℝ} (hs : 0 < s) {μ : Measure (Euc d)} {B : ℝ}
    (hB : ∀ x, Whole.convMeasure (rieszKernel d s) μ x ≤ B) (Y : EucConfig d N) :
    s66Pp s Y ≤ 2 * |rieszModulatedEnergy d s Y μ| + 2 * B := by
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hep : 0 ≤ Whole.energyPairing (rieszKernel d s) μ μ := by
    unfold Whole.energyPairing
    refine integral_nonneg fun x => integral_nonneg fun y => ?_
    unfold rieszKernel
    simp only [hs.ne', if_false]
    exact Real.rpow_nonneg (norm_nonneg _) _
  have hsum : (1 / (N : ℝ)) * ∑ i, Whole.convMeasure (rieszKernel d s) μ (Y i) ≤ B := by
    have : ∑ i, Whole.convMeasure (rieszKernel d s) μ (Y i) ≤ ∑ _i : Fin N, B :=
      Finset.sum_le_sum fun i _ => hB _
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    calc (1 / (N : ℝ)) * ∑ i, Whole.convMeasure (rieszKernel d s) μ (Y i) ≤ (1 / (N : ℝ)) * (N * B) :=
          mul_le_mul_of_nonneg_left this (by positivity)
      _ = B := by field_simp
  rw [s66_Pp_eq_pos hs]
  unfold rieszModulatedEnergy Whole.modulatedEnergy
  have h1 := le_abs_self (1 / (2 * (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, rieszKernel d s (Y i - Y j) -
      1 / (N : ℝ) * ∑ i, Whole.convMeasure (rieszKernel d s) μ (Y i) + 1 / 2 * Whole.energyPairing (rieszKernel d s) μ μ)
  set S := ∑ i, ∑ j ∈ Finset.univ.erase i, rieszKernel d s (Y i - Y j) with hS
  have e : 1 / (N : ℝ) ^ 2 * S = 2 * (1 / (2 * (N : ℝ) ^ 2) * S) := by field_simp
  rw [e]
  nlinarith

theorem s66_Pp_le_zero {N : ℕ} (hN : 0 < N) (Y : EucConfig d N) : s66Pp (0 : ℝ) Y ≤ 1 := by
  unfold s66Pp
  simp only [neg_zero, Real.rpow_zero, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hc : ((N - 1 : ℕ) : ℝ) ≤ N := by
    have : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N 1
    exact this
  rw [div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
  nlinarith

end HRS.MS.MovEnt

end
