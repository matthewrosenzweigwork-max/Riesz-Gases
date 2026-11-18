import HRS.MS.S116N01
import HRS.MS.S116N02
import HRS.MS.S116N03
import HRS.MS.S116N04

/-!
# S11.6 packet N05 (`R26-T8B.N05`): bounded normalizers on the whole interval `[-a_*, β₊]`

Prefix `s116_`, namespace `HRS.MS.S116`.  `a_*, B` depend only on `d, M, L, C_g, c_g, β₊`.  The negative endpoint `-a_*` is the one of `s116_negative_normalizers` (N03), the positive
endpoint `β₊` is `s116_positive_endpoint` (N04); the interval between is filled by `s116_exponential_interval` (N01): `K_θ ≤ max (K_{-a_*}, K_{β₊})`,
and Jensen with the mean of `N F_N` (N02): `log K_θ ≥ -θ E[N F_N] ≥ -max(a_*, β₊) B_mean`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace HRS.MS.S116

open HRS HRS.Whole

theorem s116_log_normalizers {d : ℕ} (hd : 2 ≤ d) (M L Cg cg βplus : ℝ)
    (hcg : 0 < cg) (hβplus : 0 < βplus) :
    ∃ astar B : ℝ, 0 < astar ∧ 0 ≤ B ∧
      ∀ ρ : Euc d → ℝ, IsRound2Density d 0 M L ρ → HasR2GaussianUpper Cg cg ρ →
      ∀ N : ℕ, 2 ≤ N → ∀ θ ∈ Set.Icc (-astar) βplus,
        0 < HRS.Whole.gibbsNormalizer (rieszKernel d 0) N θ (HRS.Whole.withDensityReal ρ) ∧
        |Real.log (HRS.Whole.gibbsNormalizer (rieszKernel d 0) N θ (HRS.Whole.withDensityReal ρ))| ≤ B := by
  have hd1 : 1 ≤ d := by omega
  obtain ⟨a0, B0, ha0, hB0, hneg⟩ := s116_negative_normalizers hd1 Cg cg hcg
  obtain ⟨B1, hB1, hpos⟩ := s116_positive_endpoint hd M L βplus hβplus
  obtain ⟨Bm, hBm, hmean⟩ := s116_energy_mean hd1 Cg cg hcg
  refine ⟨a0, max (max B0 B1) (max a0 βplus * Bm), ha0,
    le_trans (le_trans hB0 (le_max_left _ _)) (le_max_left _ _), ?_⟩
  intro ρ hρ hG N hN θ hθ
  have hprob := hρ.prob
  have : IsProbabilityMeasure (HRS.Whole.withDensityReal ρ) := HRS.MS.R2Mt.s92_isProb_mu hprob
  set μ := HRS.Whole.withDensityReal ρ with hμ
  set P : Measure (EucConfig d N) := Measure.pi fun _ : Fin N => μ with hP
  set F : EucConfig d N → ℝ := fun X => (N : ℝ) * rieszModulatedEnergy d 0 X μ with hF
  obtain ⟨hFi, hFb⟩ := hmean ρ hprob hG N hN
  have hFm : Measurable F :=
    measurable_const.mul (HRS.MS.Wr.wr9_measurable_pairEnergy (μ := μ) (N := N)
      (k := fun x y : Euc d => rieszKernel d 0 (x - y)) (HRS.MS.Wr.wr9_rieszKernel_pair_meas (d := d) 0))
  have hK : ∀ t : ℝ, HRS.Whole.gibbsNormalizer (rieszKernel d 0) N t μ = ∫ X, Real.exp (-t * F X) ∂P := by
    intro t
    unfold HRS.Whole.gibbsNormalizer
    simp only [hF, mul_assoc]
    rfl
  obtain ⟨hnegI, hnegK, hneglog⟩ := hneg ρ hprob hG N hN (-a0) ⟨le_rfl, by linarith⟩
  obtain ⟨hGW, hposlog⟩ := hpos ρ hρ N hN
  have h₀ : Integrable (fun X => Real.exp (-(-a0) * F X)) P := by
    refine hnegI.congr (Filter.Eventually.of_forall fun X => ?_)
    simp only [hF, mul_assoc]
    rfl
  have h₁ : Integrable (fun X => Real.exp (-βplus * F X)) P := by
    refine hGW.weight_integrable.congr (Filter.Eventually.of_forall fun X => ?_)
    simp only [hF, mul_assoc]
    rfl
  obtain ⟨-, hjen, hmax⟩ := s116_exponential_interval P F hFm hFi (-a0) βplus
    (by linarith) h₀ h₁ θ hθ
  have hKb : 0 < ∫ X, Real.exp (-βplus * F X) ∂P := by
    rw [← hK]; exact hGW.normalizer_pos
  have hKa : 0 < ∫ X, Real.exp (-(-a0) * F X) ∂P := by
    rw [← hK]; exact hnegK
  have hKθ : 0 < HRS.Whole.gibbsNormalizer (rieszKernel d 0) N θ μ := by
    rw [hK]; exact lt_of_lt_of_le (Real.exp_pos _) hjen
  refine ⟨hKθ, ?_⟩
  -- lower bound
  have hlow : -θ * ∫ X, F X ∂P ≤ Real.log (HRS.Whole.gibbsNormalizer (rieszKernel d 0) N θ μ) := by
    have := Real.log_le_log (Real.exp_pos _) (hK θ ▸ hjen)
    rwa [Real.log_exp] at this
  have hθabs : |θ| ≤ max a0 βplus := by
    rw [abs_le]
    constructor
    · have := hθ.1; have := le_max_left a0 βplus; linarith
    · have := hθ.2; have := le_max_right a0 βplus; linarith
  have hlow' : |-θ * ∫ X, F X ∂P| ≤ max a0 βplus * Bm := by
    rw [abs_mul, abs_neg]
    exact mul_le_mul hθabs hFb (abs_nonneg _) (le_trans (abs_nonneg _) hθabs)
  -- upper bound
  have hup : Real.log (HRS.Whole.gibbsNormalizer (rieszKernel d 0) N θ μ) ≤ max B0 B1 := by
    have hle : HRS.Whole.gibbsNormalizer (rieszKernel d 0) N θ μ ≤
        max (∫ X, Real.exp (-(-a0) * F X) ∂P) (∫ X, Real.exp (-βplus * F X) ∂P) := by
      rw [hK]; exact hmax
    have hbA : Real.log (∫ X, Real.exp (-(-a0) * F X) ∂P) ≤ B0 := by
      rw [← hK]; exact (le_abs_self _).trans hneglog
    have hbB : Real.log (∫ X, Real.exp (-βplus * F X) ∂P) ≤ B1 := by
      rw [← hK]; exact (le_abs_self _).trans hposlog
    rcases le_total (∫ X, Real.exp (-(-a0) * F X) ∂P) (∫ X, Real.exp (-βplus * F X) ∂P) with h | h
    · rw [max_eq_right h] at hle
      exact ((Real.log_le_log hKθ hle).trans hbB).trans (le_max_right _ _)
    · rw [max_eq_left h] at hle
      exact ((Real.log_le_log hKθ hle).trans hbA).trans (le_max_left _ _)
  rw [abs_le]
  have hU : max B0 B1 ≤ max (max B0 B1) (max a0 βplus * Bm) := le_max_left _ _
  have hV : max a0 βplus * Bm ≤ max (max B0 B1) (max a0 βplus * Bm) := le_max_right _ _
  have := (abs_le.1 hlow').1
  constructor
  · linarith
  · linarith

end HRS.MS.S116

end
