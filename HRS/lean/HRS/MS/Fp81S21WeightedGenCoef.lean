import HRS.MS.S21F_D00
import HRS.MS.S104eEx1
import HRS.MS.S21A_Mono

/-! Uniform coefficient data and the trajectory-uniform Gaussian density jets. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.R26T3
open HRS.MS.S104e HRS.MS.S104b HRS.MS.Mov63 HRS.MS.S105r HRS.MS.R2WinOrbNL

abbrev fp81s21_b3_q (p : Parameters) : ℕ := 2 * p.d + 6

def fp81s21_b3_Data {p : Parameters} {δ : ℝ} (R : Trajectory p δ)
    (B c : ℝ) : Prop :=
  ∀ u, 0 ≤ u →
    ContDiff ℝ (fp81s21_b3_q p) ((r26t3_coeff R).drift u) ∧
    (∀ j ≤ fp81s21_b3_q p, ∀ x,
      ‖iteratedFDeriv ℝ j ((r26t3_coeff R).drift u) x‖ ≤ B * jbracket x) ∧
    ContDiff ℝ (fp81s21_b3_q p + 2) (R.ρ u) ∧
    (∀ j ≤ fp81s21_b3_q p + 2, ∀ x,
      ‖iteratedFDeriv ℝ j (R.ρ u) x‖ ≤ B * Real.exp (-c * ‖x‖ ^ 2))

/-- Gaussian density jets with constants fixed before the radius and trajectory. -/
theorem fp81s21_b3_rho_jets (p : Parameters) :
    ∃ B c : ℝ, 0 ≤ B ∧ 0 < c ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ (1 / 2 : ℝ) → ∀ R : Trajectory p δ,
        ∀ u, 0 ≤ u →
          ContDiff ℝ (fp81s21_b3_q p + 2) (R.ρ u) ∧
          ∀ j ≤ fp81s21_b3_q p + 2, ∀ x,
            ‖iteratedFDeriv ℝ j (R.ρ u) x‖ ≤ B * Real.exp (-c * ‖x‖ ^ 2) := by
  have hsd : p.s < (p.d : ℝ) := by linarith [p.hs]
  by_cases hex : ∃ δ : ℝ, Nonempty (Trajectory p δ)
  · obtain ⟨δ₀, ⟨R₀⟩⟩ := hex
    obtain ⟨B₀, hBdef, hR, -⟩ := HRS.MS.Mov0.mv0_gapref p.hd p.hs0 hsd p.ha p.hβ R₀.thermal
    let n : ℕ := fp81s21_b3_q p + 2
    let m : ℕ := 102 * p.d + 1020
    have hmR : (m : ℝ) = 102 * (p.d : ℝ) + 1020 := by dsimp [m]; push_cast; ring
    have hm1 : (p.d : ℝ) / 2 + (n : ℝ) + 2 < m := by
      rw [hmR]
      dsimp [n, fp81s21_b3_q]
      push_cast
      have : (0 : ℝ) ≤ p.d := Nat.cast_nonneg p.d
      linarith
    obtain ⟨Cv, hCv0, hCv⟩ := mn_force_bound p.hd p.hs0 hsd p.β p.a p.hβ p.ha R₀.ρβ R₀.thermal n m hm1
    let E : ℝ := |p.C₁| * |(1 / 2 : ℝ)|
    have hE0 : 0 ≤ E := by dsimp [E]; positivity
    obtain ⟨c, K, hc, hK0, hKb⟩ := s104e_leibniz (mul_pos p.hβ p.ha) hR n Cv E hCv0 hE0
    refine ⟨K, c, hK0, hc, ?_⟩
    intro δ hδ hδhalf R u hu
    have heq : R.ρβ = R₀.ρβ :=
      (HRS.MS.Mov0.mv0_rho_eq p.hd p.hs0 hsd p.ha p.hβ R.thermal).trans
        (HRS.MS.Mov0.mv0_rho_eq p.hd p.hs0 hsd p.ha p.hβ R₀.thermal).symm
    have hmono := HRS.MS.S21A.s21a_cls_mono p.hd p.hs0 hsd p.ha p.hβ R.thermal
      (hle := hδhalf) R.admissible R.resulting
    have hres := hmono.2
    rw [heq] at hres
    have hpos : ∀ x, 0 < R₀.ρβ x := hR.pos
    have hρβc : Continuous R₀.ρβ := hR.smooth.continuous
    have hdec : R.ρ u = fun x => R₀.ρβ x + Real.sqrt (R₀.ρβ x) *
        ((R.ρ u x - R₀.ρβ x) / Real.sqrt (R₀.ρβ x)) := by
      funext x
      have hsq : 0 < Real.sqrt (R₀.ρβ x) := Real.sqrt_pos.2 (hpos x)
      field_simp
      ring
    have hvc : Continuous (fun x => (R.ρ u x - R₀.ρβ x) / Real.sqrt (R₀.ρβ x)) :=
      ((hres.regular u hu).sub hρβc).div hρβc.sqrt (fun x => (Real.sqrt_pos.2 (hpos x)).ne')
    have hvm : MemOsc (m : ℝ) (fun x => (R.ρ u x - R₀.ρβ x) / Real.sqrt (R₀.ρβ x)) := by
      rw [hmR]; exact (hres.weighted u hu).1
    have hvn : oscNorm (m : ℝ) (fun x => (R.ρ u x - R₀.ρβ x) / Real.sqrt (R₀.ρβ x)) ≤ E := by
      rw [hmR]
      refine ((hres.weighted u hu).2).trans ?_
      have h1 : Real.exp (-p.c₁ * u) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have := hres.cpos
        nlinarith
      have h2 : 0 ≤ Real.exp (-p.c₁ * u) := (Real.exp_pos _).le
      calc p.C₁ * (1 / 2 : ℝ) * Real.exp (-p.c₁ * u) ≤
          |p.C₁ * (1 / 2 : ℝ)| * Real.exp (-p.c₁ * u) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) h2
        _ ≤ |p.C₁ * (1 / 2 : ℝ)| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = E := by dsimp [E]; rw [mul_one, abs_mul]
    obtain ⟨hvn2, hvb, -⟩ := hCv _ hvc hvm
    have hv' : ContDiff ℝ (n : WithTop ℕ∞) (fun x => (R.ρ u x - R₀.ρβ x) / Real.sqrt (R₀.ρβ x)) :=
      hvn2.of_le (by exact_mod_cast (by omega : n ≤ n + 2))
    have hvb' : ∀ k ≤ n, ∀ x : Euc p.d,
        ‖iteratedFDeriv ℝ k (fun x => (R.ρ u x - R₀.ρβ x) / Real.sqrt (R₀.ρβ x)) x‖ ≤ Cv * E :=
      fun k hk x => (hvb k (by omega) x).trans (mul_le_mul_of_nonneg_left hvn hCv0)
    obtain ⟨hcd, hKb'⟩ := hKb _ hv' hvb'
    rw [← hdec] at hcd hKb'
    exact ⟨hcd, hKb'⟩
  · refine ⟨0, 1, le_rfl, zero_lt_one, ?_⟩
    intro δ hδ hδhalf R
    exact False.elim (hex ⟨δ, ⟨R⟩⟩)

#print axioms HRS.Fp81.S21.fp81s21_b3_Data
#print axioms HRS.Fp81.S21.fp81s21_b3_rho_jets

end HRS.Fp81.S21
