import HRS.MS.Fp81S21GaussG4U42
import HRS.MS.Fp81S21AdjointAll

/-! Superposition for the physical propagator on arbitrary data admitting
classical adjoints. This includes generator inputs from regular mode orbits. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R2WinErr HRS.MS.R2WinOrbNL

/-- Superposition needs existence for each input; uniqueness and existence for
the sum then identify the chosen propagator. -/
theorem fp81s21_g4_propagator_linear
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) {t r : ℝ}
    (ht : 0 ≤ t) (hr : r ∈ Icc (0 : ℝ) t)
    {f g : Euc p.d → ℝ} (a b : ℝ)
    (hf : ∃ u, IsClassicalAdjointW (r26t3_coeff R) t f u)
    (hg : ∃ u, IsClassicalAdjointW (r26t3_coeff R) t g u) :
    r26t3_U R r t (fun x => a * f x + b * g x) =
      fun x => a * r26t3_U R r t f x + b * r26t3_U R r t g x := by
  have hsd : p.s < (p.d : ℝ) := by
    have hdreal : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
    nlinarith [p.hs]
  obtain ⟨c, K, hc, hK0, hρ⟩ := HRS.MS.S104e.s104e_gauss_rho
    p.hd p.hs0 hsd p.ha p.hβ δ p.c₁ p.C₁ 1 (by omega)
    R.thermal R.resulting
  obtain ⟨P, hP0, hU⟩ := HRS.MS.S104e.s104e_u2dec_of_gauss
    (d := p.d) hc 1 (p.d + 1)
  have hA : ∀ τ ∈ Icc (0 : ℝ) t,
      U2Dec 1 ((p.d + 1 : ℕ) : ℝ) (P * K) (R.ρ τ) := by
    intro τ hτ
    obtain ⟨hreg, hbnd⟩ := hρ τ hτ.1
    exact hU (R.ρ τ) K hK0 hreg (fun k hk x => hbnd k hk x)
  obtain ⟨u, hu⟩ := hf
  obtain ⟨v, hv⟩ := hg
  have hlin := HRS.MS.R2WinOrbNL.s103c_lincomb p.hd p.hs0 hsd
    (show (p.d : ℝ) < ((p.d + 1 : ℕ) : ℝ) by exact_mod_cast Nat.lt_succ_self p.d)
    R.ρ hA a b hu hv
  have hu' := HRS.MS.S104e.s104e_unique p.hd p.hs0 hsd p.ha p.hβ
    δ p.c₁ p.C₁ R.thermal R.admissible R.resulting t ht ⟨ht, le_rfl⟩ hu
  have hv' := HRS.MS.S104e.s104e_unique p.hd p.hs0 hsd p.ha p.hβ
    δ p.c₁ p.C₁ R.thermal R.admissible R.resulting t ht ⟨ht, le_rfl⟩ hv
  have hs' := HRS.MS.S104e.s104e_unique p.hd p.hs0 hsd p.ha p.hβ
    δ p.c₁ p.C₁ R.thermal R.admissible R.resulting t ht ⟨ht, le_rfl⟩ hlin
  have eu : r26t3_U R r t f = u r := by
    simpa [r26t3_U, r26t3_coeff] using hu' r hr
  have ev : r26t3_U R r t g = v r := by
    simpa [r26t3_U, r26t3_coeff] using hv' r hr
  have es : r26t3_U R r t (fun x => a * f x + b * g x) =
      (fun x => a * u r x + b * v r x) := by
    simpa [r26t3_U, r26t3_coeff] using hs' r hr
  rw [es, eu, ev]

#print axioms fp81s21_g4_propagator_linear
end HRS.Fp81.S21
end
