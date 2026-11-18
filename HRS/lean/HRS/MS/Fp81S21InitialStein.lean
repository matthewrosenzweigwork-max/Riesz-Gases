import HRS.MS.S21F_D02
import HRS.MS.S21U_Tilt

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole
open HRS.MS.R26T3

/-- The S4.7 perturbed-reference and static preparation data at the actual initial density.

The constants are stored before the particle-indexed static fields, so consumers choose them uniformly in `N`. -/
structure InitialSteinEnv {p : Parameters} {δ : ℝ} (R : Trajectory p δ) where
  Cs : ℝ
  C : ℝ
  c : ℝ
  BU : ℝ
  BB : ℝ
  Bd : Euc p.d → Euc p.d
  Cs_nonneg : 0 ≤ Cs
  reference : S47.TRef p.d p.s (R.ρ 0) (p.a * p.β) C c BU BB Bd
  static : ∀ N : ℕ, 2 ≤ N → S47.S47Static p.d p.s (R.ρ 0) p.γ Cs N
  law_eq : ∀ N : ℕ,
    S47.s47_P p.d p.s (R.ρ 0) p.γ N = r26t3_Q R N

/-- The S4.7 context exists uniformly at the trajectory's actual preparation density. -/
theorem initialSteinEnv_exists
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (hγ : 0 < p.γ) : Nonempty (InitialSteinEnv R) := by
  have hpd : 2 ≤ p.d := p.hd
  have hsd : p.s < (p.d : ℝ) := by
    have hd : (0 : ℝ) < (p.d : ℝ) := by
      exact_mod_cast (show 0 < p.d by omega)
    have hd2 : (p.d : ℝ) / 2 ≤ p.d := by
      have hcast : (2 : ℝ) ≤ (p.d : ℝ) := by exact_mod_cast p.hd
      nlinarith
    exact lt_of_lt_of_le p.hs hd2
  have hρβ : R.ρβ = thermalDensity p.d p.s p.a p.β :=
    HRS.MS.Mov0.mv0_rho_eq p.hd p.hs0 hsd p.ha p.hβ R.thermal
  have hA := R.admissible
  have hRes := R.resulting
  have hosc : 0 ≤ oscNorm (102 * (p.d : ℝ) + 1020)
      (fun x => R.ε * Real.sqrt (R.ρβ x) * R.ψ x) := Real.sqrt_nonneg _
  have hcb : cbNorm (100 * p.d + 1001) (fun x => R.ε * R.ψ x) ≤ δ := by
    have := hA.small
    linarith
  have hcb0 := HRS.MS.S48.s48_cbu_bound hA.smooth hA.compactSupport R.ε δ
    (100 * p.d + 1001) hcb 0 (Nat.zero_le _)
  have htilt : IsTiltData p.d p.s p.a p.β R.ψ R.ε :=
    ⟨hA.smooth, hA.compactSupport, by rw [← hρβ]; exact hA.meanZero, fun x => by
      have := hcb0 x
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
      linarith⟩
  obtain ⟨Cs, C, c, BU, BB, KR, KT, hCs, hKR, hKT, hsetup⟩ :=
    S47.s47_setup_unif p.hd p.hs0 hsd
      (am := p.a) (ap := p.a) (βm := p.β) (βp := p.β) (γm := p.γ) (γp := p.γ)
      p.ha p.hβ hγ le_rfl le_rfl le_rfl (1 / 2)
  obtain ⟨Bd, hsu⟩ := hsetup p.a ⟨le_rfl, le_rfl⟩ p.β ⟨le_rfl, le_rfl⟩
    p.γ ⟨le_rfl, le_rfl⟩ R.ε R.ψ htilt (hcb.trans hδh)
  have hρ0 : R.ρ 0 = perturbedDensity (thermalDensity p.d p.s p.a p.β) R.ε R.ψ := by
    rw [hRes.init, hρβ]
  have hT : S47.TRef p.d p.s (R.ρ 0) (p.a * p.β) C c BU BB Bd := by
    rw [hρ0]
    exact hsu.hT
  have hstatic : ∀ N : ℕ, 2 ≤ N → S47.S47Static p.d p.s (R.ρ 0) p.γ Cs N := by
    intro N hN
    rw [hρ0]
    exact hsu.hS N hN
  have hpeq : ∀ N : ℕ,
      S47.s47_P p.d p.s (R.ρ 0) p.γ N = r26t3_Q R N := by
    intro N
    have hd1 : 1 ≤ p.d := by omega
    have hpeq := S47.s47_P_eq (d := p.d) hd1 p.hs0 hsd hT.hc hT.C0 hT.prob
      hT.smooth.continuous hT.pos hT.h0 hγ N
    simpa only [r26t3_Q, r26t3_mu] using hpeq
  exact ⟨⟨Cs, C, c, BU, BB, Bd, hCs, hT, hstatic, hpeq⟩⟩

#print axioms initialSteinEnv_exists

end HRS.Fp81.S21

end
