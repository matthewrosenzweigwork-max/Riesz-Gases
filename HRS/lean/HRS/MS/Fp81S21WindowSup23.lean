import HRS.MS.Fp81S21WindowSup22

/-!
# S2.1(iii), packet 9d: raw frozen-source commutator FTC

For fixed physical source time `v`, `S104nOrbit.diff01` supplies the
terminal-time difference quotient in relative time `τ = t - v`. This brick
records the exact pathwise S5.3 FTC before centering by the particle law.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Set

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.S53 HRS.MS.R2WinErr

/-- The raw commutator functional obeys the frozen-source FTC along a moving
terminal orbit. The integral is written in elapsed terminal time `τ`, where
`s = v + τ`. -/
theorem fp81s21_window_s53_frozen_source_ftc
    {d N : ℕ} {C : WholeCoeff d} {T s : ℝ} {φ : Euc d → ℝ}
    (horb : S104nOrbit C φ T) {ρ : Euc d → ℝ} {Mρ : ℝ}
    (ctx : S53Ctx s ρ Mρ) (hN : 0 < N)
    {v t : ℝ} (hv : 0 ≤ v) (hvt : v ≤ t) (htT : t ≤ T)
    (X : EucConfig d N) :
    s53_Dk s ρ (propagatorW C v t φ) X =
      s53_Dk s ρ (propagatorW C v v φ) X +
        ∫ τ in Ioc (0 : ℝ) (t - v),
          s53_Dk s ρ
            (propagatorW C v (v + τ) (generatorW C (v + τ) φ)) X := by
  have hvT : v ∈ Icc (0 : ℝ) T := ⟨hv, hvt.trans htT⟩
  have hτ : t - v ∈ Icc (0 : ℝ) (T - v) := by
    constructor <;> linarith
  let G0 : ℝ → Euc d → ℝ := fun τ => propagatorW C v (v + τ) φ
  let G1 : ℝ → Euc d → ℝ := fun τ =>
    propagatorW C v (v + τ) (generatorW C (v + τ) φ)
  have hG0 : ∀ τ ∈ Icc (0 : ℝ) (T - v), MemCb 2 (G0 τ) := by
    intro τ hτ'
    exact horb.cb0 hvT hτ'
  have hG1 : ∀ τ ∈ Icc (0 : ℝ) (T - v), MemCb 2 (G1 τ) := by
    intro τ hτ'
    exact horb.cb1 hvT hτ'
  have hdiff := horb.diff01 v hvT
  obtain ⟨G2, hG2, hd12⟩ := horb.diff12 v hvT
  have hc1 : S53Cont (T - v) G1 := s53_cont_of_diff hG1 hG2 hd12
  have hft := s104_stat_ftc ctx hN hG0 hG1 hdiff hc1 X
    (τ0 := 0) (τ := t - v) (by norm_num) hτ.1 hτ.2
  simpa [G0, G1, add_sub_cancel] using hft

#print axioms fp81s21_window_s53_frozen_source_ftc

end HRS.Fp81.S21

end
