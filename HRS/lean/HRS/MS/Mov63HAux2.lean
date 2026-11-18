import HRS.MS.Mov63HAux1
import HRS.MS.Mov63GAux19
import HRS.MS.Mov63CAux15

/-!
# S6.3, packet N9 (part 2): the assembly `mnh_nonlinear`

Namespace `HRS.MS.Mov63`, prefix `mnh_`.  The statement of `HRS.Whole.mov_nonlinear`, proved from `mov63_decay_f0` (N5-N8), `mov_nl_unique_conjunct`
(N4) and the conversions of `Mov63HAux1` (see the plan there).  Constants: `ε_*, r, c` from `mov63_decay_f0`, `c₀ = c₁/2`, `C = max C₀ 2`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd

theorem mnh_nonlinear {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β q : ℝ) (hβ : 0 < β)
    (hq : 0 < q) (j : ℕ) (hj : 1 ≤ j) (m : ℕ) (hm : (d : ℝ) / 2 + j + 6 < m)
    (ρ₀ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s q β ρ₀) :
    ∃ εstar r c₀ c C : ℝ, 0 < εstar ∧ 0 < r ∧ 0 < c₀ ∧ 0 < c ∧ 0 < C ∧
      MovNonlinearConclusion d s q β ρ₀ j m εstar r c₀ c C ∧
      ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → ψ ≠ 0 →
        ∫ x, ψ x * ρ₀ x = 0 →
        ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, |ε| < ε₀ →
          MovInitialClass ρ₀ j m εstar (fun x => ε * ψ x) := by
  have H : Mov2dTh d s β q ρ₀ := ⟨hd, hs0, hsd, hβ, hq, hρ⟩
  obtain ⟨c₁, hc₁, h⟩ := mov63_decay_f0 H hj
  obtain ⟨εstar, r, c, C₀, hε, hε4, hr, hc, hC₀, hf⟩ := h m hm
  have hm3 : (d : ℝ) / 2 + 3 < m := by
    have : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    linarith
  have hC2 : (2 : ℝ) ≤ max C₀ 2 := le_max_right _ _
  have hCinv : (max C₀ 2)⁻¹ ≤ 2⁻¹ := inv_anti₀ (by norm_num) hC2
  refine ⟨εstar, r, c₁ / 2, c, max C₀ 2, hε, hr, by positivity, hc, by linarith, ?_, ?_⟩
  · intro f0 hf0
    have hcont := mnh_contDiff3 H hm3 hf0.cb hj hf0.osc
    have hmass := mnh_massZero H hm3 hf0.osc hf0.mean
    obtain ⟨v, hM, hv0, hcls, hrat, hDi, hDe, hI⟩ := hf hm3 f0 hcont hf0.cb hf0.osc hmass hf0.small
    have hRD := mnb_rhoData H
    refine ⟨mneP d ρ₀ hm3 v, hcls, fun t ht => ⟨(hcls.solution t).density t ⟨ht, le_rfl⟩, fun x => ?_⟩,
      fun t ht x => ⟨?_, ?_⟩, mnh_decay_mono_C hε.le (le_max_left _ _) hDe,
      mnh_decay_mono_C (mnh_initialNorm_nonneg f0 ρ₀ j m) (le_max_left _ _) hDi, hI,
      mov_nl_unique_conjunct hd hs0 hsd hβ hq hρ hj hm hcls⟩
    · linarith [(hrat t ht x).1, hRD.pos x]
    · have h1 := (hrat t ht x).1
      have h2 : (max C₀ 2)⁻¹ * ρ₀ x ≤ 2⁻¹ * ρ₀ x := mul_le_mul_of_nonneg_right hCinv (hRD.pos x).le
      linarith
    · have h1 := (hrat t ht x).2
      have h2 : 2 * ρ₀ x ≤ max C₀ 2 * ρ₀ x := mul_le_mul_of_nonneg_right hC2 (hRD.pos x).le
      linarith
  · intro ψ hψ hcs _ hmean
    exact mnh_psi_class H hm3 hε hψ hcs hmean

end HRS.MS.Mov63

end
