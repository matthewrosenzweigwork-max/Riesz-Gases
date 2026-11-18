import HRS.MS.SA16Y4Io5
import HRS.MS.SA16Y3Jt1
import HRS.MS.SA16ZM1
import HRS.MS.SA16ZL7

/-!
# S.A.16 (SA16Y5) Dc1: the order-one bound `‖∂_i (g ⋆ (a ψ))‖_p ≤ K ‖ψ‖_p` for a decaying coefficient `a`

`sa16y5_Dec N W μ`: `‖D^κ μ (x)‖ ≤ W (1+|x|)^{-(d+3)}` for `κ ≤ N` (closed under `∂_l`: `sa16y5_Dec_dm`).
`sa16y5_D0` (`0 ≤ s < d-1`, `d < p(s+1)`): for `a` smooth with `Dec 1 W a` and `ψ ∈ C_c^∞`,
`‖∂_i (g ⋆ (a ψ))‖_p ≤ K ‖ψ‖_p`, `K = K(d,s,p,W)`.  No derivative falls on `ψ`: this is the commutator-order bound
(order `θ - 1 < 0`) that replaces the `θ > 1` bound `sa16z_P_Lp` in the energy chain.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Dc1
variable {d : ℕ}

/-- decay of the derivatives of `μ` up to order `N` -/
def sa16y5_Dec (N : ℕ) (W : ℝ) (μ : Euc d → ℝ) : Prop :=
  ∀ κ ≤ N, ∀ x, ‖iteratedFDeriv ℝ κ μ x‖ ≤ W * (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ))

lemma sa16y5_Dec_mono {N M : ℕ} (h : N ≤ M) {W : ℝ} {μ : Euc d → ℝ} (hμ : sa16y5_Dec M W μ) :
    sa16y5_Dec N W μ := fun κ hκ => hμ κ (hκ.trans h)

lemma sa16y5_Dec_dm {N : ℕ} {W : ℝ} {μ : Euc d → ℝ} (hμs : ContDiff ℝ ∞ μ) (hμ : sa16y5_Dec (N + 1) W μ)
    (l : Fin d) : sa16y5_Dec N W (sa16z_dm μ l) := fun κ hκ y => by
  have h := sa16so_norm_iter_dir hμs (sa16z_e l) κ y
  rw [show ‖sa16z_e l‖ = 1 by simp [sa16z_e], one_mul] at h
  exact h.trans (hμ (κ + 1) (by omega) y)

lemma sa16y5_jet0_le {p : ℝ} [Fact (2 ≤ p)] {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) :
    eLpNorm (wJet 0 f) (ENNReal.ofReal p) volume ≤ eLpNorm f (ENNReal.ofReal p) volume := by
  refine (sa16y3_jet_le_pd (p := p) hf 0).trans (le_of_eq ?_)
  rw [Finset.sum_range_one, Finset.univ_unique, Finset.sum_singleton]
  exact congrArg (fun g => eLpNorm g (ENNReal.ofReal p) volume) (funext fun x => sa16j_pd_zero _ f x)

theorem sa16y5_D0 (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < (d : ℝ) - 1) {p : ℝ} (hp : 2 ≤ p)
    (hfar : (d : ℝ) < p * (s + 1)) {W : ℝ} (hW : 0 ≤ W) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {a : Euc d → ℝ}, ContDiff ℝ ∞ a → sa16y5_Dec 1 W a →
      ∀ {ψ : Euc d → ℝ}, IsCcInfty ψ → ∀ i : Fin d,
        eLpNorm (fun x => fderiv ℝ (convFun (rieszKernel d s) (fun y => a y * ψ y)) x (sa16z_e i))
          (ENNReal.ofReal p) volume ≤ ENNReal.ofReal K * eLpNorm ψ (ENNReal.ofReal p) volume := by
  have : Fact (2 ≤ p) := ⟨hp⟩
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hp1r : 1 < p := by linarith
  obtain ⟨q, C1, hq1, hqp, hrel, hC1, hD1⟩ := sa16y4io_D1_bound hd hs0 hs1 hp hfar
  have hra : ∃ ra : ℝ, 1 ≤ ra ∧ 1 / q = 1 / ra + 1 / p := by
    refine ⟨(((d : ℝ) - s - 1) / d)⁻¹, ?_, ?_⟩
    · rw [le_inv_comm₀ one_pos (by apply div_pos <;> linarith), inv_one, div_le_one hd0]
      linarith
    · rw [one_div (((d : ℝ) - s - 1) / d)⁻¹, inv_inv]
      linarith
  obtain ⟨KQ, hKQ, hQ⟩ := sa16q_term_unif hd hp1r hq1 (Or.inr ⟨hqp, hra⟩) 0 hW
  refine ⟨C1 * KQ.toReal, mul_nonneg hC1.le ENNReal.toReal_nonneg, fun {a} ha hdec {ψ} hψ i => ?_⟩
  have hΞ : IsCcInfty (fun y => a y * ψ y) := ⟨ha.mul hψ.1, hψ.2.mul_left⟩
  have h1 := hD1 (sa16z_schw hΞ) i
  refine h1.trans ?_
  have h2 : eLpNorm (⇑(sa16z_schw hΞ)) (ENNReal.ofReal q) volume ≤ KQ * eLpNorm ψ (ENNReal.ofReal p) volume := by
    have hh := hQ ha (fun κ hκ x => hdec κ (by omega) x) (sa16z_schw hψ) (κ := 0) (n := 0) (by omega) le_rfl
    have hcont : Continuous (fun x => ‖iteratedFDeriv ℝ 0 a x‖ * ‖iteratedFDeriv ℝ 0 (⇑(sa16z_schw hψ)) x‖) :=
      ((ha.continuous_iteratedFDeriv (m := 0) (by exact_mod_cast le_top)).norm).mul
        (((sa16z_schw hψ).smooth'.continuous_iteratedFDeriv (m := 0) (by exact_mod_cast le_top)).norm)
    refine le_trans ?_ (hh.trans (mul_le_mul' le_rfl (sa16y5_jet0_le (p := p) hψ.1)))
    refine eLpNorm_mono_real (sa16z_schw hΞ).continuous.aestronglyMeasurable (fun x => ?_)
    simp only [norm_iteratedFDeriv_zero, sa16z_schw_coe, Real.norm_eq_abs, abs_mul]
    exact le_refl _
  calc ENNReal.ofReal C1 * eLpNorm (⇑(sa16z_schw hΞ)) (ENNReal.ofReal q) volume
      ≤ ENNReal.ofReal C1 * (KQ * eLpNorm ψ (ENNReal.ofReal p) volume) := mul_le_mul' le_rfl h2
    _ = ENNReal.ofReal (C1 * KQ.toReal) * eLpNorm ψ (ENNReal.ofReal p) volume := by
        rw [ENNReal.ofReal_mul hC1.le, ENNReal.ofReal_toReal hKQ, mul_assoc]

end Dc1

end HRS.Whole.AppendixA.Phase2SA16R
