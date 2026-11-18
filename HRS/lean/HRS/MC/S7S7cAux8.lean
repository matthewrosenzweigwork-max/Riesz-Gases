import HRS.MC.S7S7cAux7

/-!
# Packet `s7_S7c_hilbert_stein`, helper 8: the mode-wise bounds `E|B_k| <= C b_k`, measurability of `A_{kl}`
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7c

open HRS HRS.Sec7 HRS.MC.SEdge HRS.StaticLimitAux

variable {d : ℕ}

theorem s7c_B_mode {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 ≤ γ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {r : ℝ}
    {a : NonzeroLattice d → Torus d → ℝ} {v : NonzeroLattice d → Fin d → Torus d → ℝ} {C₀ : ℝ}
    (hmode : s7_ModeData d s γ ρ r a v C₀) :
    ∃ CB : ℝ, 0 ≤ CB ∧ ∀ (N : ℕ), 1 ≤ N → ∀ k : NonzeroLattice d,
      Integrable (sed_B d s ρ γ (v k)) (sed_Q d s N γ ρ) ∧
      ∫ X, |sed_B d s ρ γ (v k) X| ∂(sed_Q d s N γ ρ) ≤ CB * s7_b k := by
  obtain ⟨CB, hCB0, hCB⟩ := s7c_B_L1 hd hs0 hs hγ hρ
  refine ⟨CB * d * max C₀ 0, by positivity, fun N hN k => ?_⟩
  have hbk : 0 ≤ s7_b k := by unfold s7_b; have := Torus.jp_pos k.1; positivity
  have hL0 : ∀ j, 0 ≤ Torus.cbNorm 1 (v k j) := fun j => HRS.PDE.R2Aux.cbNorm_nonneg' 1 _
  have hLip : ∀ j, HRS.KernelGrad.IsLipschitz (Torus.cbNorm 1 (v k j)) (v k j) := fun j x y =>
    HRS.PDE.R2Aux.isLipschitz_of_cbNorm (HRS.Q66.q66_isCk_of_smooth (hmode.smooth_v k j) 1) x y
  obtain ⟨h1, h2, h3⟩ := hCB (v k) (fun j => Torus.cbNorm 1 (v k j)) hL0 hLip (hmode.smooth_v k) N hN
  refine ⟨h2, h3.trans ?_⟩
  have hsum : ∑ j, Torus.cbNorm 1 (v k j) ≤ d * (max C₀ 0 * s7_b k) := by
    calc ∑ j, Torus.cbNorm 1 (v k j) ≤ ∑ _j : Fin d, (max C₀ 0 * s7_b k) :=
          Finset.sum_le_sum fun j _ => (hmode.bound_v k j).trans
            (by unfold s7_b; gcongr; exact le_max_left _ _)
      _ = _ := by simp
  calc CB * ∑ j, Torus.cbNorm 1 (v k j) ≤ CB * (d * (max C₀ 0 * s7_b k)) :=
        mul_le_mul_of_nonneg_left hsum hCB0
    _ = _ := by ring

theorem s7c_A_meas {N : ℕ} (hN : 1 ≤ N) {r : ℝ} (k l : NonzeroLattice d)
    {v : NonzeroLattice d → Fin d → Torus d → ℝ} (hv : ∀ k j, Torus.IsSmooth (v k j)) :
    Measurable (sed_A (v k) (s7_phi r l) : Config d N → ℝ) := by
  unfold sed_A
  refine HRS.MC.SEdge.B5b.b5b_pair_meas hN ?_
  unfold sed_drift
  refine Finset.measurable_sum _ fun j _ => ?_
  refine Measurable.mul (HRS.Q66.q66_cont_of_smooth (hv k j)).measurable ?_
  exact (HRS.Q66.q66_cont_of_smooth
    (HRS.Q66.q66_isSmooth_partialDeriv (HRS.MC.Sec7.S7a.s7a_phi_smooth r l) j)).measurable

end HRS.MC.Sec7.S7c

end
