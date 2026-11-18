import HRS.MC.S7S7cAux3
import HRS.MC.SEdgeB2b

/-!
# Packet `s7_S7c_hilbert_stein`, helper 4: weighted deterministic bounds

(a) `|A_{N,kl}| <= C b_k b_l` deterministically; (b) the envelope `|h_v| <= K (sum L_j)(g + c)` with an explicit
dependence on the Lipschitz constants `L_j` of `v_j`; (c) the `L^2(mu x mu)` bound `||h_v||^2 <= G (sum L_j)^2`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7c

open HRS HRS.Sec7 HRS.MC.SEdge HRS.StaticLimitAux

open Classical

variable {d : ℕ}

/-! ### (a) the deterministic bound on `A` -/

theorem s7c_jp_exp_le {r : ℝ} (hr : r = 2 * (d : ℝ) + 6) (k : NonzeroLattice d) :
    Lattice.jp k.1 ^ (1 - r) ≤ s7_b k := by
  unfold s7_b
  refine Real.rpow_le_rpow_of_exponent_le (Torus.jp_ge_one _) ?_
  rw [hr]; push_cast; linarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]

theorem s7c_dphi_bound {r : ℝ} (hr : r = 2 * (d : ℝ) + 6) (l : NonzeroLattice d) (j : Fin d)
    (x : Torus d) : |Torus.partialDeriv j (s7_phi r l) x| ≤ 2 * Real.sqrt 2 * s7_b l := by
  have hjp := Torus.jp_pos l.1
  have hcb : Torus.cbNorm 1 (s7_phi r l) ≤ 2 * Real.sqrt 2 * Lattice.jp l.1 ^ (1 - r) := by
    rw [HRS.MC.Sec7.S7a.s7a_phi_eq_trig]
    refine (HRS.PDE.MFPair.cbNorm_trigTerm_le _ _ l.1 1).trans ?_
    have hab : |(if Lattice.IsPosHalf l.1 then Real.sqrt 2 * Lattice.jp l.1 ^ (-r) else 0)| +
        |(if Lattice.IsPosHalf l.1 then 0 else Real.sqrt 2 * Lattice.jp l.1 ^ (-r))| =
        Real.sqrt 2 * Lattice.jp l.1 ^ (-r) := by
      have h0 : 0 ≤ Real.sqrt 2 * Lattice.jp l.1 ^ (-r) := by positivity
      by_cases h : Lattice.IsPosHalf l.1
      · simp [h, abs_of_nonneg h0]
      · simp [h, abs_of_nonneg h0]
    rw [hab]
    have : Lattice.jp l.1 ^ (1 - r) = Lattice.jp l.1 ^ (1 : ℕ) * Lattice.jp l.1 ^ (-r) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hjp]; norm_num; ring_nf
    rw [this]
    norm_num
    nlinarith [mul_nonneg (Real.sqrt_nonneg 2) (Real.rpow_nonneg hjp.le (-r))]
  have h1 := HRS.PDE.abs_partialDeriv_le_cbNorm_one j (s7_phi r l)
    (HRS.Q66.q66_isCk_of_smooth (HRS.MC.Sec7.S7a.s7a_phi_smooth r l) 1) x
  have h2 := s7c_jp_exp_le hr l
  calc _ ≤ Torus.cbNorm 1 (s7_phi r l) := h1
    _ ≤ 2 * Real.sqrt 2 * Lattice.jp l.1 ^ (1 - r) := hcb
    _ ≤ 2 * Real.sqrt 2 * s7_b l := by gcongr

theorem s7c_A_bound {s : ℝ} {γ : ℝ} {ρ : Torus d → ℝ} {r : ℝ} (hr : r = 2 * (d : ℝ) + 6)
    {a : NonzeroLattice d → Torus d → ℝ} {v : NonzeroLattice d → Fin d → Torus d → ℝ} {C₀ : ℝ}
    (hmode : s7_ModeData d s γ ρ r a v C₀) :
    ∃ CA : ℝ, 0 ≤ CA ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (k l : NonzeroLattice d) (X : Config d N),
      |sed_A (v k) (s7_phi r l) X| ≤ CA * s7_b k * s7_b l := by
  refine ⟨d * max C₀ 0 * (2 * Real.sqrt 2), by positivity, fun N hN k l X => ?_⟩
  have hbk : 0 ≤ s7_b k := by unfold s7_b; have := Torus.jp_pos k.1; positivity
  have hbl : 0 ≤ s7_b l := by unfold s7_b; have := Torus.jp_pos l.1; positivity
  have hv : ∀ j x, |v k j x| ≤ max C₀ 0 * s7_b k := fun j x => by
    have h1 := HRS.PDE.R2Aux.abs_le_cbNorm
      (HRS.Q66.q66_isCk_of_smooth (hmode.smooth_v k j) 1) x
    exact h1.trans ((hmode.bound_v k j).trans (by unfold s7_b; gcongr; exact le_max_left _ _))
  have hdr : ∀ x, |sed_drift (v k) (s7_phi r l) x| ≤ d * (max C₀ 0 * s7_b k) *
      (2 * Real.sqrt 2 * s7_b l) := by
    intro x
    unfold sed_drift
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j, |v k j x * Torus.partialDeriv j (s7_phi r l) x|
        ≤ ∑ _j : Fin d, (max C₀ 0 * s7_b k) * (2 * Real.sqrt 2 * s7_b l) := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [abs_mul]
          exact mul_le_mul (hv j x) (s7c_dphi_bound hr l j x) (abs_nonneg _) (by positivity)
      _ = _ := by simp; ring
  have := HRS.MC.SEdge.B5b.b5b_pair_bdd hN hdr X
  unfold sed_A
  calc _ ≤ _ := this
    _ = _ := by ring

end HRS.MC.Sec7.S7c

end
