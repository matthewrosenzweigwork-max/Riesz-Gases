import HRS.MC.S7S7cAux1
import HRS.MC.S7S7bAux13
import HRS.MC.S7S7dAux3
import HRS.MC.S7S7a
import HRS.MC.SEdgeB5a

/-!
# Packet `s7_FC_D3`, sub-statement L2: coordinate second moments of `ζ_N`

`E [ coord_k(ζ_N)^2 ] ≤ C ⟨k⟩^{-2r}` uniformly in `N ≥ 1` (`coord_k ζ_N = sed_Y Q (φ_k)`, `φ_k = ⟨k⟩^{-r} e_k`,
`|φ_k| ≤ √2 ⟨k⟩^{-r}`, and the uniform moment bound `s7b_Y_moment` with `q = 1`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.FCD3

open HRS HRS.Sec7 HRS.MC.SEdge

variable {d : ℕ} {s : ℝ}

/-- **L2** coordinate second moments of `ζ_N` under the modulated Gibbs law. -/
theorem d3_coord_zeta_sq (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 ≤ γ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {r : ℝ} (hr : r = 2 * (d : ℝ) + 6) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N → ∀ k : NonzeroLattice d,
      ∫⁻ X, ENNReal.ofReal (NegSobolev.coord (zetaE r (sed_Q d s N γ ρ) X) k ^ 2) ∂(sed_Q d s N γ ρ) ≤
        ENNReal.ofReal (C * Lattice.jp k.1 ^ (-(2 * r))) := by
  obtain ⟨C, hC0, hC⟩ := HRS.MC.Sec7.S7b.s7b_Y_moment hd hs0 hs hγ hρ 1
  refine ⟨2 * C, by positivity, fun N hN k => ?_⟩
  haveI : IsProbabilityMeasure (sed_Q d s N γ ρ) := HRS.MC.SEdge.B5a.b5a_Q_prob hd hs0 hs hγ hρ hN
  have hr2 : (d : ℝ) < 2 * r := by
    rw [hr]
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hwS : Torus.IsSmooth (s7_phi r k) := HRS.MC.Sec7.S7a.s7a_phi_smooth r k
  have hwc : Continuous (s7_phi r k) := HRS.Q66.q66_cont_of_smooth hwS
  have hT : ∀ x, |s7_phi r k x| ≤ Lattice.jp k.1 ^ (-r) * Real.sqrt 2 := by
    intro x
    have hx : s7_phi r k x = Lattice.jp k.1 ^ (-r) * Torus.realMode k x := rfl
    rw [hx, abs_mul, abs_of_pos (Real.rpow_pos_of_pos (Torus.jp_pos k.1) _)]
    exact mul_le_mul_of_nonneg_left (Torus.abs_realMode_le k x)
      (Real.rpow_nonneg (Torus.jp_pos k.1).le _)
  have hsq : Lattice.jp k.1 ^ (-r) * Lattice.jp k.1 ^ (-r) = Lattice.jp k.1 ^ (-(2 * r)) := by
    rw [← Real.rpow_add (Torus.jp_pos k.1)]
    congr 1
    ring
  have hcoord : ∀ X : Config d N,
      NegSobolev.coord (zetaE r (sed_Q d s N γ ρ) X) k = sed_Y (sed_Q d s N γ ρ) (s7_phi r k) X :=
    fun X => HRS.MC.Sec7.S7c.s7c_coord_zeta hN hr2 (sed_Q d s N γ ρ) X k
  simp only [hcoord]
  have hYm : Measurable (sed_Y (sed_Q d s N γ ρ) (s7_phi r k)) :=
    HRS.MC.Sec7.S7c.s7c_sedY_meas hN _ hwc
  have hint : Integrable (fun X => sed_Y (sed_Q d s N γ ρ) (s7_phi r k) X ^ 2)
      (sed_Q d s N γ ρ) := by
    refine Integrable.of_bound (hYm.pow_const 2).aestronglyMeasurable
      ((Real.sqrt N * (2 * (Lattice.jp k.1 ^ (-r) * Real.sqrt 2))) ^ 2) (ae_of_all _ fun X => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _)
      (HRS.MC.Sec7.S7d.s7d_sedY_bdd hN (sed_Q d s N γ ρ) hT X) 2
  have hnn : 0 ≤ᵐ[sed_Q d s N γ ρ] (fun X => sed_Y (sed_Q d s N γ ρ) (s7_phi r k) X ^ 2) :=
    ae_of_all _ fun X => sq_nonneg _
  refine (le_of_eq (ofReal_integral_eq_lintegral_ofReal hint hnn).symm).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hmom := hC (s7_phi r k) (Lattice.jp k.1 ^ (-r) * Real.sqrt 2) hwS hT N hN
  have habs : ∫ X, sed_Y (sed_Q d s N γ ρ) (s7_phi r k) X ^ 2 ∂(sed_Q d s N γ ρ) =
      ∫ X, |sed_Y (sed_Q d s N γ ρ) (s7_phi r k) X| ^ (2 * 1) ∂(sed_Q d s N γ ρ) := by
    congr 1
    funext X
    rw [mul_one, sq_abs]
  rw [habs]
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have e : (Lattice.jp k.1 ^ (-r) * Real.sqrt 2) ^ (2 * 1) = 2 * Lattice.jp k.1 ^ (-(2 * r)) := by
    calc (Lattice.jp k.1 ^ (-r) * Real.sqrt 2) ^ (2 * 1)
        = (Lattice.jp k.1 ^ (-r) * Lattice.jp k.1 ^ (-r)) * (Real.sqrt 2 * Real.sqrt 2) := by ring
      _ = 2 * Lattice.jp k.1 ^ (-(2 * r)) := by rw [hsq, h2]; ring
  refine hmom.trans (le_of_eq ?_)
  rw [e]
  ring

end HRS.MC.Sec7.FCD3
