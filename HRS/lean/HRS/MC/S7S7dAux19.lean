import HRS.MC.S7S7dAux18

/-!
# Packet `s7_S7d_uniform_limits`, helper 19: the single-mode estimate for (R3)

For `0 < γ`, a smooth field `v` (the `k`-th transport field) with `E |B_N(v)|^2, E |B_N(v)|^4` bounded, `Q_{lj} = sed_Qt v (a_l) (a_j)`
with `|Q_{lj}| ≤ c τ_l τ_j`:  uniformly over the Stein class and the unit ball,
`E[B_N Df(W_N)[u]] → ½ Σ_{l,j} Q_{lj} ∫ D³f(F)[u,ε_l,ε_j] dG`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7d

open HRS HRS.Sec7 HRS.MC.SEdge HRS.StaticLimitAux

variable {d : ℕ} {s : ℝ} {r : ℝ}

theorem s7d_Qt_congr {ρ : Torus d → ℝ} {v : Fin d → Torus d → ℝ} {f f' g g' : Torus d → ℝ}
    (hf : f =ᵐ[withDensityReal ρ] f') (hg : g =ᵐ[withDensityReal ρ] g') :
    sed_Qt d s ρ v f g = sed_Qt d s ρ v f' g' := by
  unfold sed_Qt
  refine integral_congr_ae ?_
  filter_upwards [hf] with x hx
  refine integral_congr_ae ?_
  filter_upwards [hg] with y hy
  rw [hx, hy]

theorem s7d_tail2_eventually {τ : NonzeroLattice d → ℝ} (hτ : Summable τ) (hτ0 : ∀ j, 0 ≤ τ j)
    {c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 < δ) :
    ∀ᶠ K : Finset (NonzeroLattice d) in atTop,
      c * ((∑' i, τ i) ^ 2 - (∑ i ∈ K, τ i) ^ 2) < δ := by
  set S := ∑' i, τ i with hS
  have hS0 : 0 ≤ S := tsum_nonneg hτ0
  have hev : ∀ᶠ K : Finset (NonzeroLattice d) in atTop,
      S - ∑ i ∈ K, τ i < δ / (2 * c * S + 1) :=
    (tendsto_order.1 (s7d_tail_tendsto hτ)).2 _ (by positivity)
  filter_upwards [hev] with K hK
  have hx0 : 0 ≤ ∑ i ∈ K, τ i := Finset.sum_nonneg fun i _ => hτ0 i
  have hxS : ∑ i ∈ K, τ i ≤ S := hτ.sum_le_tsum K (fun j _ => hτ0 j)
  have h1 : S ^ 2 - (∑ i ∈ K, τ i) ^ 2 ≤ 2 * S * (S - ∑ i ∈ K, τ i) := by nlinarith
  have h2 : c * ((S ^ 2 - (∑ i ∈ K, τ i) ^ 2)) ≤ c * (2 * S * (S - ∑ i ∈ K, τ i)) :=
    mul_le_mul_of_nonneg_left h1 hc
  have h3 : 2 * c * S * (S - ∑ i ∈ K, τ i) ≤ 2 * c * S * (δ / (2 * c * S + 1)) :=
    mul_le_mul_of_nonneg_left hK.le (by positivity)
  have h4 : 2 * c * S * (δ / (2 * c * S + 1)) < δ := by
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
    nlinarith
  nlinarith

end HRS.MC.Sec7.S7d

end
