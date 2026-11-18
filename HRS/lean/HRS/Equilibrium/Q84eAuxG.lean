/-
# HRS.Equilibrium.Q84eAuxG — packet Q84e: `(√N/2) D_μ(h_f) = F_N(H_f) - (2/N) ζ-term + const`

Pointwise (every configuration), purely algebraic from `H_f = ½ P_xP_y h_f`,
`a_f = ½ ∫h_f(·,y)μ(dy)` and the symmetry of `h_f` (`∇g` odd); the constant is
`c₀ / (2√N)` with `c₀ = μ^{⊗2}(h_f)` (source line 4961).
-/
import HRS.Equilibrium.Q84eAuxF

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84e

open HRS.Q84d

variable {d : ℕ} {s : ℝ} {N : ℕ}

theorem q84e_hTransport_symm (hsd : s < d) (f : Torus d → ℝ) (x y : Torus d) :
    hTransport d s f x y = hTransport d s f y x := by
  unfold hTransport
  have e : y - x = -(x - y) := by abel
  rw [e, HRS.KernelGrad.periodicRieszGrad_neg_of_lt hsd]
  have e2 : Torus.grad f y - Torus.grad f x = -(Torus.grad f x - Torus.grad f y) := by abel
  rw [e2, inner_neg_neg]

/-- `H_f = ½ h_f - a_f(x) - a_f(y) + ½ c₀`. -/
theorem q84e_Hsource_eq (hsd : s < d) (ρ f : Torus d → ℝ) (x y : Torus d) :
    Hsource d s ρ f x y = (1 / 2) * hTransport d s f x y - aCoef d s ρ f x - aCoef d s ρ f y +
      (1 / 2) * ∫ x', ∫ y', hTransport d s f x' y' ∂(withDensityReal ρ) ∂(withDensityReal ρ) := by
  have h2 : ∫ x', hTransport d s f x' y ∂(withDensityReal ρ) =
      ∫ x', hTransport d s f y x' ∂(withDensityReal ρ) :=
    integral_congr_ae (Filter.Eventually.of_forall fun x' => q84e_hTransport_symm hsd f x' y)
  unfold Hsource canonicalCenter aCoef
  rw [h2]
  ring

theorem q84e_pairSum_H (ρ f : Torus d → ℝ) (C : ℝ) (h : Torus d → Torus d → ℝ) (a : Torus d → ℝ)
    (hN : 1 ≤ N) (X : Config d N) :
    pairSumOrdered (fun x y => (1 / 2) * h x y - a x - a y + C) X =
      (1 / 2) * pairSumOrdered h X - 2 * ((N : ℝ) - 1) * ∑ i, a (X i) +
        (N : ℝ) * ((N : ℝ) - 1) * C := by
  have hcard : ∀ i : Fin N, ((Finset.univ.erase i).card : ℝ) = (N : ℝ) - 1 := by
    intro i
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
      Nat.cast_sub hN]
    simp
  have hswap := q84e_pair_swap (N := N) (fun i j => a (X i))
  unfold pairSumOrdered
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hswap]
  simp only [Finset.sum_const, nsmul_eq_mul, hcard]
  simp only [Finset.card_univ, Fintype.card_fin, ← Finset.mul_sum]
  ring

theorem q84e_rpow_three_half (hN : 0 < N) :
    (N : ℝ) ^ (-(3 / 2 : ℝ)) = 1 / ((N : ℝ) * Real.sqrt N) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.rpow_neg hNp.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hNp,
    Real.rpow_one, ← Real.sqrt_eq_rpow]
  simp

theorem q84e_quad_alg (hN : 1 ≤ N) (hsd : s < d) (ρ f : Torus d → ℝ) (X : Config d N) :
    Real.sqrt N / 2 * quadStat (hTransport d s f) (withDensityReal ρ) X =
      Fstat (Hsource d s ρ f) X -
        (2 / (N : ℝ)) * (Real.sqrt N * ((1 / (N : ℝ)) * ∑ i, aCoef d s ρ f (X i))) +
        (1 / (2 * Real.sqrt N)) *
          ∫ x', ∫ y', hTransport d s f x' y' ∂(withDensityReal ρ) ∂(withDensityReal ρ) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hr : 0 < Real.sqrt N := Real.sqrt_pos.2 hNp
  have hrr : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hNp.le
  set c₀ := ∫ x', ∫ y', hTransport d s f x' y' ∂(withDensityReal ρ) ∂(withDensityReal ρ) with hc₀
  have hH : Hsource d s ρ f = fun x y => (1 / 2) * hTransport d s f x y - aCoef d s ρ f x -
      aCoef d s ρ f y + (1 / 2) * c₀ := funext fun x => funext fun y => q84e_Hsource_eq hsd ρ f x y
  have hint : ∀ i : Fin N, ∫ y, hTransport d s f (X i) y ∂(withDensityReal ρ) =
      2 * aCoef d s ρ f (X i) := by
    intro i; unfold aCoef; ring
  unfold quadStat Fstat
  rw [hH, q84e_pairSum_H ρ f ((1 / 2) * c₀) (hTransport d s f) (aCoef d s ρ f) hN X,
    q84e_rpow_three_half (by omega : 0 < N)]
  simp only [hint, ← Finset.mul_sum, ← hc₀]
  unfold pairSumOrdered
  field_simp
  rw [Real.sq_sqrt hNp.le]
  ring

end HRS.Q84e

end
