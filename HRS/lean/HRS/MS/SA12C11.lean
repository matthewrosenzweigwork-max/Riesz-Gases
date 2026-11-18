import HRS.MS.SA12C10

/-!
# S.A.12(c), packet E7.06 (part 9): the box energy bound from a box nonlocal inequality

Let `F` be a classical solution of `∂_τF = νΔF + b·∇F + G` with `L`-periodic `F(τ)`, `b(τ)`.  If, for every `τ`,
`2⟨F, G⟩_{m,L} ≤ κ D_{m,L} + A E_{m,L}` with `κ ≤ 2ν`, then `E_{m,L}(F τ) ≤ exp((Λ_b + A)τ) E_{m,L}(F 0)`
with the explicit `Λ_b = (d+1)^m (d C_b + 1 + (d C_b 2^m)² c_T)`.  (E7.05 supplies the inequality for
`G = -𝒢_L[F]`; the constants `κ, A` are chosen before `L, ν₀`.)
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12C

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Construction HRS.MH.AdjointRd.Phase2SA12Near HRS.MS.UniqT3
open HRS.MH.AdjointRd.Phase2SA12

variable {d : ℕ}

theorem sa12c_box_energy_deriv {m : ℕ} {Cb T t ν : ℝ} {b : ℝ → Euc d → Euc d}
    (hb : IsAdvectingDrift m Cb T b) {G F : ℝ → Euc d → ℝ} (hF : IsClassicalSol m ν b G t F)
    (htT : t ≤ T) (L : ℝ) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) t) :
    HasDerivWithinAt (fun τ' => boxEnergy m L (F τ'))
      (∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d,
        ∫ x in periodBox d L, 2 * (partialDeriv idx (F τ) x * partialDeriv idx
          (fun y => ν * Laplacian.laplacian (F τ) y + inner ℝ (b τ y) (gradient (F τ) y) + G τ y) x))
      (Icc (0 : ℝ) t) τ := by
  unfold boxEnergy
  refine HasDerivWithinAt.fun_sum fun j hj => ?_
  refine HasDerivWithinAt.const_mul _ ?_
  refine HasDerivWithinAt.fun_sum fun idx _ => ?_
  exact sa12c_energy_term_deriv hb hF htT L (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) idx hτ

/-- **E7.06 core.** -/
theorem sa12c_box_energy_bound {m : ℕ} {Cb T t ν L κ A : ℝ} {b : ℝ → Euc d → Euc d}
    (hb : IsAdvectingDrift m Cb T b) {G F : ℝ → Euc d → ℝ} (hF : IsClassicalSol m ν b G t F)
    (htT : t ≤ T) (hL : 0 < L)
    (hFp : ∀ τ ∈ Icc (0 : ℝ) t, ∀ (x : Euc d) (k : Fin d → ℤ), F τ (x + L • latticePt k) = F τ x)
    (hbp : ∀ τ ∈ Icc (0 : ℝ) T, ∀ (x : Euc d) (k : Fin d → ℤ), b τ (x + L • latticePt k) = b τ x)
    (hκ : κ ≤ 2 * ν)
    (hnl : ∀ τ ∈ Icc (0 : ℝ) t, 2 * boxJetPair m L (F τ) (G τ) ≤
      κ * boxDissip m L (F τ) + A * boxEnergy m L (F τ)) :
    ∀ τ ∈ Icc (0 : ℝ) t, boxEnergy m L (F τ) ≤
      Real.exp ((((d : ℝ) + 1) ^ m * sa12cK d m Cb + A) * τ) * boxEnergy m L (F 0) := by
  refine sa12c_gronwall (E := fun τ => boxEnergy m L (F τ)) (E' := fun τ =>
    ∑ j ∈ Finset.range (m + 1), (Nat.choose m j : ℝ) * ∑ idx : Fin j → Fin d,
        ∫ x in periodBox d L, 2 * (partialDeriv idx (F τ) x * partialDeriv idx
          (fun y => ν * Laplacian.laplacian (F τ) y + inner ℝ (b τ y) (gradient (F τ) y) + G τ y) x))
    (fun τ hτ => sa12c_box_energy_deriv hb hF htT L hτ) ?_
  intro τ hτ
  have hτT : τ ∈ Icc (0 : ℝ) T := ⟨hτ.1, hτ.2.trans htT⟩
  have h1 := sa12c_box_rate_le hL (hF.smooth τ hτ).1 (hF.smooth τ hτ).2 (hFp τ hτ)
    (hb.smooth τ hτT) (hbp τ hτT) (hb.deriv_bdd τ hτT) ν
  have h2 := hnl τ hτ
  have h3 := boxDissip_nonneg m L (F τ)
  have h4 : (κ - 2 * ν) * boxDissip m L (F τ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) h3
  show _ ≤ (((d : ℝ) + 1) ^ m * sa12cK d m Cb + A) * boxEnergy m L (F τ)
  nlinarith [h1, h2, h4]

end HRS.MH.AdjointRd.Phase2SA12C
