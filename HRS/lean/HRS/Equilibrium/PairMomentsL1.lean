/-
# HRS.Equilibrium.PairMomentsL1 -- the first level of the three-particle estimate (EQ-01b)
-/
import HRS.Equilibrium.PairMomentsL2

open MeasureTheory ProbabilityTheory Filter Topology Function
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.PairMom

open HRS HRS.External HRS.Quad HRS.External.PoleVar

variable {d : ℕ} {s : ℝ}

section Reindex

theorem sum_erase_succAbove {n : ℕ} (i : Fin (n + 1)) (f : Fin (n + 1) → ℝ) :
    ∑ j ∈ Finset.univ.erase i, f j = ∑ a : Fin n, f (i.succAbove a) := by
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), Fin.sum_univ_succAbove _ i]
  ring

theorem tripleB_insertAt (g3 : Torus d → Torus d → Torus d → ℝ) {n : ℕ} (i : Fin (n + 1)) (x : Torus d)
    (y : Fin n → Torus d) :
    tripleB g3 i x (insertAt i x y) = pairSumOrdered (g3 x) y := by
  unfold tripleB pairSumOrdered
  rw [sum_erase_succAbove i (fun j => ∑ k ∈ (Finset.univ.erase i).erase j, g3 x (insertAt i x y j) (insertAt i x y k))]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h1 : i.succAbove a ∈ Finset.univ.erase i := Finset.mem_erase.2 ⟨Fin.succAbove_ne i a, Finset.mem_univ _⟩
  simp only [insertAt_succAbove]
  rw [Finset.sum_erase_eq_sub h1, sum_erase_succAbove i (fun k => g3 x (y a) (insertAt i x y k)),
    Finset.sum_erase_eq_sub (Finset.mem_univ a)]
  simp [insertAt_succAbove]

end Reindex

section Level1

theorem level1_bound (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (ρ : Torus d → ℝ) (hρ : SmoothPosDensity ρ) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)
    (Mmax M'max γmax Cq : ℝ) (hCq : 0 ≤ Cq) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V : WeakPotential (withDensityReal ρ)),
      PotBound (d := d) s c Mmax M'max γmax Cq V → ∀ m : ℕ, 1 ≤ m → weakKappa V β ≤ 1 / 2 →
      ∀ (K A : ℝ), 0 ≤ A → ∀ (g3 : Torus d → Torus d → Torus d → ℝ),
      Measurable (fun p : Torus d × Torus d × Torus d => g3 p.1 p.2.1 p.2.2) →
      IsSymmTriple g3 →
      (∀ x y z, x ≠ y → x ≠ z → y ≠ z → |g3 x y z| ≤ K * tEnv s x y z) →
      (∀ x u : Torus d, x ≠ u →
        |∑ k : Fin m, ∫ z, g3 x u z ∂((pinnedLaw V (β / ((m + 2 : ℕ) : ℝ)) m
          (pinsWith (pinsWith (fun e : Empty => e.elim) x) u)).map (fun Y => Y k))| ≤
          A * (wEnv s x u * (logEN (m + 2) + ellEnv x u))) →
      ∀ i : Fin (m + 2),
        ∫⁻ Y, ‖tripleB g3 i (Y i) Y‖ₑ ^ 2
            ∂(pinnedLaw V (β / ((m + 2 : ℕ) : ℝ)) (m + 2) (fun e : Empty => e.elim)) ≤
          ENNReal.ofReal (C * (K ^ 2 + A ^ 2) * ((m + 2 : ℕ) : ℝ) ^ 2 * logEN (m + 2) ^ 2) := by
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ.density
  obtain ⟨C, hC0, hC⟩ := level2_bound hd hcrit β hβ ρ hρ c hc Mmax M'max γmax Cq hCq
  refine ⟨C, hC0, fun V hV m hm1 hκ K A hA g3 hgm hsym hg3 hMean i => ?_⟩
  have hlam0 : 0 ≤ β / ((m + 2 : ℕ) : ℝ) := by positivity
  have hΦ : Measurable fun Y : Fin (m + 1 + 1) → Torus d => ‖tripleB g3 i (Y i) Y‖ₑ ^ 2 :=
    (measurable_tripleB hgm i).enorm.pow_const 2
  rw [lintegral_pinned_succ V hlam0 (fun e : Empty => e.elim) i hΦ]
  calc _ ≤ ∫⁻ x, pinWeight V (β / ((m + 2 : ℕ) : ℝ)) (fun e : Empty => e.elim) (m + 1) x *
        ENNReal.ofReal (C * (K ^ 2 + A ^ 2) * ((m + 2 : ℕ) : ℝ) ^ 2 * logEN (m + 2) ^ 2) ∂(withDensityReal ρ) := by
        refine lintegral_mono fun x => mul_le_mul' le_rfl ?_
        simp only [insertAt_same, tripleB_insertAt]
        exact hC V hV m hm1 hκ K A hA g3 hgm hsym hg3 hMean x
    _ = _ := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
          lintegral_pinWeight V hlam0 (fun e : Empty => e.elim) i (0 : Fin (m + 1)), one_mul]

end Level1

end HRS.PairMom

end
