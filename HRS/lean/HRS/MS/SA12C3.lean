import HRS.MS.SA12C2

/-!
# S.A.12(c), packet E7.06 (part 1): the periodic drift `torusDriftL` is `L`-periodic

For `L`-periodic `G` and `ρ`, `convGradConvL L G ρ` is `L`-periodic (translation invariance of the
integration cell `{y | x - y ∈ [-L/2,L/2)^d}` and of the integrand).  Hence `torusDriftL` is periodic
when `γ`, `μ`, `V` are; this is needed for the box transport integration by parts.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12C

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Construction

variable {d : ℕ}

theorem sa12c_convGradConv_periodic {L : ℝ} {G : Euc d → Euc d} {ρ : Euc d → ℝ}
    (hρ : ∀ (x : Euc d) (k : Fin d → ℤ), ρ (x + L • latticePt k) = ρ x)
    (x : Euc d) (k : Fin d → ℤ) :
    convGradConvL L G ρ (x + L • latticePt k) = convGradConvL L G ρ x := by
  set a : Euc d := L • latticePt k with ha
  set S : Euc d → Set (Euc d) := fun x => {y : Euc d | ∀ i, -(L / 2) ≤ (x - y) i ∧ (x - y) i < L / 2} with hS
  set f : Euc d → Euc d := fun y => (if ‖(x + a) - y‖ ≤ 1 / 4 then (ρ y - ρ (x + a)) • G ((x + a) - y)
    else ρ y • G ((x + a) - y)) with hf
  have h2 := (measurePreserving_add_right (volume : Measure (Euc d)) a).setIntegral_preimage_emb
    (measurableEmbedding_addRight a) f (S (x + a))
  have hpre : (fun y : Euc d => y + a) ⁻¹' S (x + a) = S x := by
    ext y
    simp only [hS, Set.mem_preimage, Set.mem_ofPred_eq]
    have : (x + a - (y + a)) = x - y := by abel
    rw [this]
  rw [hpre] at h2
  unfold convGradConvL
  show ∫ y in S (x + a), f y = ∫ y in S x, _
  rw [← h2]
  congr 1
  funext y
  have e : x + a - (y + a) = x - y := by abel
  have h1 : ρ (y + a) = ρ y := hρ y k
  have h3 : ρ (x + a) = ρ x := hρ x k
  simp only [hf, e, h1, h3]

theorem sa12c_gradient_periodic {L : ℝ} {V : Euc d → ℝ}
    (hV : ∀ (x : Euc d) (k : Fin d → ℤ), V (x + L • latticePt k) = V x)
    (x : Euc d) (k : Fin d → ℤ) :
    gradient V (x + L • latticePt k) = gradient V x := by
  have hfun : (fun y' => V (y' + L • latticePt (d := d) k)) = V := funext fun y' => hV y' k
  have h2 := fderiv_comp_add_right (𝕜 := ℝ) (f := V) (L • latticePt (d := d) k) (x := x)
  rw [hfun] at h2
  unfold gradient
  rw [← h2]

/-- The periodic drift `torusDriftL` of periodic coefficients is periodic. -/
theorem sa12c_torusDrift_periodic {L : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {γ μ V : Euc d → ℝ}
    (hμ : ∀ (x : Euc d) (k : Fin d → ℤ), μ (x + L • latticePt k) = μ x)
    (hV : ∀ (x : Euc d) (k : Fin d → ℤ), V (x + L • latticePt k) = V x)
    (x : Euc d) (k : Fin d → ℤ) :
    torusDriftL M L γ μ V (x + L • latticePt k) = torusDriftL M L γ μ V x := by
  unfold torusDriftL
  rw [sa12c_convGradConv_periodic hμ x k, sa12c_gradient_periodic hV x k]

end HRS.MH.AdjointRd.Phase2SA12C
