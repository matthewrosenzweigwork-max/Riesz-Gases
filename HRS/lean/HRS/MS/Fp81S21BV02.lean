import HRS.MS.Fp81S21BV0

/-! Algebraic estimates for the total variation of vector-valued paths. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Set
open scoped ENNReal BigOperators
namespace HRS.Fp81.S21

variable {E : Type*} [NormedAddCommGroup E]

theorem fp81s21_eVariationOn_add_le (f g : ℝ → E) (s : Set ℝ) :
    eVariationOn (fun x => f x + g x) s ≤ eVariationOn f s + eVariationOn g s := by
  unfold eVariationOn at *
  apply iSup_le
  rintro ⟨n, u, hu, hs⟩
  calc
    (∑ i ∈ Finset.range n, edist (f (u (i + 1)) + g (u (i + 1)))
        (f (u i) + g (u i))) ≤
        ∑ i ∈ Finset.range n, (edist (f (u (i + 1))) (f (u i)) +
          edist (g (u (i + 1))) (g (u i))) := by
            apply Finset.sum_le_sum
            intro i hi
            exact edist_add_add_le _ _ _ _
    _ = (∑ i ∈ Finset.range n, edist (f (u (i + 1))) (f (u i))) +
        (∑ i ∈ Finset.range n, edist (g (u (i + 1))) (g (u i))) := Finset.sum_add_distrib
    _ ≤ (⨆ p : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ s},
          ∑ i ∈ Finset.range p.1, edist (f (p.2.1 (i + 1))) (f (p.2.1 i))) +
        (⨆ p : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ s},
          ∑ i ∈ Finset.range p.1, edist (g (p.2.1 (i + 1))) (g (p.2.1 i))) := by
            exact add_le_add (eVariationOn.sum_le hu hs) (eVariationOn.sum_le hu hs)

theorem fp81s21_boundedVariationOn_add {f g : ℝ → E} {s : Set ℝ}
    (hf : BoundedVariationOn f s) (hg : BoundedVariationOn g s) :
    BoundedVariationOn (fun x => f x + g x) s := by
  exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hf, hg⟩) (fp81s21_eVariationOn_add_le f g s)

#print axioms fp81s21_eVariationOn_add_le
#print axioms fp81s21_boundedVariationOn_add
end HRS.Fp81.S21
end
