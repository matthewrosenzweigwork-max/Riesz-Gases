import HRS.MC.S7PIH6Heat

/-!
# Packet piH, part 7: the pair estimate for the backward heat equation
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MatrixOrder

noncomputable section

namespace HRS.MC.Sec7.S7PIH

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIS3

variable {q : ℕ} {a b : ℝ} {A S : ℝ → Matrix (Fin q) (Fin q) ℝ}

/-- Uniform modulus of continuity of `D²F(s)` near `(r, c)`. -/
theorem S7PIH_modulus (hab : a ≤ b)
    (hA : ∀ i j, ContinuousOn (fun v => A v i j) (Set.Icc a b))
    (hApsd : ∀ v ∈ Set.Icc a b, (A v).PosSemidef) (hSb : (S b).PosSemidef)
    (hS : ∀ u ∈ Set.Icc a b, ∀ i j, S u i j = S b i j + ∫ v in Set.Ioc u b, A v i j)
    {G : EuclideanSpace ℝ (Fin q) → ℝ} (hG : MemCb 2 G) (c : EuclideanSpace ℝ (Fin q))
    {r : ℝ} (hr : r ∈ Set.Icc a b) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ0 > 0, ∃ η0 > 0, ∀ s ∈ Set.Icc a b, |s - r| < η0 → ∀ y, ‖y - c‖ ≤ δ0 →
      ‖iteratedFDeriv ℝ 2 (gaussHeat S G s) y - iteratedFDeriv ℝ 2 (gaussHeat S G s) c‖ ≤ ε := by
  have hcont := S7PIH_heat_cont_ab hab hA hApsd hSb hS hG (le_refl 2)
  have hcw := hcont (r, c) ⟨hr, Set.mem_univ _⟩
  rw [Metric.continuousWithinAt_iff] at hcw
  obtain ⟨δ', hδ', h⟩ := hcw (ε / 2) (by linarith)
  refine ⟨δ' / 2, by positivity, δ', hδ', fun s hs hsr y hy => ?_⟩
  have h1 := h (show (s, y) ∈ Set.Icc a b ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin q))) from ⟨hs, Set.mem_univ _⟩) (by
    rw [Prod.dist_eq]
    refine max_lt ?_ ?_
    · simpa [Real.dist_eq] using hsr
    · simp only [dist_eq_norm]
      calc ‖y - c‖ ≤ δ' / 2 := hy
        _ < δ' := by linarith)
  have h2 := h (show (s, c) ∈ Set.Icc a b ×ˢ (Set.univ : Set (EuclideanSpace ℝ (Fin q))) from ⟨hs, Set.mem_univ _⟩) (by
    rw [Prod.dist_eq]
    refine max_lt ?_ ?_
    · simpa [Real.dist_eq] using hsr
    · simpa using hδ')
  simp only [dist_eq_norm] at h1 h2
  calc _ = ‖(iteratedFDeriv ℝ 2 (gaussHeat S G s) y - iteratedFDeriv ℝ 2 (gaussHeat S G r) c) -
        (iteratedFDeriv ℝ 2 (gaussHeat S G s) c - iteratedFDeriv ℝ 2 (gaussHeat S G r) c)‖ := by
          congr 1; abel
    _ ≤ ‖iteratedFDeriv ℝ 2 (gaussHeat S G s) y - iteratedFDeriv ℝ 2 (gaussHeat S G r) c‖ +
        ‖iteratedFDeriv ℝ 2 (gaussHeat S G s) c - iteratedFDeriv ℝ 2 (gaussHeat S G r) c‖ :=
          norm_sub_le _ _
    _ ≤ ε := by linarith

end HRS.MC.Sec7.S7PIH

end
