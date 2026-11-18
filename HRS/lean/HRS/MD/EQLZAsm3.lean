import HRS.MD.EQLZAsm2
import HRS.MD.EQLZCap10
import HRS.MD.EQLZMarg

/-!
# EQ-LZ packet ASM, part 3: `eqlz_assembly_proof`

The frozen `lyonsZheng_maximal_family` (copied verbatim from `HRS/Stochastic/LyonsZhengSpec.lean`) from
`SmoothMaximal` (packet SM), the approximation lemma (packet CAP, `eqlz_cap_proof`) and the stationarity of the marginals
(packet MARG, `eqlz_marg_proof`).  Tie to the specification in `EQLZAsmTie.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.MD.EQLZ.Asm

/-- From a countable set of times to its finite subsets (monotone convergence). -/
theorem asm_countable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (f : ℝ → Ω → ℝ≥0∞) (R : Set ℝ)
    (hR : R.Countable) (hf : ∀ t ∈ R, Measurable (f t)) (B : ℝ≥0∞)
    (h : ∀ S : Finset ℝ, (S : Set ℝ) ⊆ R → ∫⁻ ω, ⨆ t ∈ (S : Set ℝ), f t ω ∂P ≤ B) :
    ∫⁻ ω, ⨆ t ∈ R, f t ω ∂P ≤ B := by
  rcases R.eq_empty_or_nonempty with hRe | hne
  · subst hRe; simp
  obtain ⟨e, he⟩ := hR.exists_eq_range hne
  let S : ℕ → Finset ℝ := fun n => (Finset.range (n + 1)).image e
  have hSR : ∀ n, ((S n : Finset ℝ) : Set ℝ) ⊆ R := by
    intro n t ht
    simp only [S, Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at ht
    obtain ⟨i, -, rfl⟩ := ht
    rw [he]; exact Set.mem_range_self i
  let g : ℕ → Ω → ℝ≥0∞ := fun n ω => ⨆ t ∈ ((S n : Finset ℝ) : Set ℝ), f t ω
  have hgm : ∀ n, Measurable (g n) := fun n =>
    Measurable.biSup _ (S n).countable_toSet fun t ht => hf t (hSR n ht)
  have hmono : Monotone g := by
    intro m n hmn ω
    refine iSup₂_le fun t ht => le_iSup₂ (f := fun t (_ : t ∈ ((S n : Finset ℝ) : Set ℝ)) => f t ω) t ?_
    simp only [S, Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio] at ht ⊢
    obtain ⟨i, hi, rfl⟩ := ht
    exact ⟨i, by omega, rfl⟩
  have hle : ∀ ω, ⨆ t ∈ R, f t ω ≤ ⨆ n, g n ω := by
    intro ω
    refine iSup₂_le fun t ht => ?_
    rw [he] at ht
    obtain ⟨i, rfl⟩ := ht
    refine (le_iSup₂ (f := fun t (_ : t ∈ ((S i : Finset ℝ) : Set ℝ)) => f t ω) (e i) ?_).trans
      (le_iSup (fun n => g n ω) i)
    simp only [S, Finset.coe_image, Finset.coe_range, Set.mem_image, Set.mem_Iio]
    exact ⟨i, by omega, rfl⟩
  calc ∫⁻ ω, ⨆ t ∈ R, f t ω ∂P ≤ ∫⁻ ω, ⨆ n, g n ω ∂P := lintegral_mono hle
    _ = ⨆ n, ∫⁻ ω, g n ω ∂P := lintegral_iSup hgm hmono
    _ ≤ B := iSup_le fun n => h (S n) (hSR n)

end HRS.MD.EQLZ.Asm

end
