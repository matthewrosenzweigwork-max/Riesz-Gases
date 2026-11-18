/-
# HRS.Equilibrium.Q84dAuxY — packet Q84d: strictly measurable modifications of `𝒥ψ`, `B_ψ`, `G_ψ`

`Frozen` statements such as `pair_moments` assume `Measurable (uncurry j)`.  The kernels `𝒥ψ`,
`B_ψ`, `G_ψ` contain `fderiv`-defined quantities whose values on the diagonal are junk, so a
strictly measurable version is only available after modification on a null set of the form
`E × 𝕋^d ∪ 𝕋^d × E ∪ {diagonals}` (with `E` a Haar-null measurable set).  The modifications
`Jt`, `Bt`, `Gt` below are strictly measurable, have the symmetry/canonicity/size properties
required by `pair_moments`, and agree with the originals off that null set; hence
`F_N(Jt) = F_N(𝒥ψ)` etc. `P_{N,β}`-almost surely.
-/
import HRS.Equilibrium.Q84dAuxX
import HRS.Equilibrium.NormalForm

open MeasureTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.Q84d

variable {d : ℕ} {s : ℝ} {N : ℕ}

theorem q84d_jpair_modification (hd : 1 ≤ d) (hsd : s < d) {V : Torus d → ℝ} {β : ℝ}
    {ρ : Torus d → ℝ} (hρs : SmoothPosDensity ρ) {f : Torus d → ℝ} (hf : Torus.IsSmooth f)
    {K₁ : ℝ} {ψ : Torus d → Torus d → ℝ} (hψ : IsPairCorrector d s V β ρ f K₁ ψ) :
    ∃ (E : Set (Torus d)) (Jh : Torus d → Torus d → ℝ), MeasurableSet E ∧
      (volume : Measure (Torus d)) E = 0 ∧ Measurable (fun p : Torus d × Torus d => Jh p.1 p.2) ∧
      ∀ x y : Torus d, x ∉ E → y ∉ E → x ≠ y → Jpair d s ρ ψ x y = Jh x y := by
  obtain ⟨δ, hδm, hδ⟩ := q84d_jpair_decomp_aesm hd hsd hρs hf hψ
  set δ' : Torus d → ℝ := hδm.mk δ with hδ'
  have hδ'm : Measurable δ' := hδm.stronglyMeasurable_mk.measurable
  have hnull : (volume : Measure (Torus d)) {x | δ x ≠ δ' x} = 0 := by
    have := hδm.ae_eq_mk
    rw [Filter.EventuallyEq, ae_iff] at this
    simpa using this
  refine ⟨toMeasurable volume {x | δ x ≠ δ' x},
    fun x y => Ssur d s V β ρ f ψ x y + δ' x + δ' y, measurableSet_toMeasurable _ _, ?_, ?_, ?_⟩
  · rw [measure_toMeasurable]; exact hnull
  · have hS := q84d_measurable_Ssur (V := V) (β := β) (ρ := ρ) (f := f) (ψ := ψ) hsd hf hρs.density
    exact (hS.add (hδ'm.comp measurable_fst)).add (hδ'm.comp measurable_snd)
  · intro x y hxE hyE hxy
    have h1 : δ x = δ' x := by
      by_contra h
      exact hxE (subset_toMeasurable _ _ (show x ∈ {x | δ x ≠ δ' x} from h))
    have h2 : δ y = δ' y := by
      by_contra h
      exact hyE (subset_toMeasurable _ _ (show y ∈ {x | δ x ≠ δ' x} from h))
    rw [hδ x y hxy, h1, h2]

end HRS.Q84d

end
