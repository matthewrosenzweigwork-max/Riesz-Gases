/-
# HRS.Equilibrium.Q84dAuxC — packet Q84d: a.e. joint measurability of `𝒥ψ` (D3)
-/
import HRS.Equilibrium.Q84dAuxB

open MeasureTheory Filter Topology

noncomputable section

namespace HRS.Q84d

variable {d : ℕ} {s : ℝ}

theorem q84d_volume_ac_mu {ρ : Torus d → ℝ} (hρs : SmoothPosDensity ρ) :
    (volume : Measure (Torus d)) ≪ withDensityReal ρ := by
  unfold withDensityReal
  refine withDensity_absolutelyContinuous' ?_ ?_
  · exact (ENNReal.measurable_ofReal.comp hρs.density.measurable).aemeasurable
  · exact Filter.Eventually.of_forall fun x => by
      simpa using hρs.pos x

theorem q84d_measurable_section {F : Torus d → Torus d → ℝ}
    (h : Measurable (fun p : Torus d × Torus d => F p.1 p.2)) (x : Torus d) :
    Measurable (fun y => F x y) :=
  h.comp (measurable_const.prodMk measurable_id)

/-- Generic form: a kernel which off the diagonal is `S + δ ⊗ 1 + 1 ⊗ δ`. -/
theorem q84d_aesm_of_decomp (hd : 1 ≤ d) {J S : Torus d → Torus d → ℝ} {δ : Torus d → ℝ}
    (hS : Measurable (fun p : Torus d × Torus d => S p.1 p.2))
    (hδ : AEStronglyMeasurable δ (volume : Measure (Torus d)))
    (hJ : ∀ x y : Torus d, x ≠ y → J x y = S x y + δ x + δ y) :
    AEStronglyMeasurable (fun p : Torus d × Torus d => J p.1 p.2) volume := by
  have hfst : AEStronglyMeasurable (fun p : Torus d × Torus d => δ p.1) volume := by
    rw [Measure.volume_eq_prod]
    exact hδ.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hsnd : AEStronglyMeasurable (fun p : Torus d × Torus d => δ p.2) volume := by
    rw [Measure.volume_eq_prod]
    exact hδ.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have h1 : AEStronglyMeasurable (fun p : Torus d × Torus d => S p.1 p.2 + δ p.1 + δ p.2) volume :=
    (hS.aestronglyMeasurable.add hfst).add hsnd
  refine h1.congr ?_
  filter_upwards [q84d_ae_ne_diag hd] with p hp
  exact (hJ p.1 p.2 hp).symm

/-- Structure of `𝒥ψ`: `Jpair = S + δ ⊗ 1 + 1 ⊗ δ` off the diagonal with `S` measurable and `δ`
a.e.-measurable for Haar measure. -/
theorem q84d_jpair_decomp_aesm (hd : 1 ≤ d) (hsd : s < d) {V : Torus d → ℝ} {β : ℝ}
    {ρ : Torus d → ℝ} (hρs : SmoothPosDensity ρ) {f : Torus d → ℝ} (hf : Torus.IsSmooth f)
    {K₁ : ℝ} {ψ : Torus d → Torus d → ℝ} (hψ : IsPairCorrector d s V β ρ f K₁ ψ) :
    ∃ δ : Torus d → ℝ, AEStronglyMeasurable δ (volume : Measure (Torus d)) ∧
      ∀ x y : Torus d, x ≠ y → Jpair d s ρ ψ x y = Ssur d s V β ρ f ψ x y + δ x + δ y := by
  obtain ⟨δ, hδ⟩ := q84d_jpair_decomp hψ
  have hSm : Measurable (fun p : Torus d × Torus d => Ssur d s V β ρ f ψ p.1 p.2) :=
    q84d_measurable_Ssur hsd hf hρs.density
  have hSx := q84d_measurable_section hSm (0 : Torus d)
  have hint : Integrable (Jpair d s ρ ψ 0) (withDensityReal ρ) := (hψ.jpair_canonical 0).1
  have hae : ∀ᵐ y ∂(withDensityReal ρ), y ≠ (0 : Torus d) := by
    have h0 : ∀ᵐ y ∂(volume : Measure (Torus d)), y ≠ (0 : Torus d) := by
      rw [ae_iff]
      simpa using volume_singleton_torus hd 0
    exact (withDensity_absolutelyContinuous _ _).ae_le h0
  have hδμ : AEStronglyMeasurable δ (withDensityReal ρ) := by
    have h1 : AEStronglyMeasurable
        (fun y => Jpair d s ρ ψ 0 y - Ssur d s V β ρ f ψ 0 y - δ 0) (withDensityReal ρ) :=
      (hint.aestronglyMeasurable.sub hSx.aestronglyMeasurable).sub aestronglyMeasurable_const
    refine h1.congr ?_
    filter_upwards [hae] with y hy
    have := hδ 0 y hy.symm
    linarith
  exact ⟨δ, hδμ.mono_ac (q84d_volume_ac_mu hρs), hδ⟩

/-- **D3.**  `𝒥ψ` is almost everywhere equal (for `volume` on `𝕋^d × 𝕋^d`) to a jointly measurable
function: `Jpair d s ρ ψ = S + δ ⊗ 1 + 1 ⊗ δ` off the diagonal with `S` measurable and `δ`
a.e.-measurable. -/
theorem q84d_jpair_aestronglyMeasurable (hd : 1 ≤ d) (hsd : s < d) {V : Torus d → ℝ} {β : ℝ}
    {ρ : Torus d → ℝ} (hρs : SmoothPosDensity ρ) {f : Torus d → ℝ} (hf : Torus.IsSmooth f) {K₁ : ℝ}
    {ψ : Torus d → Torus d → ℝ} (hψ : IsPairCorrector d s V β ρ f K₁ ψ) :
    AEStronglyMeasurable (fun p : Torus d × Torus d => Jpair d s ρ ψ p.1 p.2) volume := by
  obtain ⟨δ, hδm, hδ⟩ := q84d_jpair_decomp_aesm hd hsd hρs hf hψ
  exact q84d_aesm_of_decomp hd (q84d_measurable_Ssur hsd hf hρs.density) hδm hδ

end HRS.Q84d

end
