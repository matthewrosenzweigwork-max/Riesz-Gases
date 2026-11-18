import HRS.MS.QsfBridge1

/-!
# S4.5 packet B4, part 1: the pointwise generator identity `(★)` and the row bound of the commutator kernel

`s45_star`: for a corrector `χ` of `φ` (`A Lχ = P_μ φ` `μ`-a.e.) there is a constant `c₀` with
`Δχ(x) - β a⟨x,∇χ(x)⟩ - β ∫ h_χ(x,y) dμ(y) = -β φ(x) + c₀` for Lebesgue-a.e. `x`
(`h_χ(x,y) = ⟨∇χ(x)-∇χ(y), ∇g(x-y)⟩` the commutator kernel): the deterministic replacement in the TeX Stein argument.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal RealInnerProductSpace

noncomputable section

namespace S45

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s45_ae_leb_of_ae_mu {ρ : Euc d → ℝ} (hρ : IsProbDensity ρ) (hpos : ∀ y, 0 < ρ y)
    {E : Euc d → Prop} (h : ∀ᵐ x ∂(withDensityReal ρ), E x) :
    ∀ᵐ x ∂(volume : Measure (Euc d)), E x := by
  have hm : AEMeasurable (fun x => ENNReal.ofReal (ρ x)) volume :=
    hρ.measurable.ennreal_ofReal.aemeasurable
  have hac : (volume : Measure (Euc d)) ≪ withDensityReal ρ :=
    withDensity_absolutelyContinuous' hm (Filter.Eventually.of_forall fun x => by
      simpa using hpos x)
  exact hac.ae_le h

/-- The pointwise generator identity (`★`). -/
theorem s45_star (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β C c BU : ℝ}
    (hβ : 0 < β) (hT : ThermalData d s a β C c BU) {χ : Euc d → ℝ} (hχ : ContDiff ℝ 2 χ)
    {B1 B2 : ℝ} (hB1 : ∀ x, ‖gradient χ x‖ ≤ B1) (hB2 : ∀ x, ‖fderiv ℝ (gradient χ) x‖ ≤ B2)
    {φ : Euc d → ℝ}
    (hcorr : ∀ᵐ x ∂(thermalMeasure d s a β),
      susceptibilityOp (rieszKernel d s) (thermalMeasure d s a β) β (thermalGen d s a β χ) x =
        projMean (thermalMeasure d s a β) φ x) :
    ∃ c0 : ℝ, ∀ᵐ x ∂(volume : Measure (Euc d)),
      Laplacian.laplacian χ x - β * (a * ⟪x, gradient χ x⟫) -
        β * ∫ y, commutatorKernel d s (gradient χ) x y ∂(thermalMeasure d s a β) = -β * φ x + c0 := by
  have hUd : Differentiable ℝ (convMeasure (rieszKernel d s) (thermalMeasure d s a β)) :=
    hT.Usmooth.differentiable (by simp)
  obtain ⟨F, hFdef⟩ : ∃ F : Euc d → ℝ, ∀ x, F x = ∫ y, rieszKernel d s (x - y) *
      thermalGen d s a β χ y ∂(thermalMeasure d s a β) := ⟨_, fun _ => rfl⟩
  refine ⟨β * (pair (thermalMeasure d s a β) φ - pair (thermalMeasure d s a β) F),
    s45_ae_leb_of_ae_mu hT.prob hT.pos ?_⟩
  filter_upwards [hcorr] with x hx
  have h1 := s45_corr_identity hd hs0 hsd hT hχ hB1 hB2 x
  rw [h1, ← hFdef x]
  have h2 := s45_gen_eq (χ := χ) hUd x
  have hx' : β⁻¹ * thermalGen d s a β χ x + (F x - pair (thermalMeasure d s a β) F) =
      φ x - pair (thermalMeasure d s a β) φ := by
    have e : (fun x => ∫ y, rieszKernel d s (x - y) * thermalGen d s a β χ y
        ∂(thermalMeasure d s a β)) = F := funext fun x => (hFdef x).symm
    unfold susceptibilityOp Kop projMean at hx
    rw [e] at hx
    exact hx
  have hβ0 : β ≠ 0 := hβ.ne'
  have h3 : thermalGen d s a β χ x + β * (F x - pair (thermalMeasure d s a β) F) =
      β * (φ x - pair (thermalMeasure d s a β) φ) := by
    calc _ = β * (β⁻¹ * thermalGen d s a β χ x + (F x - pair (thermalMeasure d s a β) F)) := by
          field_simp
      _ = _ := by rw [hx']
  have h4 : ⟪a • x + gradient (convMeasure (rieszKernel d s) (thermalMeasure d s a β)) x,
      gradient χ x⟫ = a * ⟪x, gradient χ x⟫ + ⟪gradient (convMeasure (rieszKernel d s)
        (thermalMeasure d s a β)) x, gradient χ x⟫ := by
    rw [inner_add_left, real_inner_smul_left]
  rw [h2, h4] at h3
  have h5 := real_inner_comm (gradient (convMeasure (rieszKernel d s) (thermalMeasure d s a β)) x)
    (gradient χ x)
  rw [h5]
  linarith

end S45

end
