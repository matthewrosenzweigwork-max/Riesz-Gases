import HRS.Sections.ScrnAux26

/-!
# Packet SCRN, part 27: the probabilistic setting and measurability of the remainder

`ScrnFlow` bundles the hypotheses on the particle system of `screening_comparison`.  `scrn_rem_aemeas`:
the remainder vector `R` is a.e. measurable (it equals `Z - ∑_i N^{-1/2}(f(x_i) - m) - M_T` a.s.).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

open HRS.Main.A8P

variable {d : ℕ}

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

/-- The hypotheses on the Haar-started free particle system of Proposition 6.1. -/
structure ScrnFlow (d : ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β) (N : ℕ)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) (X₀ : Ω → Config d N)
    (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N) : Prop where
  brownian : IsVectorBrownian P W
  indep : IndepFun X₀ (fun ω => fun t : ℝ≥0 => W t ω) P
  law : P.map X₀ = Measure.pi (fun _ : Fin N => (volume : Measure (Torus d)))
  sol : ∀ T' : ℝ, 0 ≤ T' → IsStrongSolution P (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) T' X₀ W X
  filt : ∃ (ℱ : MeasureTheory.Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
    IsFilteredSolution P ℱ W' W X

theorem ScrnFlow.law0 {s : ℝ} {hs0 : 0 ≤ s} {hsd : s < d} {β : ℝ} {hβ : 0 < β} {N : ℕ}
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {X₀ : Ω → Config d N}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (h : ScrnFlow d hs0 hsd β hβ N P X₀ W X) :
    P.map (X 0) = Measure.pi (fun _ : Fin N => (volume : Measure (Torus d))) := by
  rw [← h.law]
  exact Measure.map_congr (h.sol 0 le_rfl).init

theorem scrn_rem_aemeas (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    {N : ℕ} (hN : 2 ≤ N) {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Config d N} {ℱ : MeasureTheory.Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} (hF : IsFilteredSolution P ℱ W' W X) {T : ℝ} (hT : 0 ≤ T)
    (hsolT : IsStrongSolution P (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) T X₀ W X)
    {p : ℕ} (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc 0 T) (ψ : Fin p → Torus d → ℝ)
    (hψ2 : ∀ a, Torus.IsCk 2 (ψ a)) (f : Fin p → ℝ → Torus d → ℝ)
    (hf : ∀ a, (ts a = 0 ∧ f a = fun _ => ψ a) ∨ (0 < ts a ∧ IsClassicalAdjointSolution
      (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) (fun _ _ => (1 : ℝ)) (ts a) (ψ a) (f a)))
    (hC12 : ∀ a, ∃ ft, IsC12Test (ts a) (f a) ft) (hfc : ∀ a, Continuous (f a 0)) :
    AEMeasurable (scrnRem (PDE.mfData d s hs0 hsd (fun _ => 0) β hβ) f ts X) P := by
  set D := PDE.mfData d s hs0 hsd (fun _ => 0) β hβ with hD
  have hXm : ∀ r : ℝ≥0, Measurable (X r) := fun r => (hF.adapted r).mono (ℱ.le _) le_rfl
  obtain ⟨hmart, -⟩ := scrn_vector_mart (D := D) hF ts (fun a => (hts a).1) (fun a => (hts a).2) f hC12
    (Real.sqrt N)
  have hdec := scrn_decomp hd hs0 hsd β hβ hN hF hsolT ts hts ψ hψ2 f hf hC12 hfc
  have hZm : Measurable (scrnZ ψ ts X) := by
    unfold scrnZ
    refine (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun a => ?_)
    have h := a8p_flucPair_meas (hXm (Real.toNNReal (ts a))) (hψ2 a |> scrn_cont_of_ck2)
      (fun _ => (1 : ℝ))
    have e : (fun ω => linCoord (volume : Measure (Torus d)) (ψ a) (X (Real.toNNReal (ts a)) ω)) =
        fun ω => Real.sqrt N * flucPair (X (Real.toNNReal (ts a)) ω) (fun _ => (1 : ℝ)) (ψ a) := by
      funext ω; exact scrn_linCoord_eq (by omega) _ _
    rw [e]
    exact measurable_const.mul h
  have hSm : Measurable fun ω => ∑ i : Fin N, (Real.sqrt N)⁻¹ • (scrnFvec f (X 0 ω i) -
      ∫ y, scrnFvec f y ∂(volume : Measure (Torus d))) := by
    refine Finset.measurable_sum _ fun i _ => ?_
    have h1 : Measurable fun ω => scrnFvec f (X 0 ω i) :=
      (scrn_continuous_fvec hfc).measurable.comp ((measurable_pi_apply i).comp (hXm 0))
    exact (h1.sub_const (∫ y, scrnFvec f y ∂(volume : Measure (Torus d)))).const_smul (Real.sqrt N)⁻¹
  have hMm : AEMeasurable (vectorItoIntegral P ℱ W' (fun a => killAfter
      (scrnPhi D (Real.sqrt N) (ts a) (f a) X) (ts a)) T) P :=
    (hmart.sq_int T ⟨hT, le_rfl⟩).aestronglyMeasurable.aemeasurable
  have hRe : scrnRem D f ts X =ᵐ[P] fun ω => scrnZ ψ ts X ω - (∑ i : Fin N, (Real.sqrt N)⁻¹ •
      (scrnFvec f (X 0 ω i) - ∫ y, scrnFvec f y ∂(volume : Measure (Torus d)))) -
      vectorItoIntegral P ℱ W' (fun a => killAfter (scrnPhi D (Real.sqrt N) (ts a) (f a) X) (ts a)) T ω := by
    filter_upwards [hdec] with ω h
    rw [h]; abel
  exact ((hZm.aemeasurable.sub hSm.aemeasurable).sub hMm).congr hRe.symm

end HRS
