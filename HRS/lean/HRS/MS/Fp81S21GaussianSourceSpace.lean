import HRS.MS.S21F_D01
import HRS.MS.S21L_G11A
import HRS.MC.QRPWick

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MC.E213U13 HRS.MC.QRSpec.Wick

/-- Oscillator tests at the regularity used by the retained Gaussian source. -/
abbrev fp81s21_oscTest (d : ℕ) :=
  {φ : Euc d → ℝ // IsOscTest (wholeSpaceIndex d : ℝ) φ}

/-- The scalar first-chaos space on the source probability space.  Its elements are
exactly the functions whose `L²` classes lie in the closed span of the retained
standard Gaussian coordinates.  The definition is stable under changes on null
sets. -/
noncomputable def fp81s21_scalarFirstChaosSpace
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → ℝ) (hξ : IsStdGaussianSeq P ξ)
    (hξmeas : ∀ i, Measurable (ξ i)) : Submodule ℝ (Ω → ℝ) where
  carrier := {W | InQ1 hξ hξmeas W}
  zero_mem' := by
    let hzero : MemLp (fun _ : Ω => (0 : ℝ)) 2 P := MemLp.zero
    refine ⟨hzero, ?_⟩
    rw [MemLp.toLp_zero hzero]
    exact Submodule.zero_mem _
  add_mem' := by
    rintro W V ⟨hW, hWc⟩ ⟨hV, hVc⟩
    refine ⟨hW.add hV, ?_⟩
    have hto : (hW.add hV).toLp (W + V) = hW.toLp W + hV.toLp V :=
      MemLp.toLp_add hW hV
    rw [hto]
    exact add_mem hWc hVc
  smul_mem' := by
    rintro c W ⟨hW, hWc⟩
    let hW' : MemLp (c • W) 2 P := hW.const_smul c
    refine ⟨hW', ?_⟩
    have hto : hW'.toLp (c • W) = c • hW.toLp W :=
      MemLp.toLp_const_smul c hW
    rw [hto]
    exact Submodule.smul_mem _ _ hWc

/-- Every member of the scalar first-chaos space has the centered Gaussian fourth
moment.  This uses the Gaussian law of the closed `L²` span, not a Banach-valued
Gaussian representation. -/
theorem fp81s21_scalarFirstChaos_QrpwG4
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → ℝ) (hξ : IsStdGaussianSeq P ξ)
    (hξmeas : ∀ i, Measurable (ξ i)) :
    QrpwG4 P (fp81s21_scalarFirstChaosSpace (P := P) ξ hξ hξmeas) := by
  intro W hW
  obtain ⟨v, hv⟩ := InQ1.exists_gaussian hξ hξmeas hW
  have hWmeas : AEMeasurable W P := hW.1.aestronglyMeasurable.aemeasurable
  have hWlaw : HasGaussianLaw W P := by
    haveI : IsGaussian (P.map W) := by rw [hv]; infer_instance
    exact IsGaussian.hasGaussianLaw hWmeas
  have hmean : ∫ ω, W ω ∂P = 0 := by
    have hmap : ∫ ω, W ω ∂P = ∫ x, x ∂(P.map W) := by
      exact (integral_map hWmeas aestronglyMeasurable_id).symm
    rw [hmap, hv, integral_id_gaussianReal]
  exact qrpw_gauss4 hWlaw hmean

/-- The retained coordinate functions themselves belong to the scalar first-chaos
space. -/
theorem fp81s21_scalarFirstChaos_coordinate
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → ℝ) (hξ : IsStdGaussianSeq P ξ)
    (hξmeas : ∀ i, Measurable (ξ i)) (i : ℕ) :
    (fun ω => ξ i ω) ∈ fp81s21_scalarFirstChaosSpace (P := P) ξ hξ hξmeas := by
  change InQ1 hξ hξmeas (fun ω => ξ i ω)
  refine ⟨memLp_xi hξ hξmeas i, ?_⟩
  change g1 hξ hξmeas i ∈ Qc (K1 hξ hξmeas)
  have hgen : g1 hξ hξmeas i ∈ K1 hξ hξmeas (i + 1) := by
    exact Submodule.subset_span ⟨⟨i, by omega⟩, rfl⟩
  exact Submodule.le_topologicalClosure _ ((le_iSup (K1 hξ hξmeas) (i + 1)) hgen)

/-- Conditional common-source Gaussian space on the retained realization.  The
explicit source hypotheses are the standard Gaussian coordinate law and its
measurability, the first-chaos certificate for every oscillator evaluation, and
the a.e. identification of those evaluations with `L` on a dense oscillator-test
subspace.  The operator `L u` is continuous into the source `L²` space.  Thus the
conclusion covers all `L u f`, as well as every nonnegative-time endpoint or past
oscillator observation of `G0.Z`. -/
theorem fp81s21_gaussianSourceSpace_conditional
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ) (G0 : GaussianRealization R)
    (ξ : ℕ → G0.Ω → ℝ)
    (hξ : IsStdGaussianSeq G0.P ξ)
    (hξmeas : ∀ i, Measurable (ξ i))
    (μ : Measure (Euc p.d))
    (φLp : fp81s21_oscTest p.d → Lp ℝ 2 μ)
    (hφdense : Dense (Set.range φLp))
    (L : ℝ → Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 G0.P)
    (hEvalFirst : ∀ u : ℝ, 0 ≤ u → ∀ φ : fp81s21_oscTest p.d,
      InFirstChaos G0.P ξ 2 (fun ω => OscDual.eval (G0.Z u ω) φ.1))
    (hEvalL : ∀ u : ℝ, 0 ≤ u → ∀ φ : fp81s21_oscTest p.d,
      (L u (φLp φ) : G0.Ω → ℝ) =ᵐ[G0.P]
        (fun ω => OscDual.eval (G0.Z u ω) φ.1)) :
    ∃ 𝒢 : Submodule ℝ (G0.Ω → ℝ),
      QrpwG4 G0.P 𝒢 ∧
      (∀ i, (fun ω => ξ i ω) ∈ 𝒢) ∧
      (∀ u : ℝ, 0 ≤ u → ∀ f : Lp ℝ 2 μ,
        (L u f : G0.Ω → ℝ) ∈ 𝒢) ∧
      (∀ u : ℝ, 0 ≤ u → ∀ φ : fp81s21_oscTest p.d,
        (fun ω => OscDual.eval (G0.Z u ω) φ.1) ∈ 𝒢) := by
  let 𝒢 : Submodule ℝ (G0.Ω → ℝ) :=
    fp81s21_scalarFirstChaosSpace (P := G0.P) ξ hξ hξmeas
  have hG4 : QrpwG4 G0.P 𝒢 :=
    fp81s21_scalarFirstChaos_QrpwG4 ξ hξ hξmeas
  have hcoords : ∀ i, (fun ω => ξ i ω) ∈ 𝒢 := by
    intro i
    exact fp81s21_scalarFirstChaos_coordinate ξ hξ hξmeas i
  have hEvalMem : ∀ u : ℝ, 0 ≤ u → ∀ φ : fp81s21_oscTest p.d,
      (fun ω => OscDual.eval (G0.Z u ω) φ.1) ∈ 𝒢 := by
    intro u hu φ
    change InQ1 hξ hξmeas (fun ω => OscDual.eval (G0.Z u ω) φ.1)
    exact s21l_inQ1_of_first hξ hξmeas (hEvalFirst u hu φ)
  have hLmem : ∀ u : ℝ, 0 ≤ u → ∀ f : Lp ℝ 2 μ,
      (L u f : G0.Ω → ℝ) ∈ 𝒢 := by
    intro u hu f
    have hclosed : IsClosed (Qc (K1 hξ hξmeas) : Set (Lp ℝ 2 G0.P)) :=
      Submodule.isClosed_topologicalClosure _
    have hpre : IsClosed {x : Lp ℝ 2 μ | L u x ∈ Qc (K1 hξ hξmeas)} :=
      hclosed.preimage (L u).continuous
    have htests : Set.range φLp ⊆
        {x : Lp ℝ 2 μ | L u x ∈ Qc (K1 hξ hξmeas)} := by
      rintro x ⟨φ, rfl⟩
      have hfirst := hEvalFirst u hu φ
      have hq1 : InQ1 hξ hξmeas (fun ω => OscDual.eval (G0.Z u ω) φ.1) :=
        s21l_inQ1_of_first hξ hξmeas hfirst
      have hq1L : InQ1 hξ hξmeas (fun ω => (L u (φLp φ)) ω) :=
        InQ1_congr (hEvalL u hu φ).symm hq1
      rcases hq1L with ⟨hmem, hmemQ⟩
      have hto : hmem.toLp (fun ω => (L u (φLp φ)) ω) = L u (φLp φ) :=
        Lp.toLp_coeFn (L u (φLp φ)) hmem
      change L u (φLp φ) ∈ Qc (K1 hξ hξmeas)
      rw [← hto]
      exact hmemQ
    have hLQ : L u f ∈ Qc (K1 hξ hξmeas) :=
      closure_minimal htests hpre (hφdense f)
    have hmem : MemLp (fun ω => (L u f) ω) 2 G0.P := Lp.memLp _
    have hto : hmem.toLp (fun ω => (L u f) ω) = L u f :=
      Lp.toLp_coeFn (L u f) hmem
    change InQ1 hξ hξmeas (fun ω => (L u f) ω)
    have hmemQ : hmem.toLp (fun ω => (L u f) ω) ∈ Qc (K1 hξ hξmeas) := by
      rw [hto]
      exact hLQ
    exact ⟨hmem, hmemQ⟩
  exact ⟨𝒢, hG4, hcoords, hLmem, hEvalMem⟩

#print axioms fp81s21_scalarFirstChaos_QrpwG4
#print axioms fp81s21_scalarFirstChaos_coordinate
#print axioms fp81s21_gaussianSourceSpace_conditional

end HRS.Fp81.S21
end
