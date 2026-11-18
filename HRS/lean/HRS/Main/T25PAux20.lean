import HRS.Main.T25PAux19

/-!
# T25P, part 20: the comparison on a window, for the particle fluctuation process
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.T25P

open HRS HRS.Uniform HRS.GF HRS.AdjK

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

set_option maxHeartbeats 1600000 in
theorem t25p_core_gen (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {m : ℝ}
    (hm : (d : ℝ) + 2 < m) {T : ℝ} (hT : 0 < T) {Cr cr : ℝ} (hCr : 0 < Cr) (hcr : 0 < cr) {Cmax : ℝ}
    {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m} (hdual : IsDualEvolution htr.dyn ρ m Vev)
    (hEv : T25Ev m Cr cr T Cmax Vev) {N : ℕ} (hN : 2 ≤ N) {a : ℝ} (ha : 0 ≤ a)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hX : IsParticleSystem P htr.dyn (a + T) X₀ W X) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsFilteredSolution P ℱ W' W X)
    (η' : Ω → NegSobolev d m) (hη' : Measurable[ℱ 0] η')
    (Λ : Measure (PathSp T (NegSobolev d m)))
    (hid : ∀ (Ω₂ : Type) [mΩ₂ : MeasurableSpace Ω₂] (P₂ : Measure Ω₂) [IsProbabilityMeasure P₂]
      (ℱ₂ : Filtration ℝ mΩ₂) (ξ : Ω₂ → NegSobolev d m) (G : ℝ → Ω₂ → NegSobolev d m),
      Measurable ξ →
      IsHilbertMartingaleWithCovariation P₂ ℱ₂ (a + T) G (fun r _ => covDensT m β⁻¹ (a + T) ρ r) →
      Indep (MeasurableSpace.comap ξ inferInstance)
        (⨆ τ ∈ Set.Icc (0 : ℝ) (a + T), MeasurableSpace.comap (G τ) inferInstance) P₂ →
      P₂.map ξ = P.map η' →
      ∀ Zb : ℝ → Ω₂ → NegSobolev d m,
        (∀ t ∈ Set.Icc (0 : ℝ) (a + T),
          IsStochConv P₂ Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) G 0 t (Zb t)) →
        (∀ᵐ ω ∂P₂, ContinuousOn (fun t => Zb t ω) (Set.Icc 0 (a + T))) →
        (∀ t, Measurable (Zb t)) →
        Λ = law P₂ (windowPath a T (fun t ω => Vev t 0 (ξ ω) + Zb t ω))) :
    (ENNReal.ofReal (smoothDist 2 (law P (windowPath a T (flucProc m (Real.sqrt N) X ρ))) Λ) ≤
      ENNReal.ofReal (Cr * Real.exp (-cr * a)) *
        ∫⁻ ω, ‖flucProc m (Real.sqrt N) X ρ 0 ω - η' ω‖ₑ ∂P +
        ∫⁻ ω, ENNReal.ofReal Cr * t25p_Psi d s ρ m cr a T X ω ∂P +
        ENNReal.ofReal (Cr ^ 2 / 2) * ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T),
          ENNReal.ofReal (Real.exp (-cr * max (a - r) 0) ^ 2 * traceNormForm
            (covForm m β⁻¹ (empirical (X r.toNNReal ω)) - covDensT m β⁻¹ (a + T) ρ r))) ∂P) ∧
    (∀ p : ℝ, (p = 1 ∨ p = 2) →
      wassersteinE p (law P (windowPath a T (flucProc m (Real.sqrt N) X ρ))) Λ ≤
        ENNReal.ofReal ((2 * (Cr ^ 2 + Real.sqrt Cmax) + Cr + 1) * Real.exp (-cr * a)) *
            (∫⁻ ω, ‖flucProc m (Real.sqrt N) X ρ 0 ω - η' ω‖ₑ ^ p ∂P) ^ (1 / p) +
          (∫⁻ ω, (ENNReal.ofReal Cr * t25p_Psi d s ρ m cr a T X ω) ^ p ∂P) ^ (1 / p) +
          ENNReal.ofReal (2 * (Cr ^ 2 + Real.sqrt Cmax) + Cr + 1) *
            (∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T),
              ENNReal.ofReal (Real.exp (-cr * max (a - r) 0) ^ 2 * traceNormForm
                (covForm m β⁻¹ (empirical (X r.toNNReal ω)) - covDensT m β⁻¹ (a + T) ρ r))) ∂P) ^
              (1 / 2 : ℝ)) := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hT' : 0 < a + T := by linarith
  have hm1 : (d : ℝ) / 2 + 2 < m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hm0 : (d : ℝ) / 2 < m := by linarith
  obtain ⟨Mart, Z, hM, hZS, hZc, hZm, hRc, hRm, hRb⟩ :=
    t25p_stage1 hd htr hm hT hCr hcr hdual hEv hN ha P X₀ W X hX ℱ W' hF
  obtain ⟨C2, -, hst⟩ := t25p_stage2 hCr.le hcr.le hT Vev hEv (d := d) (m := m) (Cmax := Cmax)
  have hCb := t25p_detCov hd htr hm1 hT'
  have hCb0 : ∀ r : ℝ, a + T < r → covDensT m β⁻¹ (a + T) ρ r = 0 := fun r hr => t25p_covDensT_zero hr ρ
  have hXm : ∀ t : ℝ≥0, Measurable[ℱ 0] (X t) → True := fun _ _ => trivial
  have hX0ℱ : Measurable[ℱ 0] (X (Real.toNNReal 0)) := by
    rw [Real.toNNReal_zero]
    have h := hF.adapted 0
    rwa [NNReal.coe_zero] at h
  have hflm0 : Measurable[ℱ 0] (fun ω => flucProc m (Real.sqrt N) X ρ 0 ω) :=
    ((gf_measurable_ofMeasureDiff_proof m hm0 (withDensityReal (ρ 0))).const_smul (Real.sqrt N)).comp hX0ℱ
  have hBm : AEMeasurable (fun ω => ENNReal.ofReal Cr * t25p_Psi d s ρ m cr a T X ω) P :=
    (t25p_Psi_aemeas hd htr m cr a T hT' P X hF.progressive).const_mul _
  exact hst a ha Ω P ℱ (fun ω => flucProc m (Real.sqrt N) X ρ 0 ω) η' hflm0 hη' Mart
    (fun r ω => covForm m β⁻¹ (empirical (X r.toNNReal ω))) hM (covDensT m β⁻¹ (a + T) ρ) hCb hCb0 Z
    (fun t ω => flucProc m (Real.sqrt N) X ρ t ω - Vev t 0 (flucProc m (Real.sqrt N) X ρ 0 ω) - Z t ω)
    (flucProc m (Real.sqrt N) X ρ) hZS hZc hZm hRc hRm
    (fun t _ ω => by abel) (fun ω => ENNReal.ofReal Cr * t25p_Psi d s ρ m cr a T X ω) hBm hRb Λ hid

end HRS.T25P
