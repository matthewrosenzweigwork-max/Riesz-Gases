import HRS.MC.CepE7
import HRS.MC.CepU2

/-!
# Packet CEPH4ID: the flow of B.14 on one cyclic component is `mk ∘ unrank_{σ₀} ∘ Zl`

Proof of `HRS.MC.CepH4Id.cep_H4_identify` (statement in `HRS/MC/CepH4IdSpec.lean`, copied verbatim).  The first bullet of
`HRS.MC.CepE7.cep_E7_existence_repaired_proof` is redone for the given `Zl` and the constant labelling `σ₀`: the process
`projectPath Y`, `Y t ω = cep_unrank σ₀ (Zl t ω)`, is an `IsCepaLepingleFlow P D T X₀ W ·`; then U2 identifies it with `X`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH4Id

open HRS HRS.MC.Cepa HRS.MC.CepK1 HRS.MC.CepE7

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

theorem cep_H4_identify_proof [IsProbabilityMeasure P] [NeZero N] {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hW' : IsBrownianFiltration P ℱ W')
    {D : DynData 1} (hs : D.s = 0) (hM : D.M = -(1 : Matrix (Fin 1) (Fin 1) ℝ)) (hV : cep_IsC11 D.V)
    {T : ℝ} {X₀ : Ω → Config 1 N} (hdist : ∀ᵐ ω ∂P, X₀ ω ∉ collisionSet 1 N)
    (σ₀ : Equiv.Perm (Fin N))
    {W : ℝ≥0 → Ω → (Fin N → Euc 1)}
    (hWW' : ∀ᵐ ω ∂P, ∀ t i j, W' t ω (i, j) = W t ω i j)
    {X : ℝ≥0 → Ω → Config 1 N} (hX : IsCepaLepingleFlow P D T X₀ W X)
    {Ψ : Ch N → ℝ} {L : ℝ≥0} (hΨL : LipschitzWith L (gradient Ψ))
    (hΨdr : ∀ (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1), cep_StrictlyOrdered π y → ∀ k : Fin N,
      liftedDrift D y (π k) 0 =
        -(gradient (cep_chamberPot 1 N) (cep_toCh π y)) k - (gradient Ψ (cep_toCh π y)) k)
    {z₀ : Ω → Ch N} (hz₀A : ∀ ω, z₀ ω ∈ cep_Alcove N)
    (hz₀X : ∀ᵐ ω ∂P, (fun i => Torus.mk (cep_unrank σ₀ (z₀ ω) i)) = X₀ ω)
    {Zl : ℝ → Ω → Ch N} (hZlc : ∀ ω, Continuous fun t => Zl t ω)
    (hZlm : ∀ t, 0 ≤ t → Measurable[ℱ t] (Zl t))
    (hZlcl : ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → Zl t ω ∈ closure (cep_Alcove N))
    (hZlnull : ∀ᵐ ω ∂P, ∀ T : ℝ, volume {s : ℝ | s ∈ Set.Icc 0 T ∧ Zl s ω ∉ cep_Alcove N} = 0)
    (hZlint : ∀ᵐ ω ∂P, ∀ T : ℝ,
      IntegrableOn (fun s : ℝ => ‖gradient (cep_chamberPot 1 N) (Zl s ω)‖) (Set.Icc 0 T))
    (hZleq : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → Zl t ω = z₀ ω +
      (∫ s in (0 : ℝ)..t, (-(gradient (cep_chamberPot 1 N) (Zl s ω)) + -(gradient Ψ (Zl s ω)))) +
        Real.sqrt (2 * D.invβ) • cep_noise (fun _ : Ω => σ₀) W' t ω) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T → X t ω = fun i => Torus.mk (cep_unrank σ₀ (Zl (t : ℝ) ω) i) := by
  classical
  have hE1 : cepE7_E1drift D 1 N Ψ := hΨdr
  have hΨc : Continuous (gradient Ψ) := hΨL.continuous
  set σ' : ℝ := Real.sqrt (2 * D.invβ) with hσ'
  set π : Ω → Equiv.Perm (Fin N) := fun _ => σ₀ with hπdef
  have hπm : ∀ σ, MeasurableSet {ω | π ω = σ} := fun σ => by
    by_cases h : σ₀ = σ <;> simp [hπdef, h]
  set Y : ℝ≥0 → Ω → Fin N → Euc 1 := fun t ω => cep_unrank (π ω) (Zl (t : ℝ) ω) with hYdef
  have hAE : ∀ᵐ ω ∂P, (∀ t : ℝ, 0 ≤ t → Zl t ω ∈ closure (cep_Alcove N)) ∧
      (∀ T : ℝ, volume {s : ℝ | s ∈ Icc 0 T ∧ Zl s ω ∉ cep_Alcove N} = 0) ∧
      (∀ T : ℝ, IntegrableOn (fun s : ℝ => ‖gradient (cep_chamberPot 1 N) (Zl s ω)‖) (Icc 0 T)) ∧
      (∀ t : ℝ, 0 ≤ t → Zl t ω = z₀ ω +
        (∫ s in (0 : ℝ)..t, (-(gradient (cep_chamberPot 1 N) (Zl s ω)) + -(gradient Ψ (Zl s ω)))) +
          σ' • cep_noise π W' t ω) ∧
      (∀ t i j, W' t ω (i, j) = W t ω i j) ∧
      (fun i => Torus.mk (cep_unrank σ₀ (z₀ ω) i)) = X₀ ω := by
    filter_upwards [hZlcl, hZlnull, hZlint, hZleq, hWW', hz₀X] with ω h1 h2 h3 h4 h5 h6
    exact ⟨h1, h2, h3, h4, h5, h6⟩
  have hproj : ∀ ω, ∀ s : ℝ, 0 ≤ s → projectPath Y (Real.toNNReal s) ω =
      fun j => Torus.mk (cep_unrank (π ω) (Zl s ω) j) := by
    intro ω s hs0
    funext j
    simp only [projectPath, hYdef, Real.coe_toNNReal s hs0]
  have hinit : ∀ᵐ ω ∂P, projectPath Y 0 ω = X₀ ω := by
    filter_upwards [hAE] with ω ⟨hcl, hnull, hint, heq, hWW, hz⟩
    have h0 := heq 0 le_rfl
    have hnz : cep_noise π W' 0 ω = 0 := by
      ext k
      simp [cep_noise, hW'.zero ω]
    simp only [intervalIntegral.integral_same, add_zero, hnz, smul_zero] at h0
    rw [← hz]
    funext i
    show Torus.mk (cep_unrank (π ω) (Zl ((0 : ℝ≥0) : ℝ) ω) i) = _
    rw [NNReal.coe_zero, h0]
  have hlift : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ T →
      (∀ i, IntegrableOn (fun s : ℝ => particleDrift D (projectPath Y (Real.toNNReal s) ω) i)
        (Icc 0 (t : ℝ))) ∧
      ∀ i, Y t ω i = Y 0 ω i +
        (∫ s in Icc (0 : ℝ) t, particleDrift D (projectPath Y (Real.toNNReal s) ω) i) +
          Real.sqrt (2 * D.invβ) • (W t ω i - W 0 ω i) := by
    filter_upwards [hAE] with ω ⟨hcl, hnull, hint, heq, hWW, hz⟩ t _
    have hEqOn : ∀ i, EqOn (fun s : ℝ => particleDrift D (projectPath Y (Real.toNNReal s) ω) i)
        (fun s : ℝ => particleDrift D (fun j => Torus.mk (cep_unrank (π ω) (Zl s ω) j)) i)
        (Icc 0 (t : ℝ)) := by
      intro i s hs0
      simp only [hproj ω s hs0.1]
    have hP := fun i => cepE7_lift_path hE1 hΨc (hZlc ω) (π ω) (z₀ ω)
      (fun t => cep_noise π W' t ω) σ' heq hint hnull (t.2 : (0 : ℝ) ≤ t) i
    refine ⟨fun i => ((hP i).1).congr_fun (fun s hs0 => (hEqOn i hs0).symm) measurableSet_Icc, fun i => ?_⟩
    rw [setIntegral_congr_fun measurableSet_Icc (hEqOn i)]
    have hn : ∀ s : ℝ≥0, cep_noise π W' (s : ℝ) ω ((π ω).symm i) = W s ω i 0 := by
      intro s
      simp only [cep_noise, Real.toNNReal_coe, Equiv.apply_symm_apply]
      exact hWW s i 0
    have hn0 : cep_noise π W' 0 ω ((π ω).symm i) = W 0 ω i 0 := by
      simpa using hn 0
    have hE := (hP i).2
    have hnt := hn t
    erw [hnt] at hE
    rw [hn0] at hE
    show cep_unrank (π ω) (Zl (t : ℝ) ω) i = cep_unrank (π ω) (Zl ((0 : ℝ≥0) : ℝ) ω) i + _ + _
    rw [NNReal.coe_zero]
    refine hE.trans ?_
    congr 1
    ext c
    have hc : c = 0 := Subsingleton.elim _ _
    subst hc
    simp [cepk1_ι]
    left
    rw [hσ']
    exact Real.sqrt_mul (by norm_num) _
  have hord : ∀ᵐ ω ∂P, ∃ Y' : ℝ≥0 → Fin N → Euc 1,
      (∀ t : ℝ≥0, (t : ℝ) ≤ T → projectPath Y t ω = fun i => Torus.mk (Y' t i)) ∧ Continuous Y' ∧
      ∀ t : ℝ≥0, (t : ℝ) ≤ T → CyclicallyOrdered (π ω) (Y' t) := by
    filter_upwards [hAE] with ω ⟨hcl, hnull, hint, heq, hWW, hz⟩
    refine ⟨fun t => cep_unrank (π ω) (Zl (t : ℝ) ω), fun t _ => rfl, ?_, fun t _ => ?_⟩
    · exact continuous_pi fun i => cepk1_contDiff_ι.continuous.comp
        ((EuclideanSpace.proj ((π ω).symm i)).continuous.comp ((hZlc ω).comp NNReal.continuous_coe))
    · exact cepE7_unrank_cyc (hcl t t.2) (π ω)
  have hocc : ∀ᵐ ω ∂P, volume {s : ℝ | s ∈ Icc 0 T ∧
      projectPath Y (Real.toNNReal s) ω ∈ collisionSet 1 N} = 0 := by
    filter_upwards [hAE] with ω ⟨hcl, hnull, hint, heq, hWW, hz⟩
    refine measure_mono_null (fun s hs => ?_) (hnull T)
    refine ⟨hs.1, fun hz => ?_⟩
    have := hs.2
    rw [hproj ω s hs.1.1] at this
    exact cepE7_not_collision hz (π ω) this
  have hflow : IsCepaLepingleFlow P D T X₀ W (projectPath Y) := by
    refine ⟨⟨⟨Y, ?_, rfl⟩, hinit, ?_, ?_⟩, ⟨π, hπm, hord⟩, hocc⟩
    · filter_upwards [hlift] with ω h t ht
      exact h t ht
    · exact Filter.Eventually.of_forall fun ω i =>
        (continuous_apply i).comp (cepE7_X_continuous (π ω) (hZlc ω))
    · intro t
      exact cepE7_X_measurable (m := mΩ) hπm ((hZlm t t.2).mono (ℱ.le _) le_rfl)
  have hU := HRS.MC.CepU2.cep_U2_flow_unique_proof (a := 1) hs one_pos
    (by rw [hM, one_smul]) hV hdist hX hflow
  filter_upwards [hU] with ω h t ht
  exact h t ht

end HRS.MC.CepH4Id
