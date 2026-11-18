import HRS.MC.CepH4FinA
import HRS.MC.CepE2Props
import HRS.MC.CepH4Id
import HRS.MC.CepH4a
import HRS.MC.CepH4Core

/-!
# Packet CEPH4FIN: `cep_H4_single_component` (B.14 on one cyclic component), assembly

`HRS.MC.CepH4Fin.cep_H4_single_component_proof` has the statement of `HRS.MC.Cepa.cep_H4_single_component`.
Route: the filtered solution gives `∀ t, Measurable[ℱ t] X₀`; the initial chamber point `z₀ = ch4f_z0 σ₀ ∘ X₀`;
E1, E2 (with properties), E3, E6 give the Yosida flows `Z n` and the limit `Zl`; `cep_H4_identify_proof` gives
`X = mk ∘ unrank_{σ₀} ∘ Zl` a.s. on `[0,T]`, `cep_H4_core_proof` the entropy inequality for that flow, which is transported
to `X`; `cep_H4a_density_of_entropy_proof` gives the density.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepH4Fin

open HRS HRS.MC.Cepa HRS.MC.CepK1 HRS.MC.CepE7

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

/-- `E2` with envelope properties, at the types of the `Cepa` vocabulary (repackaging of `cep_Yosida`). -/
theorem ch4f_E2 (a : ℝ) (ha : 0 < a) (N : ℕ) [NeZero N] :
    ∃ (J : ℝ → Ch N → Ch N) (Φn : ℝ → Ch N → ℝ), cep_Yosida a N J ∧
      (∀ n z, 0 < n → HasGradientAt (Φn n) (n • (z - J n z)) z) ∧
      (∀ n z, 0 < n → z ∈ cep_Alcove N → Φn n z ≤ cep_chamberPot a N z) ∧
      (∀ z, z ∈ cep_Alcove N → Filter.Tendsto (fun n : ℕ => Φn n z) Filter.atTop (𝓝 (cep_chamberPot a N z))) ∧
      (∀ n z, 0 < n → Φn n (z + cep_diag N) = Φn n z) ∧
      (∀ n, 0 < n → ContDiff ℝ 1 (Φn n) ∧ LipschitzWith (Real.toNNReal n) (gradient (Φn n))) ∧
      (∃ C : ℝ, ∀ n z, 0 < n → n / 2 * Metric.infDist z (cep_Alcove N) ^ 2 - C ≤ Φn n z) := by
  obtain ⟨J, Φn, hY, h1, h2, h3, h4, h5, h6⟩ := HRS.MC.CepE2Props.cep_E2_envelope_props_proof a ha N
  exact ⟨J, Φn, ⟨hY.mem, hY.force, hY.lip, hY.yosida⟩, h1, h2, h3, h4, h5, h6⟩

theorem ch4f_gibbsEntropy_ne_bot (D : DynData 1) (μ : Measure (Config 1 N)) :
    gibbsEntropy D μ ≠ ⊥ := by
  unfold gibbsEntropy
  generalize relEntropy μ (gibbsRef D N) = x
  generalize Real.log (gibbsPartition D N).toReal = r
  rcases eq_or_ne x ⊤ with rfl | hx
  · simp
  · have : ((x : ℝ≥0∞) : EReal) = ((x.toReal : ℝ) : EReal) := by
      rw [← EReal.coe_ennreal_toReal hx]
    rw [this, ← EReal.coe_sub]
    exact EReal.coe_ne_bot _

/-- Finiteness of the entropy from the entropy inequality. -/
theorem ch4f_lt_top {A H : EReal} {B : ℝ≥0∞} (hA : A ≠ ⊥) (hH : H < ⊤)
    (h : A + (B : EReal) ≤ H) : A < ⊤ := by
  by_contra hcon
  have hAt : A = ⊤ := top_le_iff.1 (not_lt.1 hcon)
  rw [hAt, EReal.top_add_of_ne_bot (EReal.coe_ennreal_ne_bot B)] at h
  exact absurd (lt_of_le_of_lt h hH) (lt_irrefl _)

set_option maxHeartbeats 800000 in
theorem cep_H4_single_component_proof [IsProbabilityMeasure P] (hN : 2 ≤ N) [NeZero N]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ}
    {D : DynData 1} (hs : D.s = 0) (hβ : 0 < D.invβ)
    (hM : D.M = -(1 : Matrix (Fin 1) (Fin 1) ℝ)) (hV : Torus.IsCk 2 D.V)
    {T : ℝ} (hT : 0 < T)
    {X₀ : Ω → Config 1 N} (hX₀ : Measurable X₀) (hdist : ∀ᵐ ω ∂P, X₀ ω ∉ collisionSet 1 N)
    (σ₀ : Equiv.Perm (Fin N))
    (hcomp : ∀ᵐ ω ∂P, ∃ y : Fin N → Euc 1, (fun i => Torus.mk (y i)) = X₀ ω ∧ cep_StrictlyOrdered σ₀ y)
    {W : ℝ≥0 → Ω → (Fin N → Euc 1)} (hW : IsVectorBrownian P W)
    (hind : IndepFun X₀ (fun ω => fun t => W t ω) P)
    {X : ℝ≥0 → Ω → Config 1 N}
    (hX : IsCepaLepingleFlow P D T X₀ W X) (hF : IsFilteredSolution P ℱ W' W X)
    (hdens0 : HasSelectedDensity P X 0) (hH0 : gibbsEntropy D (selectedLaw P X 0) < ⊤) :
    cep_EntropyConcl P D T X := by
  classical
  have hW' : IsBrownianFiltration P ℱ W' := hF.brownian
  have hWW' := hF.coords
  have hV11 : cep_IsC11 D.V := ch4f_isC11 hV
  have hM1 : D.M = -((1 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ)) := by simpa using hM
  -- adaptedness of `X₀` at all times
  have hX0m : ∀ t : ℝ, Measurable[ℱ t] X₀ := by
    intro t
    have hX0 : ∀ s : ℝ, s ≤ 0 → Measurable[ℱ s] (X 0) := by
      intro s hs0
      have h := hF.progressive.adapted s
      have e : ofNNRealTime X s = X 0 := by
        funext ω
        simp [ofNNRealTime, Real.toNNReal_of_nonpos hs0]
      rw [e] at h
      exact h
    have hX0t : Measurable[ℱ t] (X 0) := by
      rcases le_or_gt t 0 with ht | ht
      · exact hX0 t ht
      · exact (hX0 0 le_rfl).mono (ℱ.mono ht.le) le_rfl
    exact hW'.complete.measurable_of_ae_eq t hX0t hX₀ hX.toContact.init
  -- the initial chamber point
  set π : Ω → Equiv.Perm (Fin N) := fun _ => σ₀ with hπdef
  have hπ : ∀ σ, MeasurableSet[ℱ 0] {ω | π ω = σ} := fun σ => by
    by_cases h : σ₀ = σ <;> simp [hπdef, h]
  set z₀ : Ω → Ch N := fun ω => ch4f_z0 σ₀ (X₀ ω) with hz₀def
  have hz₀m : Measurable[ℱ 0] z₀ := (ch4f_z0_meas σ₀).comp (hX0m 0)
  have hz₀A : ∀ ω, z₀ ω ∈ cep_Alcove N := fun ω => ch4f_z0_mem σ₀ (X₀ ω)
  have hz₀b : ∃ R : ℝ, ∀ ω, ‖z₀ ω‖ ≤ R := ⟨2 * Real.sqrt N, fun ω => ch4f_z0_norm σ₀ (X₀ ω)⟩
  have hz₀X : ∀ᵐ ω ∂P, (fun i => Torus.mk (cep_unrank σ₀ (z₀ ω) i)) = X₀ ω := by
    filter_upwards [hcomp] with ω h
    exact ch4f_z0_X σ₀ (X₀ ω) h
  -- E1, E2
  obtain ⟨Ψ, LΨ, hΨ1, hΨL, hΨper, hΨdr, hΨtot⟩ := cepE7_E1 hs zero_le_one hM1 hV11 N
  obtain ⟨J, Φn, hJ, hΦ, hΦle, hΦlim, hΦper, hΦC, hΦlow⟩ := ch4f_E2 1 one_pos N
  set σ' : ℝ := Real.sqrt (2 * D.invβ) with hσ'
  set F : Ch N → Ch N := fun z => -(gradient Ψ z) with hFdef
  have hF' : LipschitzWith LΨ F := cepE7_lip_neg hΨL
  have hB : ∀ n : ℕ, 1 ≤ n → LipschitzWith (Real.toNNReal n + LΨ)
      (fun z => -((n : ℝ) • (z - J n z)) + F z) := fun n hn =>
    (cepE7_lip_neg (hJ.lip (n : ℝ) (Nat.cast_pos.mpr (by omega)))).add hF'
  have hex : ∀ n : ℕ, 1 ≤ n → ∃ Zn : ℝ → Ω → Ch N, cep_IsChamberSolution P ℱ W' π σ'
      (fun z => -((n : ℝ) • (z - J n z)) + F z) z₀ Zn := fun n hn =>
    cepE7_E3 hW' hπ (hB n hn) σ' hz₀m
  choose Zs hZs using hex
  set Z : ℕ → ℝ → Ω → Ch N := fun n => if h : 1 ≤ n then Zs n h else Zs 1 le_rfl with hZdef
  have hZ : ∀ n : ℕ, 1 ≤ n → cep_IsChamberSolution P ℱ W' π σ'
      (fun z => -((n : ℝ) • (z - J n z)) + F z) z₀ (Z n) := by
    intro n hn
    simp only [hZdef, dif_pos hn]
    exact hZs n hn
  obtain ⟨Zl, hZlc, hZlm, hZlconv, hZlcl, hZlnull, hZlint, hZleq⟩ :=
    cepE7_E6 hW' hπ one_pos hJ hF' σ' hz₀m hz₀A hz₀b hZ
  -- identification
  have hid := HRS.MC.CepH4Id.cep_H4_identify_proof hW' hs hM hV11 hdist σ₀ hWW' hX hΨL hΨdr hz₀A hz₀X hZlc
    hZlm hZlcl hZlnull hZlint hZleq
  -- the chamber solutions for the potential `Φn n + Ψ`
  have hZ' : ∀ n : ℕ, 1 ≤ n → cep_IsChamberSolution P ℱ W' (fun _ => σ₀) (Real.sqrt (2 * D.invβ))
      (fun z => -(gradient (fun w => Φn n w + Ψ w) z)) z₀ (Z n) := by
    intro n hn
    have hg : (fun z => -(gradient (fun w => Φn n w + Ψ w) z)) =
        fun z => -((n : ℝ) • (z - J n z)) + F z := by
      funext z
      have h1 : HasGradientAt (fun w => Φn n w + Ψ w) ((n : ℝ) • (z - J n z) + gradient Ψ z) z :=
        hasGradientAt_iff_hasFDerivAt.2 (by
          rw [map_add]
          exact (hΦ n z (Nat.cast_pos.mpr (by omega))).add
            ((hΨ1.differentiable one_ne_zero z).hasGradientAt))
      rw [h1.gradient, hFdef]
      simp only [neg_add]
    rw [hg]
    exact hZ n hn
  -- selected laws agree up to `T`
  set Xs : ℝ≥0 → Ω → Config 1 N := fun s ω => fun i => Torus.mk (cep_unrank σ₀ (Zl (s : ℝ) ω) i) with hXs
  have hlaw : ∀ t : ℝ, 0 ≤ t → t ≤ T → selectedLaw P X t = selectedLaw P Xs t := by
    intro t ht0 htT
    unfold selectedLaw HRS.law
    refine Measure.map_congr ?_
    filter_upwards [hid] with ω h
    exact h _ (by rw [Real.coe_toNNReal t ht0]; exact htT)
  have hH0' : gibbsEntropy D (selectedLaw P Xs 0) < ⊤ := by
    rw [← hlaw 0 le_rfl hT.le]; exact hH0
  have hcore := HRS.MC.CepH4Core.cep_H4_core_proof hW' hs hβ hM hV11 σ₀ hJ hΦ hΦle hΦlim hΦper hΦC hΦlow hΨ1 hΨL hΨper
    (hΨtot rfl) hz₀m hz₀A hZ' hZlconv hZlc hZlcl hZlnull hH0'
  intro t ht
  have hfish : ∫⁻ r in Set.Icc (0 : ℝ) t, fisherInfo D N (selectedLaw P X r) =
      ∫⁻ r in Set.Icc (0 : ℝ) t, fisherInfo D N (selectedLaw P Xs r) := by
    refine setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    rw [hlaw r hr.1 (hr.2.trans ht.2)]
  have hineq : gibbsEntropy D (selectedLaw P X t)
      + ((ENNReal.ofReal D.invβ * ∫⁻ r in Set.Icc (0 : ℝ) t, fisherInfo D N (selectedLaw P X r) : ℝ≥0∞) : EReal)
      ≤ gibbsEntropy D (selectedLaw P X 0) := by
    rw [hfish, hlaw t ht.1 ht.2, hlaw 0 le_rfl hT.le]
    exact hcore t ht.1
  refine ⟨?_, hineq⟩
  have : IsProbabilityMeasure (selectedLaw P X t) :=
    by unfold selectedLaw HRS.law; infer_instance
  exact HRS.MC.CepH4a.cep_H4a_density_of_entropy_proof hβ _
    (ch4f_lt_top (ch4f_gibbsEntropy_ne_bot D _) hH0 hineq)

end HRS.MC.CepH4Fin
