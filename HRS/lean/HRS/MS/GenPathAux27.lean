import HRS.MS.GenPathAux26
import HRS.MH.DualityRdFinal

/-!
# S5.6 packet P6b: the duality identity for a whole-space strong solution without pathwise uniqueness
(copy of `duality_identity_rd_proof`, whose proof only uses `flow_contact`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS.Whole HRS.Whole.AppendixA HRS.MH.DualityRd

variable {d : ℕ}

theorem s56_duality_core {N : ℕ} (s Λ T ΛV G₀ : ℝ) (D : WholeDyn d) (hs : D.s = s) (hs0 : 0 ≤ s) (hsd : s < d)
    (hinv : 0 ≤ D.invβ) (hV : VHypRd 2 ΛV G₀ D.V) (ρ : ℝ → Euc d → ℝ) (hρ : IsWholeMeanFieldSolution D T ρ)
    (hreg : IsRegularMFRd s 3 Λ T ρ)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hX : IsWholeStrongSolution P D T X₀ W X) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsWholeFilteredSolution P ℱ W' W X)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ)
    (hf : IsClassicalAdjointW (D.coeff ρ) t φ f) :
    DualityIdentityRd P ℱ W' D ρ X t f := by
  have hXc : IsWholeContactStrongSolution P D T X₀ W X := ⟨hX.init, hX.eqn, hX.cont, hX.adapted⟩
  have hocc : D.M = 0 ∨ ∀ᵐ ζ ∂P,
      volume {s : ℝ | s ∈ Set.Icc (0 : ℝ) T ∧ X (Real.toNNReal s) ζ ∈ eucCollisionSet d N} = 0 := by
    refine Or.inr ?_
    filter_upwards [hX.no_collision] with ζ hζ
    have : {s : ℝ | s ∈ Set.Icc (0 : ℝ) T ∧ X (Real.toNNReal s) ζ ∈ eucCollisionSet d N} = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun s hs => ?_
      refine hζ (Real.toNNReal s) ?_ hs.2
      rw [Real.coe_toNNReal _ hs.1.1]
      exact hs.1.2
    rw [this, measure_empty]
  have hM : MFData s Λ T ΛV G₀ D ρ := ⟨hs, hs0, hsd, hinv, hV, hρ, hreg⟩
  have hC := hf.isC12TestRd
  have hd : 1 ≤ d := hM.one_le_d
  have hs0' : 0 ≤ D.s := hs ▸ hs0
  have hsd' : D.s < d := hs ▸ hsd
  have hM : MFData s Λ T ΛV G₀ D ρ := ⟨hs, hs0, hsd, hinv, hV, hρ, hreg⟩
  have hC := hf.isC12TestRd
  have hd : 1 ≤ d := hM.one_le_d
  have hs0' : 0 ≤ D.s := hs ▸ hs0
  have hsd' : D.s < d := hs ▸ hsd
  unfold DualityIdentityRd
  rcases ht.1.eq_or_lt with h0 | hpos
  · subst h0
    refine Filter.Eventually.of_forall fun ζ τ hτ => ?_
    have hτ0 : τ = 0 := le_antisymm hτ.2 hτ.1
    subst hτ0
    have hI : itoIntegral P ℱ W' (fun r ζ' (ia : Fin N × Fin d) =>
        if r ∈ Set.Icc (0 : ℝ) 0 then gradComp ia.2 (f r) (X (Real.toNNReal r) ζ' ia.1) else 0) 0 ζ = 0 :=
      itoIntegral_of_nonpos P ℱ W' _ le_rfl ζ
    refine ⟨?_, ?_⟩
    · have hv : volume (Set.Icc (0 : ℝ) 0) = 0 := by simp
      unfold IntegrableOn
      rw [Measure.restrict_eq_zero.2 hv]
      exact integrable_zero_measure
    · rw [hI]
      simp
  · have hito := empirical_ito_rd_proof D hinv (measurable_gradient_of_vhyp hV) hXc hF hocc hpos ht.2 hC
    have hmf := mf_time_dependent_proof hM ht hC
    filter_upwards [hito] with ζ hζ
    intro τ hτ
    obtain ⟨hI1, hE1⟩ := hζ τ hτ
    obtain ⟨hI2, hE2⟩ := hmf τ hτ
    have hpt : ∀ r ∈ Set.Icc (0 : ℝ) τ,
        (Whole.pair (Whole.empirical (X (Real.toNNReal r) ζ))
            (driftTestRd D f (fun r x => -(generatorW (D.coeff ρ) r (f r) x)) r)
          + interactionPairingW D (f r) (Whole.empirical (X (Real.toNNReal r) ζ))
              (Whole.empirical (X (Real.toNNReal r) ζ)))
        - (Whole.pair (Whole.withDensityReal (ρ r))
            (driftTestRd D f (fun r x => -(generatorW (D.coeff ρ) r (f r) x)) r)
          + interactionPairingW D (f r) (Whole.withDensityReal (ρ r)) (Whole.withDensityReal (ρ r)))
        = flucInteractionRd D (f r) (X (Real.toNNReal r) ζ) (ρ r) := by
      intro r hr
      have hrt : r ∈ Set.Icc (0 : ℝ) t := ⟨hr.1, hr.2.trans hτ.2⟩
      have hrT : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1, hrt.2.trans ht.2⟩
      exact fluc_pointwise_rd_proof D hd hs0' hsd' ρ (hM.regSlice hrT) (hC.memCb hrt) (X (Real.toNNReal r) ζ)
    have hint : IntegrableOn (fun r => flucInteractionRd D (f r) (X (Real.toNNReal r) ζ) (ρ r))
        (Set.Icc 0 τ) :=
      (hI1.sub hI2).congr_fun (fun r hr => hpt r hr) measurableSet_Icc
    refine ⟨hint, ?_⟩
    have hsub : ∫ r in Set.Icc (0 : ℝ) τ, flucInteractionRd D (f r) (X (Real.toNNReal r) ζ) (ρ r)
        = (∫ r in Set.Icc (0 : ℝ) τ, (Whole.pair (Whole.empirical (X (Real.toNNReal r) ζ))
            (driftTestRd D f (fun r x => -(generatorW (D.coeff ρ) r (f r) x)) r)
          + interactionPairingW D (f r) (Whole.empirical (X (Real.toNNReal r) ζ))
              (Whole.empirical (X (Real.toNNReal r) ζ))))
        - ∫ r in Set.Icc (0 : ℝ) τ, (Whole.pair (Whole.withDensityReal (ρ r))
            (driftTestRd D f (fun r x => -(generatorW (D.coeff ρ) r (f r) x)) r)
          + interactionPairingW D (f r) (Whole.withDensityReal (ρ r)) (Whole.withDensityReal (ρ r))) := by
      rw [← integral_sub hI1 hI2]
      exact setIntegral_congr_fun measurableSet_Icc fun r hr => (hpt r hr).symm
    rw [hsub]
    change _ = _ + (Real.sqrt (2 * D.invβ) / N) *
      itoIntegral P ℱ W' (truncGradIntegrand t f X) τ ζ + _
    linarith


theorem s56_duality (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) {N : ℕ}
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hX : IsWholeStrongSolution P (S.dyn N) b.T X₀ W X) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsWholeFilteredSolution P ℱ W' W X)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) b.T) (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ)
    (hf : IsClassicalAdjointW (S.coeff N) t φ f) :
    DualityIdentityRd P ℱ W' (S.dyn N) (S.ρ N) X t f := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hk0 : (0 : ℝ) ≤ b.k := Nat.cast_nonneg b.k
  have hL := hbv.hL
  have hdL : (d : ℝ) + 3 ≤ b.L := by linarith [hbv.hs0]
  have hn : 3 ≤ b.k + 6 + ⌈(d : ℝ) / 2⌉₊ := by omega
  have hΛ3le : b.Λ ≤ (∑ j ∈ Finset.range 4, (d : ℝ) ^ j + 1) * max b.Λ 0 := by
    have h1 : 1 ≤ ∑ j ∈ Finset.range 4, (d : ℝ) ^ j + 1 := by
      have : (0 : ℝ) ≤ ∑ j ∈ Finset.range 4, (d : ℝ) ^ j :=
        Finset.sum_nonneg fun _ _ => by positivity
      linarith
    calc b.Λ ≤ max b.Λ 0 := le_max_left _ _
      _ = 1 * max b.Λ 0 := (one_mul _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 (le_max_right _ _)
  obtain ⟨ΛV, G₀, hM⟩ := HRS.MS.Go.s55f_mfdata hn hdL hbv.hs0 hbv.hsd b.M b.Q hbv.hQ b.c (S.hinvβ N).1
    (S.mf N) (S.dens N) (fun h t ht x => (S.force h N t ht x).trans hΛ3le)
  exact s56_duality_core b.s _ b.T ΛV G₀ (S.dyn N) hM.hs hM.hs0 hM.hsd hM.hinv hM.hV (S.ρ N) hM.hρ hM.hreg
    P X₀ W X hX ℱ W' hF t ht φ f hf

end HRS.MS.GenPath
