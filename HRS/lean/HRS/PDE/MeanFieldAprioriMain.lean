import HRS.PDE.MeanFieldAprioriLower

/-!
# A priori bounds for the finite-regularity mean-field equation, packet AP7 (assembly)

`mf_apriori_bound_real_on` is the time-local form of the input (I3): on every real solution on
`[0,T]`, `c ≤ ρ ≤ C` and `‖ρ̂‖_{H^K} ≤ C`, with `c, C` independent of `T` and of `β ∈ [β₋, β₊]`.
It combines the uniform lower bound (`exists_inf_bound`, AP6b), the uniform upper bound
(`exists_sup_bound`, AP4) and the uniform `H^K` bound (`exists_hK_bound`, AP5c2), applied with the
viscosity range `ν = β⁻¹ ∈ [β₊⁻¹, β₋⁻¹]`.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.PDE.MFApriori

variable {d : ℕ}

theorem mf_apriori_bound_real_on (hd : 1 ≤ d) (s βm βp : ℝ) (K : ℕ) (V ρ₀ : Torus d → ℝ)
    (H : FiniteRegHyp d s βm βp K V ρ₀) :
    ∃ c C : ℝ, 0 < c ∧ ∀ β ∈ Set.Icc βm βp, ∀ (T : ℝ) (ρc : ℝ → Coeff d),
      MFSolRealOn d s V β⁻¹ K ρ₀ ρc T → ∀ t ∈ Set.Icc 0 T,
        (∀ x, c ≤ mfPath ρc t x ∧ mfPath ρc t x ≤ C) ∧ hsNorm K (ρc t) ≤ C := by
  have hβp : 0 < βp := lt_of_lt_of_le H.hβm H.hββ
  have hKd : (d : ℝ) / 2 + 2 < K := by
    have := H.hK
    linarith
  have hνm : 0 < βp⁻¹ := inv_pos.2 hβp
  have hνν : βp⁻¹ ≤ βm⁻¹ := inv_anti₀ H.hβm H.hββ
  obtain ⟨Λ, hΛ0, hΛ⟩ := exists_sup_bound hd s H.hs0 H.hsd K hKd V H.hV βp⁻¹ βm⁻¹ hνm hνν ρ₀
    H.hρ₀ H.hρ₀H H.hρ₀pos
  obtain ⟨CK, hCK0, hCK⟩ := exists_hK_bound hd s H.hs0 H.hsd K hKd V H.hV βp⁻¹ βm⁻¹ hνm hνν ρ₀
    H.hρ₀H Λ
  obtain ⟨c, hc, hcb⟩ := exists_inf_bound hd s H.hs0 H.hsd K hKd V H.hV βp⁻¹ βm⁻¹ hνm hνν ρ₀
    H.hρ₀ H.hρ₀H H.hρ₀pos
  refine ⟨c, max Λ CK, hc, fun β hβ T ρc hsol t ht => ?_⟩
  have hβ0 : 0 < β := lt_of_lt_of_le H.hβm hβ.1
  have hνβ : β⁻¹ ∈ Set.Icc βp⁻¹ βm⁻¹ :=
    ⟨inv_anti₀ hβ0 hβ.2, inv_anti₀ H.hβm hβ.1⟩
  have hup := hΛ β⁻¹ hνβ T ρc hsol
  have habs : ∀ t ∈ Set.Icc 0 T, ∀ x, |mfPath ρc t x| ≤ Λ := fun t ht x =>
    (abs_of_nonneg (hup t ht x).1).le.trans (hup t ht x).2
  refine ⟨fun x => ⟨hcb β⁻¹ hνβ T ρc hsol t ht x, (hup t ht x).2.trans (le_max_left _ _)⟩, ?_⟩
  exact (hCK β⁻¹ hνβ T ρc hsol habs t ht).trans (le_max_right _ _)

end HRS.PDE.MFApriori
