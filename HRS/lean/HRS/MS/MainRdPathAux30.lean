import HRS.MS.MainRdPathAux29

/-!
# S.A.10: `iid_path_rd_cond_proof`

The statement of `HRS.Whole.AppendixA.iid_path_rd` with the one extra hypothesis `∀ N ≥ 1, AEMeasurable (R N).η (R N).P`
(after `IidSettingRd S R`).  Without it the statement is not provable: for a non-a.e.-measurable `(R N).η` (the Gaussian-bridge
clause only constrains the evaluations at `C_b^1` tests) the law `law (R N).P (R N).η` is a fixed junk Dirac mass.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdPath

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.IidInit

theorem iid_path_rd_cond_proof (s : ℝ) {d : ℕ} (fd : FieldDensityRd d s)
    (ν₀ MB Λ ΛV G₀ νbar T Cin m20 : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) (Kad Kadj Kst : ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ →
    ∀ (S : WholeMainData d), S.s = s → S.T = T → (∀ N, S.invβ N ≤ νbar) → fd.Holds S ν₀ →
    ∀ (R : ∀ N, RealizationRd d N) (𝔈 : ℕ → ℝ), IidSettingRd S R →
      (∀ N : ℕ, 1 ≤ N → AEMeasurable (R N).η (R N).P) →
      RdStanding S R MB Λ ΛV G₀ m20 (fd.Gamma + 5) (fd.Gamma + 5) C₀ 𝔈 →
      ∀ m₂ : ℝ, 0 ≤ m₂ → PropagatedSecondMoment S R m₂ →
      ∀ (m₀ : ℕ) (ε : ℕ → ℝ), InitialFluctuationRd S R χ m₀ Cin ε (fun _ => ∅) →
      ∀ (εf : ℕ → ℝ) (Iemp I : ∀ N, ℝ → (R N).Ω → HNeg d (fd.Gamma : ℝ)),
        TransportedInitialFieldRd S R fd.Gamma Cin εf Iemp I →
        InitialFieldDist S R fd.Gamma εf Iemp I →
      ∀ L : LimitCoeffsRd d, fd.HoldsAt S.s S.M L.invβ ν₀ →
        CoeffConvergenceRd S L MB Λ ΛV G₀ νbar (fd.Gamma + 2) fd.Gamma →
      ∀ K : ℝ, WeightedPathInput S (L.coeff S) (m₀ + 1) (fd.Gamma + 2) K →
      FieldAdjointInputRd fd S Kad →
        AdjointDerivInput ((fd.Gamma + 2 : ℕ) : ℝ) (m₀ + 1) S.coeff S.T Kadj →
        AdjointInputOneD ((fd.Gamma + 2 : ℕ) : ℝ) (m₀ + 1) (L.coeff S) S.T Kadj →
        AdjointStabilityInputRd S L (fd.Gamma + 2) (m₀ + 1) fd.Gamma Kst →
      Tendsto (fun N => εf N + S.sigma N * (𝔈 N + fd.eN N) + S.qN N * wN d N (𝔈 N) m₂) atTop (𝓝 0) →
        RdPathConclusion S R L (fd.Gamma + 2) := by
  obtain ⟨C, hC⟩ := main_rd_path_proof s fd ν₀ MB Λ ΛV G₀ νbar T Cin m20 χ hχ Kad Kadj Kst
  refine ⟨C, fun C₀ hC₀ S hs hT hinv hH R 𝔈 hid hηm hS m₂ hm₂0 hm₂ m₀ ε hinit εf Iemp I hTIF hdist L
    hHA hcoef K hW hFA hAdjP hAdjL hStab hsm => ?_⟩
  have hX0 : ∀ N : ℕ, 1 ≤ N → Measurable (R N).X₀ := fun N hN => (hS.flow N hN).init_meas
  have hFI := sa27_fieldInput (Nat.le_add_left 1 m₀) hAdjP
  obtain ⟨Iq, Jq, hrepr⟩ := sa9_init_repr S R hid hX0 (fd.Gamma + 2) _ hFI
  have hfix := sa9_iid_fix S L R hid hηm (fd.Gamma + 2) fd.Gamma m₀ Kadj Kst hinit.m₀_pos hAdjP hAdjL
    hStab hcoef.tendsto
  have hemp : ∀ (p : ℕ) (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ), (∀ a, ts a ∈ Set.Icc (0 : ℝ) T) →
      (∀ a, ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = φ a) → EmpiricalInitialVectorConverges S R L ts φ := by
    intro p ts φ hts hφ
    refine sa9_iid_emp S L R hid hX0 hηm (fd.Gamma + 2) fd.Gamma m₀ Kadj Kst hinit.m₀_pos hAdjP hAdjL
      hStab hcoef.tendsto Iq Jq hrepr ts φ (fun a => hT ▸ hts a) fun a => ?_
    obtain ⟨ψ, hψ⟩ := hφ a
    rw [← hψ]
    exact HRS.MS.PathFidi.sa26_schwartz_sob ψ (fd.Gamma + 2)
  exact hC C₀ hC₀ S hs hT hinv hH R 𝔈 hS m₂ hm₂0 hm₂ m₀ ε hinit εf Iemp I hTIF hdist L hHA hcoef K hW hFA
    hAdjP hAdjL hStab hsm hfix hemp

end HRS.MS.MainRdPath
