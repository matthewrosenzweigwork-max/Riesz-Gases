import HRS.Main.Det22Aux4

/-!
# Packet DET22, final: `deterministic_comparison`, `deterministic_comparison_matrix` (Example 2.2)

Relocation pattern: statements verbatim from `HRS/Main/Headline.lean:296, 322`; see the header of `Det22Aux1.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

namespace Main

variable {d : ℕ}

theorem deterministic_comparison_proof (b : GeneralBounds d) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ S : GeneralSetup d, S.Within { b with C₀ := C₀ } → S.MFHyp → S.PosDensityWith b.c →
      (∀ N, S.invβ N = 0) →
      ∀ (N : ℕ) (_ : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (x₀ : Config d N)
      (W : ℝ≥0 → Ω → (Fin N → Euc d)) (_ : IsVectorBrownian P W)
      (X : ℝ≥0 → Ω → Config d N)
      (_ : IsStrongSolution P (S.dyn N) S.T (fun _ => x₀) W X)
      (_ : ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
        (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X)
      (_ : S.EnergyMomentFinite P N X) (F : NegSobolev d (S.γ : ℝ)),
      ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) S.T,
        ‖S.κ N • NegSobolev.ofMeasureDiff (S.γ : ℝ) (empirical (X (Real.toNNReal t) ω))
            (withDensityReal (S.ρ N t)) - transportField (S.dyn N) (S.ρ N) t (S.γ : ℝ) F‖ ≤
          C * (‖S.κ N • NegSobolev.ofMeasureDiff (S.γ : ℝ) (empirical x₀)
              (withDensityReal (S.ρ N 0)) - F‖ + S.κ N * S.energyMoment P N X) := by

  obtain ⟨C₀min, hmain⟩ := HRS.GeneralSetup.general_fluctuation_proof b
  obtain ⟨K, hK0, hev⟩ := HRS.GF.gf_ev_grad_proof b
  refine ⟨C₀min, fun C₀ hC₀ => ?_⟩
  obtain ⟨C, hC, h⟩ := hmain C₀ hC₀
  refine ⟨C, hC, ?_⟩
  intro S hS hMF hPos hβ N hN Ω _ P _ x₀ W hW X hX hflt hE F
  have hSw : S.Within { b with C₀ := S.C₀ } := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hS
    exact ⟨h1, h2, h3, h4, h5, rfl, h7⟩
  obtain ⟨EV, hEV⟩ := hev S hSw hMF hPos N
  have hself : ∀ t ∈ Set.Icc (0 : ℝ) S.T, EV.VE t t = 1 := hEV.maxHyp.1.self_E
  refine HRS.Det22.det22_assemble S (-1) hMF N hN _ le_rfl P x₀ W hW X hX hflt hE (hβ N) EV.VE
    hEV.dual hself hEV.maxHyp.1.cont_E F F C hC ?_
  intro Y hY
  have hfin : S.InitialErrorFinite P N 1 (fun _ => x₀) (fun _ => F) := integrable_const _
  have hind : ProbabilityTheory.IndepFun (fun ω => ((fun _ => x₀) ω, (fun _ => F) ω))
      (fun ω => fun t => W t ω) P := indepFun_const_left _ _
  obtain ⟨-, hW1, -⟩ := h S hS hMF hPos N hN P (fun _ => x₀) W hW X hX hflt hE (fun _ => F)
    measurable_const hind hfin Y hY
  exact hW1

theorem deterministic_comparison_matrix_proof (b : GeneralBounds d) (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : Torus.SymNonpos M) (K : ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ S : GeneralSetup d, S.Within { b with C₀ := C₀ } → S.MFHypM M → S.AdjointInput M K →
      (∀ N, S.invβ N = 0) →
      ∀ (N : ℕ) (_ : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (x₀ : Config d N)
      (W : ℝ≥0 → Ω → (Fin N → Euc d)) (_ : IsVectorBrownian P W)
      (X : ℝ≥0 → Ω → Config d N)
      (_ : IsStrongSolution P (S.dynM M N) S.T (fun _ => x₀) W X)
      (_ : ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
        (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X)
      (_ : S.EnergyMomentFinite P N X) (F : NegSobolev d (S.γ : ℝ)),
      ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) S.T,
        ‖S.κ N • NegSobolev.ofMeasureDiff ((S.γ : ℝ) + 2) (empirical (X (Real.toNNReal t) ω))
            (withDensityReal (S.ρ N t)) -
          transportField (S.dynM M N) (S.ρ N) t ((S.γ : ℝ) + 2)
            (NegSobolev.embed ((S.γ : ℝ) + 2) F)‖ ≤
          C * (‖S.κ N • NegSobolev.ofMeasureDiff (S.γ : ℝ) (empirical x₀)
              (withDensityReal (S.ρ N 0)) - F‖ + S.κ N * S.energyMoment P N X) := by

  obtain ⟨C₀min, hmain⟩ := HRS.GeneralSetup.general_fluctuation_matrix_proof b M hM K
  obtain ⟨K', hK0, hev⟩ := HRS.GF.gf_ev_mat_proof b M hM K
  refine ⟨C₀min, fun C₀ hC₀ => ?_⟩
  obtain ⟨C, hC, h⟩ := hmain C₀ hC₀
  refine ⟨C, hC, ?_⟩
  intro S hS hMF hAdj hβ N hN Ω _ P _ x₀ W hW X hX hflt hE F
  have hSw : S.Within { b with C₀ := S.C₀ } := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hS
    exact ⟨h1, h2, h3, h4, h5, rfl, h7⟩
  obtain ⟨EV, hEV⟩ := hev S hSw hMF hAdj N
  have hself : ∀ t ∈ Set.Icc (0 : ℝ) S.T, EV.VE t t = 1 := hEV.maxHyp.1.self_E
  refine HRS.Det22.det22_assemble S M hMF N hN ((S.γ : ℝ) + 2) (by linarith) P x₀ W hW X hX hflt hE
    (hβ N) EV.VE hEV.dual hself hEV.maxHyp.1.cont_E (NegSobolev.embed ((S.γ : ℝ) + 2) F) F C hC ?_
  intro Y hY
  have hfin : S.InitialErrorFinite P N 1 (fun _ => x₀) (fun _ => F) := integrable_const _
  have hind : ProbabilityTheory.IndepFun (fun ω => ((fun _ => x₀) ω, (fun _ => F) ω))
      (fun ω => fun t => W t ω) P := indepFun_const_left _ _
  obtain ⟨-, hW1, -⟩ := h S hS hMF hAdj N hN P (fun _ => x₀) W hW X hX hflt hE (fun _ => F)
    measurable_const hind hfin Y hY
  exact hW1

example := (@deterministic_comparison_proof : type_of% @HRS.Main.deterministic_comparison)
example := (@deterministic_comparison_matrix_proof : type_of% @HRS.Main.deterministic_comparison_matrix)

end Main

end HRS
