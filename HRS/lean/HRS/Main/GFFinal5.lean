import HRS.Main.GFFinal4

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS.Uniform

variable {d : ℕ}

/-- **`general_fluctuation` (Theorem 2.1, gradient clause) from the sub-packet statements** (PROVED, conditional on the sorried
packets; the type is the frozen statement, checked by the `example` below). -/
theorem gff_general_fluctuation (b : GeneralBounds d) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ S : GeneralSetup d, S.Within { b with C₀ := C₀ } → S.MFHyp → S.PosDensityWith b.c →
      ∀ (N : ℕ) (_ : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P]
      (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (_ : IsVectorBrownian P W)
      (X : ℝ≥0 → Ω → Config d N) (_ : IsStrongSolution P (S.dyn N) S.T X₀ W X)
      (_ : ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
        (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X)
      (_ : S.EnergyMomentFinite P N X)
      (η₀ : Ω → NegSobolev d S.γ) (_ : Measurable η₀)
      (_ : ProbabilityTheory.IndepFun (fun ω => (X₀ ω, η₀ ω)) (fun ω => fun t => W t ω) P)
      (_ : S.InitialErrorFinite P N 1 X₀ η₀)
      (Y : ℝ → Ω → NegSobolev d S.γ)
      (_ : IsLinearFluctuationSolution P (S.dyn N) (S.ρ N) S.γ (qScale N (S.κ N) (S.invβ N)) S.T
        (fun ω => Ascale N (S.κ N) (S.invβ N) • η₀ ω) Y),
      let σ := sigmaScale N (S.κ N) (S.invβ N)
      let A := Ascale N (S.κ N) (S.invβ N)
      let q := qScale N (S.κ N) (S.invβ N)
      let 𝔈 := S.energyMoment P N X
      let Ξ := law P (flucPath S.γ S.T σ X (S.ρ N))
      let YN := law P (toPath S.γ S.T Y)
      smoothDist 2 Ξ YN ≤
          C * (A * S.initialError P N 1 X₀ η₀ + σ * 𝔈 + q * (Real.sqrt 𝔈 + (N : ℝ) ^ (-(2 : ℝ) / d))) ∧
      wassersteinE 1 Ξ YN ≤ ENNReal.ofReal
          (C * (A * S.initialError P N 1 X₀ η₀ + σ * 𝔈 +
            Real.sqrt q * (𝔈 ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d)))) ∧
      (S.EnergyMoment2Finite P N X →
        Integrable (fun ω => ‖flucPath S.γ S.T σ X (S.ρ N) ω‖ ^ 2) P →
        S.InitialErrorFinite P N 2 X₀ η₀ →
        wassersteinE 2 Ξ YN ≤ ENNReal.ofReal
          (C * (A * S.initialError P N 2 X₀ η₀ + σ * S.energyMoment2 P N X +
            Real.sqrt q * (𝔈 ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d))))) := by
  obtain ⟨K, hK0, hev⟩ := gf_ev_grad_proof b
  obtain ⟨C₀min, hcore⟩ := gff_core b (-1) (fun S => S.PosDensityWith b.c) (fun S => (S.γ : ℝ))
    (fun S => le_rfl) (fun S x => x) K
    (fun S hS hMF hPos N => by
      obtain ⟨EV, hEV⟩ := hev S hS hMF hPos N
      exact ⟨EV, hEV, fun x => by rw [hEV.j_eq, embed_self]⟩)
  refine ⟨C₀min, fun C₀ hC₀ => ?_⟩
  obtain ⟨C, hC, h⟩ := hcore C₀ hC₀
  refine ⟨C, hC, ?_⟩
  intro S hS hMF hPos N hN Ω _ P _ X₀ W hW X hX hF hE η₀ hη hind hfin Y hY
  exact h S hS hMF hPos N hN P X₀ W X hX hF hE η₀ hη hind hfin Y hY

/-- **`general_fluctuation_matrix` (Theorem 2.1, general-matrix clause) from the sub-packet statements** (PROVED, conditional on the
sorried packets). -/
theorem gff_general_fluctuation_matrix (b : GeneralBounds d) (M : Matrix (Fin d) (Fin d) ℝ)
    (hM : Torus.SymNonpos M) (K : ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ S : GeneralSetup d, S.Within { b with C₀ := C₀ } → S.MFHypM M → S.AdjointInput M K →
      ∀ (N : ℕ) (_ : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P]
      (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (_ : IsVectorBrownian P W)
      (X : ℝ≥0 → Ω → Config d N) (_ : IsStrongSolution P (S.dynM M N) S.T X₀ W X)
      (_ : ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
        (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X)
      (_ : S.EnergyMomentFinite P N X)
      (η₀ : Ω → NegSobolev d S.γ) (_ : Measurable η₀)
      (_ : ProbabilityTheory.IndepFun (fun ω => (X₀ ω, η₀ ω)) (fun ω => fun t => W t ω) P)
      (_ : S.InitialErrorFinite P N 1 X₀ η₀)
      (Y : ℝ → Ω → NegSobolev d ((S.γ : ℝ) + 2))
      (_ : IsLinearFluctuationSolution P (S.dynM M N) (S.ρ N) ((S.γ : ℝ) + 2)
        (qScale N (S.κ N) (S.invβ N)) S.T
        (fun ω => Ascale N (S.κ N) (S.invβ N) • NegSobolev.embed ((S.γ : ℝ) + 2) (η₀ ω)) Y),
      let σ := sigmaScale N (S.κ N) (S.invβ N)
      let A := Ascale N (S.κ N) (S.invβ N)
      let q := qScale N (S.κ N) (S.invβ N)
      let 𝔈 := S.energyMoment P N X
      let Ξ := law P (flucPath ((S.γ : ℝ) + 2) S.T σ X (S.ρ N))
      let YN := law P (toPath ((S.γ : ℝ) + 2) S.T Y)
      smoothDist 2 Ξ YN ≤
          C * (A * S.initialError P N 1 X₀ η₀ + σ * 𝔈 + q * (Real.sqrt 𝔈 + (N : ℝ) ^ (-(2 : ℝ) / d))) ∧
      wassersteinE 1 Ξ YN ≤ ENNReal.ofReal
          (C * (A * S.initialError P N 1 X₀ η₀ + σ * 𝔈 +
            Real.sqrt q * (𝔈 ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d)))) ∧
      (S.EnergyMoment2Finite P N X →
        Integrable (fun ω => ‖flucPath ((S.γ : ℝ) + 2) S.T σ X (S.ρ N) ω‖ ^ 2) P →
        S.InitialErrorFinite P N 2 X₀ η₀ →
        wassersteinE 2 Ξ YN ≤ ENNReal.ofReal
          (C * (A * S.initialError P N 2 X₀ η₀ + σ * S.energyMoment2 P N X +
            Real.sqrt q * (𝔈 ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d))))) := by
  obtain ⟨K', hK0, hev⟩ := gf_ev_mat_proof b M hM K
  obtain ⟨C₀min, hcore⟩ := gff_core b M (fun S => S.AdjointInput M K) (fun S => (S.γ : ℝ) + 2)
    (fun S => by linarith) (fun S => NegSobolev.embed ((S.γ : ℝ) + 2)) K'
    (fun S hS hMF hAdj N => by
      obtain ⟨EV, hEV⟩ := hev S hS hMF hAdj N
      exact ⟨EV, hEV, fun x => hEV.j_eq x⟩)
  refine ⟨C₀min, fun C₀ hC₀ => ?_⟩
  obtain ⟨C, hC, h⟩ := hcore C₀ hC₀
  refine ⟨C, hC, ?_⟩
  intro S hS hMF hAdj N hN Ω _ P _ X₀ W hW X hX hF hE η₀ hη hind hfin Y hY
  exact h S hS hMF hAdj N hN P X₀ W X hX hF hE η₀ hη hind hfin Y hY

/-- **`general_fluctuation_transport` (Theorem 2.1, transport improvement) from the sub-packet statements** (PROVED, conditional on
the sorried packets): the minimum of the trace-norm coupling bound (`gff_core`) and the transport coupling bound (`gff_core_transport`). -/
theorem gff_general_fluctuation_transport (b : GeneralBounds d) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ S : GeneralSetup d, S.Within { b with C₀ := C₀ } → S.MFHyp → S.PosDensityWith b.c →
      ∀ (N : ℕ) (_ : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P]
      (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (_ : IsVectorBrownian P W)
      (X : ℝ≥0 → Ω → Config d N) (_ : IsStrongSolution P (S.dyn N) S.T X₀ W X)
      (_ : ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
        (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ), IsFilteredSolution P ℱ W' W X)
      (_ : S.EnergyMomentFinite P N X)
      (η₀ : Ω → NegSobolev d S.γ) (_ : Measurable η₀)
      (_ : ProbabilityTheory.IndepFun (fun ω => (X₀ ω, η₀ ω)) (fun ω => fun t => W t ω) P)
      (_ : S.InitialErrorFinite P N 1 X₀ η₀)
      (Y : ℝ → Ω → NegSobolev d S.γ)
      (_ : IsLinearFluctuationSolution P (S.dyn N) (S.ρ N) S.γ (qScale N (S.κ N) (S.invβ N)) S.T
        (fun ω => Ascale N (S.κ N) (S.invβ N) • η₀ ω) Y),
      let σ := sigmaScale N (S.κ N) (S.invβ N)
      let A := Ascale N (S.κ N) (S.invβ N)
      let q := qScale N (S.κ N) (S.invβ N)
      let 𝔈 := S.energyMoment P N X
      let cov := Real.sqrt q * min (𝔈 ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d))
        (𝔈 ^ ((1 : ℝ) / max 2 ((d : ℝ) - S.s)) + (N : ℝ) ^ (-(1 : ℝ) / d))
      let Ξ := law P (flucPath S.γ S.T σ X (S.ρ N))
      let YN := law P (toPath S.γ S.T Y)
      wassersteinE 1 Ξ YN ≤ ENNReal.ofReal
          (C * (A * S.initialError P N 1 X₀ η₀ + σ * 𝔈 + cov)) ∧
      (S.EnergyMoment2Finite P N X →
        Integrable (fun ω => ‖flucPath S.γ S.T σ X (S.ρ N) ω‖ ^ 2) P →
        S.InitialErrorFinite P N 2 X₀ η₀ →
        wassersteinE 2 Ξ YN ≤ ENNReal.ofReal
          (C * (A * S.initialError P N 2 X₀ η₀ + σ * S.energyMoment2 P N X + cov))) := by
  obtain ⟨K, hK0, hev⟩ := gf_ev_grad_proof b
  obtain ⟨C₀a, hcore⟩ := gff_core b (-1) (fun S => S.PosDensityWith b.c) (fun S => (S.γ : ℝ))
    (fun S => le_rfl) (fun S x => x) K
    (fun S hS hMF hPos N => by
      obtain ⟨EV, hEV⟩ := hev S hS hMF hPos N
      exact ⟨EV, hEV, fun x => by rw [hEV.j_eq, embed_self]⟩)
  obtain ⟨C₀b, hcoreT⟩ := gff_core_transport b
  refine ⟨max C₀a C₀b, fun C₀ hC₀ => ?_⟩
  obtain ⟨C₁, hC₁, h₁⟩ := hcore C₀ (le_trans (le_max_left _ _) hC₀)
  obtain ⟨C₂, hC₂, h₂⟩ := hcoreT C₀ (le_trans (le_max_right _ _) hC₀)
  refine ⟨max C₁ C₂, lt_max_of_lt_left hC₁, ?_⟩
  intro S hS hMF hPos N hN Ω _ P _ X₀ W hW X hX hF hE η₀ hη hind hfin Y hY
  have hq0 := qN_nonneg S N
  have hσ0 := sigN_nonneg S N
  have hA0 := AN_nonneg S N
  have hE0 := gff_energyMoment_nonneg S (-1) hMF N hN P X₀ W X hX hF hE
  have hε1 := initialError_nonneg S P 1 X₀ η₀
  have hn0 : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / d) := Real.rpow_nonneg (Nat.cast_nonneg N) _
  obtain ⟨-, hW1a, hW2a⟩ := h₁ S hS hMF hPos N hN P X₀ W X hX hF hE η₀ hη hind hfin Y hY
  obtain ⟨hW1b, hW2b⟩ := h₂ S hS hMF hPos N hN P X₀ W X hX hF hE η₀ hη hind hfin Y hY
  dsimp only
  have hmax1 : C₁ ≤ max C₁ C₂ := le_max_left _ _
  have hmax2 : C₂ ≤ max C₁ C₂ := le_max_right _ _
  refine ⟨?_, fun hE2 hI hfin2 => ?_⟩
  · rcases le_total (S.energyMoment P N X ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d))
        (S.energyMoment P N X ^ ((1 : ℝ) / max 2 ((d : ℝ) - S.s)) + (N : ℝ) ^ (-(1 : ℝ) / d)) with h | h
    · rw [min_eq_left h]
      refine hW1a.trans (ENNReal.ofReal_le_ofReal ?_)
      have hz : 0 ≤ AN S N * S.initialError P N 1 X₀ η₀ + sigN S N * S.energyMoment P N X +
          Real.sqrt (qN S N) * (S.energyMoment P N X ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d)) := by
        have := Real.rpow_nonneg hE0 ((1 : ℝ) / 4)
        positivity
      exact mul_le_mul_of_nonneg_right hmax1 hz
    · rw [min_eq_right h]
      refine hW1b.trans (ENNReal.ofReal_le_ofReal ?_)
      have hz : 0 ≤ AN S N * S.initialError P N 1 X₀ η₀ + sigN S N * S.energyMoment P N X +
          Real.sqrt (qN S N) * (S.energyMoment P N X ^ ((1 : ℝ) / max 2 ((d : ℝ) - S.s)) +
            (N : ℝ) ^ (-(1 : ℝ) / d)) := by
        have := Real.rpow_nonneg hE0 ((1 : ℝ) / max 2 ((d : ℝ) - S.s))
        positivity
      exact mul_le_mul_of_nonneg_right hmax2 hz
  · have hE20 : 0 ≤ S.energyMoment2 P N X := by
      unfold GeneralSetup.energyMoment2
      exact Real.iSup_nonneg fun t => Real.sqrt_nonneg _
    have hε2 := initialError_nonneg S P 2 X₀ η₀
    rcases le_total (S.energyMoment P N X ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d))
        (S.energyMoment P N X ^ ((1 : ℝ) / max 2 ((d : ℝ) - S.s)) + (N : ℝ) ^ (-(1 : ℝ) / d)) with h | h
    · rw [min_eq_left h]
      refine (hW2a hE2 hI hfin2).trans (ENNReal.ofReal_le_ofReal ?_)
      have hz : 0 ≤ AN S N * S.initialError P N 2 X₀ η₀ + sigN S N * S.energyMoment2 P N X +
          Real.sqrt (qN S N) * (S.energyMoment P N X ^ ((1 : ℝ) / 4) + (N : ℝ) ^ (-(1 : ℝ) / d)) := by
        have := Real.rpow_nonneg hE0 ((1 : ℝ) / 4)
        positivity
      exact mul_le_mul_of_nonneg_right hmax1 hz
    · rw [min_eq_right h]
      refine (hW2b hE2 hI hfin2).trans (ENNReal.ofReal_le_ofReal ?_)
      have hz : 0 ≤ AN S N * S.initialError P N 2 X₀ η₀ + sigN S N * S.energyMoment2 P N X +
          Real.sqrt (qN S N) * (S.energyMoment P N X ^ ((1 : ℝ) / max 2 ((d : ℝ) - S.s)) +
            (N : ℝ) ^ (-(1 : ℝ) / d)) := by
        have := Real.rpow_nonneg hE0 ((1 : ℝ) / max 2 ((d : ℝ) - S.s))
        positivity
      exact mul_le_mul_of_nonneg_right hmax2 hz

end HRS.GF
