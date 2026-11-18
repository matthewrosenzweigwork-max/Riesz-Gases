import HRS.PDE.MovDAux1
import HRS.PDE.MovDAux3
import HRS.PDE.MovDAux4
import HRS.PDE.MovDAux7
import HRS.PDE.MovDAux11

/-!
# MOVD Final: relocated proofs of the MovSpec2b packets
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

theorem movT_cond_narrow_proof {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [TopologicalSpace α]
    [BorelSpace α]
    (P : Measure Ω) [IsProbabilityMeasure P] {Z : Ω → α} (hZ : Measurable Z) {A : ℕ → Set Ω}
    (hA : ∀ k, MeasurableSet (A k)) (hP : Tendsto (fun k => P (A k)) atTop (𝓝 1))
    {φ : α → ℝ} (hφ : Continuous φ) (hb : ∃ C, ∀ x, |φ x| ≤ C) :
    Tendsto (fun k => ∫ x, φ x ∂((movT_cond P (A k)).map Z)) atTop (𝓝 (∫ x, φ x ∂(P.map Z))) :=
  movd_cond_narrow P hZ hA hP hφ hb

example := (@movT_cond_narrow_proof : type_of% @HRS.movT_cond_narrow)

theorem movT_cond_hyp_proof {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ} {X₀ : Ω → Config d N}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (h : MovHyp P D N T ρ X₀ W X) {B : Set (Config d N)} (hB : MeasurableSet B)
    (h0 : P ((X 0) ⁻¹' B) ≠ 0) : MovHyp (movT_cond P ((X 0) ⁻¹' B)) D N T ρ X₀ W X :=
  movd_cond_hyp h hB h0

example := (@movT_cond_hyp_proof : type_of% @HRS.movT_cond_hyp)

theorem movT_cond_entropy_limit_proof {α : Type*} [MeasurableSpace α] (ν Q : Measure α)
    [IsProbabilityMeasure ν] [IsProbabilityMeasure Q] (hfin : relEntropy ν Q ≠ ⊤) :
    ∃ K₀ : ℕ, Tendsto (fun k : ℕ => ν (movT_truncSet ν Q k)) atTop (𝓝 1) ∧
      (∀ k : ℕ, K₀ ≤ k → ν (movT_truncSet ν Q k) ≠ 0 ∧ movT_truncLaw ν Q k ≪ Q ∧
        (∃ kk : ℝ, ∀ᵐ x ∂Q, (movT_truncLaw ν Q k).rnDeriv Q x ≤ ENNReal.ofReal kk) ∧
        relEntropy (movT_truncLaw ν Q k) Q ≠ ⊤) ∧
      Tendsto (fun k : ℕ => (relEntropy (movT_truncLaw ν Q k) Q).toReal) atTop
        (𝓝 (relEntropy ν Q).toReal) :=
  movd_cond_entropy_limit ν Q hfin

example := (@movT_cond_entropy_limit_proof : type_of% @HRS.movT_cond_entropy_limit)

/-- `movT_source_limit_cond`.  Tied to the packet statement; it depends on the sorried MovSpec1 packet
`movT_srcReg_tendsto` (MOVC) only through the joint measurability of the exact source off collisions
(`movd_source_joint_measurable`). -/
theorem movT_source_limit_cond_proof {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ} {X₀ : Ω → Config d N}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (hN : 2 ≤ N) (htr : MovTraj D T ρ) (hS : IsStrongSolution P D T X₀ W X) {A : ℕ → Set Ω}
    (hA : ∀ k, MeasurableSet (A k)) (hP : Tendsto (fun k => P (A k)) atTop (𝓝 1))
    (hexp : ∃ l C : ℝ, 0 < l ∧ ∀ r ∈ Set.Icc 0 T,
      ∫⁻ Z : Config d N, ENNReal.ofReal (Real.exp (l * |movT_source D N ρ r Z|))
        ∂(movT_Q (periodicRiesz d D.s) D N ρ r) ≤ ENNReal.ofReal (Real.exp C))
    (hH : ∃ C : ℝ, ∀ k, ∀ r ∈ Set.Icc 0 T,
      relEntropy ((movT_cond P (A k)).map (X r.toNNReal)) (movT_Q (periodicRiesz d D.s) D N ρ r) ≤
        ENNReal.ofReal C) :
    (∀ r ∈ Set.Icc 0 T, Integrable (movT_source D N ρ r) (P.map (X r.toNNReal))) ∧
    IntegrableOn (fun r => ∫ Z, movT_source D N ρ r Z ∂(P.map (X r.toNNReal))) (Set.Icc 0 T) ∧
    ∀ t ∈ Set.Icc 0 T,
      Tendsto (fun k => ∫ r in Set.Icc 0 t, ∫ Z, movT_source D N ρ r Z
        ∂((movT_cond P (A k)).map (X r.toNNReal))) atTop
        (𝓝 (∫ r in Set.Icc 0 t, ∫ Z, movT_source D N ρ r Z ∂(P.map (X r.toNNReal)))) :=
  movd_source_limit_cond hN htr hS hA hP hexp hH

example := (@movT_source_limit_cond_proof : type_of% @HRS.movT_source_limit_cond)

/-- `movT_source_limit_bdd`.  Tied to the packet statement; it depends on the sorried MovSpec1 packet
`movT_srcReg_tendsto` (MOVC): the regularised sources converge to the exact source off collisions. -/
theorem movT_source_limit_bdd_proof {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {D : DynData d} {T : ℝ}
    {ρ ρt : ℝ → Torus d → ℝ} {X₀ : Ω → Config d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {X : ℝ≥0 → Ω → Config d N} {M : ℕ → ℝ} {Y₀ : Ω → Fin N → Euc d}
    {Y : ℕ → ℝ → Ω → (Fin N → Euc d)}
    (hN : 2 ≤ N) (htr : MovTraj D T ρ) (hρt : IsC12Test T ρ ρt) (hS : IsStrongSolution P D T X₀ W X)
    (seq : MovRegSeq P ℱ W' D T X₀ W X M Y₀ Y)
    (hexp : ∃ l C : ℝ, 0 < l ∧ ∀ᶠ n in atTop, ∀ r ∈ Set.Icc 0 T,
      ∫⁻ Z : Config d N, ENNReal.ofReal (Real.exp (l * |movT_srcReg D N (M n) ρ ρt r Z|))
        ∂(movT_Q (b15c_gReg d D.s (M n)) D N ρ r) ≤ ENNReal.ofReal (Real.exp C))
    (hLq : ∃ q C : ℝ, 1 < q ∧ ∀ᶠ n in atTop, ∀ r ∈ Set.Icc 0 T,
      selectedLaw P (b15c_regProcess (Y n)) r ≪ movT_Q (b15c_gReg d D.s (M n)) D N ρ r ∧
      eLpNorm ((selectedLaw P (b15c_regProcess (Y n)) r).rnDeriv
          (movT_Q (b15c_gReg d D.s (M n)) D N ρ r)) (ENNReal.ofReal q)
        (movT_Q (b15c_gReg d D.s (M n)) D N ρ r) ≤ ENNReal.ofReal C) :
    (∀ r ∈ Set.Icc 0 T, Integrable (movT_source D N ρ r) (P.map (X r.toNNReal))) ∧
    IntegrableOn (fun r => ∫ Z, movT_source D N ρ r Z ∂(P.map (X r.toNNReal))) (Set.Icc 0 T) ∧
    ∀ t ∈ Set.Icc 0 T,
      Tendsto (fun n => ∫ r in Set.Icc 0 t, ∫ Z, movT_srcReg D N (M n) ρ ρt r Z
        ∂(selectedLaw P (b15c_regProcess (Y n)) r)) atTop
        (𝓝 (∫ r in Set.Icc 0 t, ∫ Z, movT_source D N ρ r Z ∂(P.map (X r.toNNReal)))) :=
  movd_source_limit_bdd hN htr hρt hS seq hexp hLq

example := (@movT_source_limit_bdd_proof : type_of% @HRS.movT_source_limit_bdd)

end HRS

end
