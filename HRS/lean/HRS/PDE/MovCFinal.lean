import HRS.PDE.MovCAux1
import HRS.PDE.MovCAux2
import HRS.PDE.MovCAux6
import HRS.PDE.MovCAux9
import HRS.PDE.MovCAux10
import HRS.PDE.MovCAux15

/-!
# MOVC: relocated proofs of MovSpec1 packets (`movT_gReg_L1_tendsto`, `movT_convFun_tendstoUniformly`,
`movT_srcReg_measurable`, ...).  Statements verbatim; each tied by `example := (@x_proof : type_of% @HRS.x)`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem movT_gReg_L1_tendsto_proof (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {M : ℕ → ℝ}
    (hM : Tendsto M atTop atTop) (hM0 : ∀ n, 0 ≤ M n) :
    Tendsto (fun n => ∫ z : Torus d, |periodicRiesz d s z - b15c_gReg d s (M n) z|) atTop (𝓝 0) :=
  movc_gReg_L1_tendsto hd hs0 hsd hM hM0

example := (@movT_gReg_L1_tendsto_proof : type_of% @HRS.movT_gReg_L1_tendsto)

theorem movT_convFun_tendstoUniformly_proof (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {M : ℕ → ℝ}
    (hM : Tendsto M atTop atTop) (hM0 : ∀ n, 0 ≤ M n) {f : Torus d → ℝ} (hf : Continuous f) :
    TendstoUniformly (fun n x => convFun (b15c_gReg d s (M n)) f x) (convFun (periodicRiesz d s) f)
      atTop :=
  movc_convFun_tendstoUniformly hd hs0 hsd hM hM0 hf

example := (@movT_convFun_tendstoUniformly_proof : type_of% @HRS.movT_convFun_tendstoUniformly)

theorem movT_srcReg_measurable_proof {D : DynData d} {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ} (h : MovTraj D T ρ)
    (hρt : IsC12Test T ρ ρt) (M : ℝ) {r : ℝ} (hr : r ∈ Set.Icc 0 T) :
    Measurable (movT_srcReg D N M ρ ρt r) :=
  movc_srcReg_measurable h hρt M hr

example := (@movT_srcReg_measurable_proof : type_of% @HRS.movT_srcReg_measurable)

theorem movT_Q_tendsto_weak_proof (hN : 2 ≤ N) {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ}
    (h : MovTraj D T ρ) {M : ℕ → ℝ} (hM : Tendsto M atTop atTop) (hM0 : ∀ n, 0 ≤ M n) {r : ℝ}
    (hr : r ∈ Set.Icc 0 T) {φ : Config d N → ℝ} (hφ : Continuous φ) :
    Tendsto (fun n => ∫ X, φ X ∂(movT_Q (b15c_gReg d D.s (M n)) D N ρ r)) atTop
      (𝓝 (∫ X, φ X ∂(movT_Q (periodicRiesz d D.s) D N ρ r))) :=
  movc_Q_tendsto_weak hN h hM hM0 hr hφ

example := (@movT_Q_tendsto_weak_proof : type_of% @HRS.movT_Q_tendsto_weak)

theorem movT_init_tendsto_proof (hN : 2 ≤ N) {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ}
    (hT : 0 ≤ T) (h : MovTraj D T ρ) {M : ℕ → ℝ} (hM : Tendsto M atTop atTop) (hM0 : ∀ n, 0 ≤ M n)
    {ν : Measure (Config d N)} [IsProbabilityMeasure ν]
    (hfin : relEntropy ν (movT_Q (periodicRiesz d D.s) D N ρ 0) ≠ ⊤) :
    (∀ n, relEntropy ν (movT_Q (b15c_gReg d D.s (M n)) D N ρ 0) ≠ ⊤) ∧
      Tendsto (fun n => (relEntropy ν (movT_Q (b15c_gReg d D.s (M n)) D N ρ 0)).toReal) atTop
        (𝓝 (relEntropy ν (movT_Q (periodicRiesz d D.s) D N ρ 0)).toReal) :=
  movc_init_tendsto hN hT h hM hM0 hfin

example := (@movT_init_tendsto_proof : type_of% @HRS.movT_init_tendsto)

theorem movT_regSeq_exists_proof {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {D : DynData d} {T : ℝ} {ρ : ℝ → Torus d → ℝ} {X₀ : Ω → Config d N}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → Config d N}
    (h : MovHyp P D N T ρ X₀ W X) :
    ∃ (ℱ : Filtration ℝ mΩ) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (M : ℕ → ℝ) (Y₀ : Ω → Fin N → Euc d)
      (Y : ℕ → ℝ → Ω → (Fin N → Euc d)), MovRegSeq P ℱ W' D T X₀ W X M Y₀ Y :=
  movc_regSeq_exists h

example := (@movT_regSeq_exists_proof : type_of% @HRS.movT_regSeq_exists)

/-- `movT_srcReg_tendsto` with the extra hypothesis `0 < T`.  The statement is FALSE for `T = 0`: `IsC12Test.time_deriv`
is vacuous on `Ioo 0 0`, so `ρt 0` is an arbitrary continuous function, while the exact source `movT_source` does not
depend on `ρt`; counterexample `ρ ≡ 1`, `V = 0`, `ρt 0 = cos(2π x₁)` (see ISSUES "MOVA"): `movT_source = 0` but
`S^M(X) → -κ ∑ᵢ cos(2π X_{i,1})` with `κ = 1 + β ĝ(e₁) > 0`. -/
theorem movT_srcReg_tendsto_proof_pos (hN : 2 ≤ N) {D : DynData d} {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ}
    (h : MovTraj D T ρ) (hρt : IsC12Test T ρ ρt) (hT : 0 < T) {M : ℕ → ℝ}
    (hM : Tendsto M atTop atTop) {r : ℝ}
    (hr : r ∈ Set.Icc 0 T) {X : Config d N} (hX : X ∉ collisionSet d N) :
    Tendsto (fun n => movT_srcReg D N (M n) ρ ρt r X) atTop (𝓝 (movT_source D N ρ r X)) :=
  movc_srcReg_tendsto_pos hN h hρt hT hM hr hX

end HRS
