import HRS.MC.S7PIF5E

/-!
# Packet piF5 (F5): `s7_PIF_itoprocess_proof` (namespace `HRS.MC.Sec7.S7PIF5`)

The observation vector `obsVec(𝖳_u ζ_N)` is an Itô process of the filtered solution, with the explicit drift `b` and diffusion `Φc`.
The statement is copied verbatim from `HRS/MC/S7PIPlan.lean` (`HRS.MC.Sec7.PIPlan.s7_PIF_itoprocess`); the tie is in
`HRS/MC/S7PIF5Tie.lean`.  Route: parts A-E (progressive measurability and local integrability of `b` and `Φc`, `ℱ_s`-measurability of the
initial value) and, for the identity, `s7_PIF_coord_ito_proof` (F4) coordinate by coordinate, `localItoIntegralE_euclidean`,
`localItoIntegral_smul` and `localItoIntegral_eq_itoIntegral`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIF5

open HRS HRS.PDE HRS.A33 HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI HRS.MC.Sec7.S7PIF4 HRS.MC.Sec7.S7PIM

variable {d : ℕ}

section Prob

variable (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) (N : ℕ) (hN : 1 ≤ N)
  {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
  (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
  (hreal : PreparedRealization R.D P
    (modulatedGibbs (periodicRiesz d R.D.s) N R.β₀ (withDensityReal R.ρ₀)) X₀ W X)

include hm hT hN hreal

/-- the identity, coordinate by coordinate: the vector statement of F5 -/
theorem S7PIF5_identity {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution P ℱ W' W X) {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T) (hφ : ∀ i, Torus.IsSmooth (φ i)) :
    ∀ᵐ ω ∂P, ∀ u ∈ Set.Icc (0 : ℝ) T,
      obsVec m T t φ (predicted R.D R.ρ (zetaWin m T 0 P X ω) u) =
        itoProcess P ℱ W' (fun ω => obsVec m T t φ (initProp R.D R.ρ m T (zetaAt m P X 0 ω)))
          (S7PIF5_b R m P X t φ) (S7PIF5_Phi R X t φ) u ω := by
  have hW := hF.brownian
  have hL := fun i => S7PIF5_eni_L2 R m hm T hT N hN P X₀ W X hreal hF (ht i) (hφ i)
  have hΦ := S7PIF5_Phi_L2E R m hm T hT N hN P X₀ W X hreal hF t φ ht hφ
  have hbint := S7PIF5_b_int R m hm T hT N hN P X₀ W X hreal hF.progressive t φ ht hφ T
  have hcoord : ∀ i, ∀ᵐ ω ∂P, ∀ u ∈ Set.Icc (0 : ℝ) T, _ := fun i =>
    HRS.MC.Sec7.S7PIF4.s7_PIF_coord_ito_proof R m hm T hT N hN P X₀ W X hreal hF t φ ht hφ i
  have hEucl : ∀ i, ∀ᵐ ω ∂P, ∀ u, localItoIntegralE P ℱ W' (S7PIF5_Phi R X t φ) u ω i =
      localItoIntegral P ℱ W' (fun s ω k => S7PIF5_Phi R X t φ s ω k i) u ω := fun i =>
    localItoIntegralE_euclidean hW _ hΦ i
  have hsmul : ∀ i, ∀ᵐ ω ∂P, ∀ u, localItoIntegral P ℱ W' (fun s ω k => S7PIF5_Phi R X t φ s ω k i) u ω =
      Real.sqrt N * empiricalMartingale P ℱ W' R.D (t i) (fun r => propagator R.D R.ρ r (t i) (φ i)) X u ω := by
    intro i
    have h1 := localItoIntegral_smul hW (hL i).locL2 (Real.sqrt N)
    have h2 := localItoIntegral_eq_itoIntegral hW (hL i)
    filter_upwards [h1, h2] with ω h1 h2 u
    have e : (fun s ω k => S7PIF5_Phi R X t φ s ω k i) = fun s ω =>
        Real.sqrt N • empiricalNoiseIntegrand R.D (t i) (fun r => propagator R.D R.ρ r (t i) (φ i)) X s ω := by
      funext s ω k; rfl
    rw [e, h1 u, h2 u]
    rfl
  filter_upwards [ae_all_iff.2 hcoord, ae_all_iff.2 hEucl, ae_all_iff.2 hsmul, hbint] with ω h1 h2 h3 h4 u hu
  ext i
  have hbu : IntegrableOn (fun s => S7PIF5_b R m P X t φ s ω) (Set.Icc 0 u) :=
    h4.mono_set (Set.Icc_subset_Icc le_rfl hu.2)
  have hcomp : (∫ s in Set.Icc 0 u, S7PIF5_b R m P X t φ s ω) i = ∫ s in Set.Icc 0 u, S7PIF5_b R m P X t φ s ω i := by
    have := ContinuousLinearMap.integral_comp_comm (EuclideanSpace.proj i : EuclideanSpace ℝ (Fin q) →L[ℝ] ℝ) hbu
    simpa using this.symm
  have hbi : ∫ s in Set.Icc 0 u, S7PIF5_b R m P X t φ s ω i =
      -(Real.sqrt N)⁻¹ * ∫ r in Set.Ioc 0 u, NegSobolev.eval
        (quadFieldAt m R.D.s (fun s => withDensityReal (R.ρ s)) P X r ω) (obsTest R.D R.ρ t φ i r) := by
    rw [integral_Icc_eq_integral_Ioc, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    show (if 0 ≤ r then -(Real.sqrt N)⁻¹ * NegSobolev.eval
      (quadFieldAt m R.D.s (fun s => withDensityReal (R.ρ s)) P X r ω) (obsTest R.D R.ρ t φ i r) else 0) = _
    rw [if_pos hr.1.le]
  unfold itoProcess
  show obsVec m T t φ (predicted R.D R.ρ (zetaWin m T 0 P X ω) u) i =
    obsVec m T t φ (initProp R.D R.ρ m T (zetaAt m P X 0 ω)) i +
      (∫ s in Set.Icc 0 u, S7PIF5_b R m P X t φ s ω) i +
      localItoIntegralE P ℱ W' (S7PIF5_Phi R X t φ) u ω i
  rw [h1 i u hu, hcomp, hbi, h2 i u, h3 i u,
    S7PIF5_init_coord R m hm T hT N hN P X₀ W X hreal t φ ht hφ i ω]
  ring

theorem s7_PIF_itoprocess_proof {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hF : IsFilteredSolution P ℱ W' W X) {q : ℕ} (t : Fin q → ℝ) (φ : Fin q → Torus d → ℝ)
    (ht : ∀ i, t i ∈ Set.Icc (0 : ℝ) T) (hφ : ∀ i, Torus.IsSmooth (φ i)) :
    ∃ (b : ℝ → Ω → EuclideanSpace ℝ (Fin q))
      (Φc : ℝ → Ω → (Fin N × Fin d) → EuclideanSpace ℝ (Fin q)),
      IsProgressiveLocL1 P ℱ b ∧ IsProgressiveLocL2E P ℱ Φc ∧
      (∀ s, Measurable[ℱ s] (fun ω => obsVec m T t φ (initProp R.D R.ρ m T (zetaAt m P X 0 ω)))) ∧
      (∀ r ω i, b r ω i = if 0 ≤ r then -(Real.sqrt N)⁻¹ * NegSobolev.eval
          (quadFieldAt m R.D.s (fun s => withDensityReal (R.ρ s)) P X r ω) (obsTest R.D R.ρ t φ i r) else 0) ∧
      (∀ s ω k i, Φc s ω k i = Real.sqrt N *
          empiricalNoiseIntegrand R.D (t i) (fun r => propagator R.D R.ρ r (t i) (φ i)) X s ω k) ∧
      ∀ᵐ ω ∂P, ∀ u ∈ Set.Icc (0 : ℝ) T,
        obsVec m T t φ (predicted R.D R.ρ (zetaWin m T 0 P X ω) u) =
          itoProcess P ℱ W' (fun ω => obsVec m T t φ (initProp R.D R.ρ m T (zetaAt m P X 0 ω))) b Φc u ω := by
  refine ⟨S7PIF5_b R m P X t φ, S7PIF5_Phi R X t φ,
    ⟨S7PIF5_b_prog R m hm T hT N hN P X₀ W X hreal hF.progressive t φ ht hφ,
      fun T' => S7PIF5_b_int R m hm T hT N hN P X₀ W X hreal hF.progressive t φ ht hφ T'⟩,
    S7PIF5_Phi_L2E R m hm T hT N hN P X₀ W X hreal hF t φ ht hφ,
    S7PIF5_init_meas R m hm T hT N hN P X₀ W X hreal hF t φ ht hφ,
    fun r ω i => rfl, fun s ω k i => rfl,
    S7PIF5_identity R m hm T hT N hN P X₀ W X hreal hF t φ ht hφ⟩

end Prob

end HRS.MC.Sec7.S7PIF5

end
